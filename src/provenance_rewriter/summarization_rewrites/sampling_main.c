/*-----------------------------------------------------------------------------
 *
 * sampling_main.c
 *
 *
 *		AUTHOR: seokki
 *
 *
 *
 *-----------------------------------------------------------------------------
 */

#include "common.h"
#include "log/logger.h"
#include "mem_manager/mem_mgr.h"
#include "configuration/option.h"
#include "instrumentation/timing_instrumentation.h"

#include "metadata_lookup/metadata_lookup.h"
#include "model/node/nodetype.h"
#include "utility/string_utils.h"
#include "model/datalog/datalog_model.h"
#include "model/expression/expression.h"
#include "sql_serializer/sql_serializer.h"
#include "provenance_rewriter/prov_utility.h"
#include "provenance_rewriter/prov_rewriter.h"
#include "model/query_operator/query_operator.h"
#include "operator_optimizer/operator_optimizer.h"
#include "model/query_operator/operator_property.h"
#include "model/query_operator/query_operator_dt_inference.h"
#include "model/query_operator/query_operator_model_checker.h"
#include "provenance_rewriter/summarization_rewrites/sampling_main.h"

#define RESULT_WO_ATTR "numOfdistOnoc"

static Node *rewritePartition (Node *rewrittenTree, int sampleSize);
static Node *buildPartTa_Fta (QueryOperator *op, int nLeft, int leftZPos);
static Node *buildPartTb_Ftb (QueryOperator *op, int nLeft, int rightZPos);
static Node *buildProvenance (Node *ftaNode, Node *ftbNode, int leftZPos, int rightZPos, int sampleSize);
static List *children_Of_Join (QueryOperator *op, List *collectChildOps);


Node *
rewriteSampleOutput (Node *rewrittenTree, HashMap *summOpts, ProvQuestion qType)
{
	Node *rewrittenTreePart = NULL;
	Node *result = NULL;
	int sampleSize = 0;

	if (summOpts != NULL)
	{
		INFO_LOG(" * do sampling rewrite");
		FOREACH_HASH_ENTRY(n,summOpts)
		{
			KeyValue *kv = (KeyValue *) n;
			char *key = STRING_VALUE(kv->key);

			// WITH SAMPLE(p) is parsed as a flat "sumsamp" property (see
			// dl_parser.y's optionalSumSample and analyze_dl.c's
			// analyzeSummerizationBasics, which copies each sumOpts entry
			// straight onto the DLProgram's properties) -- it is never
			// nested under SAMPLE_PROPS for a plain sampling query, so that
			// case must be checked at this top level too.
			if(streq(key,PROP_SUMMARIZATION_SAMPLE))
				sampleSize = INT_VALUE(kv->value);

			if(streq(key,PROP_SUMMARIZATION_SAMPLE_PROPS))
			{
				List *explSamp = (List *) n->value;

				FOREACH(KeyValue,kv,explSamp)
				{
					char *key = STRING_VALUE(kv->key);

					if(streq(key,PROP_SUMMARIZATION_SAMPLE))
						sampleSize = INT_VALUE(kv->value);
				}
			}
		}
	}

	DEBUG_LOG("sampling options are: qType: %s, sample size: %d",
			  ProvQuestionToString(qType), sampleSize);

	Node *rewrittenHead = (Node *) getHeadOfListP((List *) rewrittenTree);
	INFO_OP_LOG("input rewritten trees:", rewrittenTree);

	rewrittenTreePart = rewritePartition(rewrittenHead, sampleSize);
	result = (Node *) rewrittenTreePart;

	return result;
}


/*
 * Walk a join condition tree and return the attrPosition of the AttributeReference
 * that belongs to the given fromClauseItem (0=left child, 1=right child) inside
 * the first "=" operator found.  Returns INVALID_ATTR if none is found.
 */
static int
findEqAttrPos (Node *cond, int fromClauseItem)
{
	if (cond == NULL || !isA(cond, Operator))
		return INVALID_ATTR;

	Operator *oper = (Operator *) cond;
	if (streq(oper->name, "="))
	{
		FOREACH(Node, arg, oper->args)
		{
			if (isA(arg, AttributeReference))
			{
				AttributeReference *ref = (AttributeReference *) arg;
				if (ref->fromClauseItem == fromClauseItem)
					return ref->attrPosition;
			}
		}
	}
	else
	{
		FOREACH(Node, arg, oper->args)
		{
			int pos = findEqAttrPos(arg, fromClauseItem);
			if (pos != INVALID_ATTR)
				return pos;
		}
	}
	return INVALID_ATTR;
}


static Node *rewritePartition (Node *rewrittenTree, int sampleSize)
{
	QueryOperator *in = (QueryOperator *) rewrittenTree;
	INFO_OP_LOG("head of input rewritten trees:", in);

	// Standard shape: DuplicateRemoval -> Projection -> Selection -> Join
	QueryOperator *po     = OP_LCHILD(in);   // Projection (top-level answer attrs)
	QueryOperator *op     = OP_LCHILD(po);   // Selection  (comparison condition)
	QueryOperator *joinOp = OP_LCHILD(op);   // Join

	// Collect left and right subtrees of the join for later reuse
	List *collectChildOps = NIL;
	collectChildOps = children_Of_Join(joinOp, collectChildOps);
	INFO_OP_LOG("collected input operators:", (Node *) collectChildOps);

	// Left subtree is the first entry; use its schema to know how many
	// attributes come from the left side in the join output.
	QueryOperator *leftChild = (QueryOperator *) getHeadOfListP(collectChildOps);
	int nLeft = LIST_LENGTH(leftChild->schema->attrDefs);

	// Derive join-equality attribute positions for both sides.
	int leftZPos  = findEqAttrPos(((JoinOperator *) joinOp)->cond, 0);
	int rightZPos = findEqAttrPos(((JoinOperator *) joinOp)->cond, 1);

	Node *fta = buildPartTa_Fta(op, nLeft, leftZPos);
	Node *ftb = buildPartTb_Ftb(op, nLeft, rightZPos);

	return buildProvenance(fta, ftb, leftZPos, rightZPos, sampleSize);
}


/* -------------------------------------------------------------------------
 * partTa + Fta
 * ------------------------------------------------------------------------- */

static Node *
buildPartTa_Fta (QueryOperator *op, int nLeft, int leftZPos)
{
	// --- Build partTa ---
	// Project only the left-side attributes (positions 0..nLeft-1) from the
	// join output, then wrap with DISTINCT.

	List *projExprs = NIL;
	List *attrNames = NIL;
	int i = 0;
	FOREACH(AttributeDef, ad, op->schema->attrDefs)
	{
		if (i < nLeft)
		{
			projExprs = appendToTailOfList(projExprs,
				createFullAttrReference(strdup(ad->attrName), 0, i,
										INVALID_ATTR, ad->dataType));
			attrNames = appendToTailOfList(attrNames, strdup(ad->attrName));
		}
		i++;
	}

	ProjectionOperator *partTaProj = createProjectionOp(
		projExprs, op, NIL, attrNames);
	op->parents = singleton((QueryOperator *) partTaProj);

	List *dupAttrExprs = NIL;
	i = 0;
	FOREACH(AttributeDef, ad, ((QueryOperator *) partTaProj)->schema->attrDefs)
	{
		dupAttrExprs = appendToTailOfList(dupAttrExprs,
			createFullAttrReference(strdup(ad->attrName), 0, i,
									INVALID_ATTR, ad->dataType));
		i++;
	}

	DuplicateRemoval *partTa = createDuplicateRemovalOp(
		dupAttrExprs, (QueryOperator *) partTaProj, NIL, attrNames);
	((QueryOperator *) partTaProj)->parents = singleton((QueryOperator *) partTa);

	// CTE for partTa to be referenced by Fta
	SET_BOOL_STRING_PROP((Node *) partTa, PROP_MATERIALIZE);
	INFO_OP_LOG("partTa operator tree:", (Node *) partTa);

	// Default: use the join-based partTa; uncomment USE_EXISTS_PART_TA to switch
	// #define USE_EXISTS_PART_TA
	QueryOperator *partTaOp = (QueryOperator *) partTa;
// #ifdef USE_EXISTS_PART_TA
// 	{
// 		QueryOperator *rightHop  = (QueryOperator *) getNthOfListP(collectChildOps, 1);
// 		QueryOperator *outerHop  = (QueryOperator *) copyObject(leftChild);
// 		QueryOperator *innerHop  = (QueryOperator *) copyObject(rightHop);
// 		outerHop->parents = NIL;
// 		innerHop->parents = NIL;

// 		// f.x = t.z  (inner source = outer connecting node, correlated)
// 		AttributeDef *outerZ_def = getAttrDefByPos(outerHop, 1);
// 		AttributeDef *outerC_def = getAttrDefByPos(outerHop, 2);
// 		AttributeDef *innerX_def = getAttrDefByPos(innerHop, 0);
// 		AttributeDef *innerC_def = getAttrDefByPos(innerHop, 2);
// 		Node *ec1 = (Node *) createOpExpr("=", LIST_MAKE(
// 			createFullAttrReference(strdup(innerX_def->attrName), 0, 0, 0, innerX_def->dataType),
// 			createFullAttrReference(strdup(outerZ_def->attrName), 0, 1, 1, outerZ_def->dataType)));
// 		// f.c > t.c  (inner cost > outer cost, correlated)
// 		Node *ec2 = (Node *) createOpExpr(">", LIST_MAKE(
// 			createFullAttrReference(strdup(innerC_def->attrName), 0, 2, 0, innerC_def->dataType),
// 			createFullAttrReference(strdup(outerC_def->attrName), 0, 2, 1, outerC_def->dataType)));
// 		SelectionOperator *innerSel = createSelectionOp(AND_EXPRS(ec1, ec2), innerHop, NIL,
// 														getAttrNames(innerHop->schema));
// 		innerHop->parents = singleton((QueryOperator *) innerSel);

// 		// NestingOperator(EXISTS): schema = outer attrs + nesting_eval_0 BOOL
// 		List *nestAttrNames = getAttrNames(outerHop->schema);
// 		List *nestDts       = getDataTypes(outerHop->schema);
// 		nestAttrNames = appendToTailOfList(nestAttrNames, strdup("nesting_eval_0"));
// 		nestDts       = appendToTailOfListInt(nestDts, DT_BOOL);
// 		NestingOperator *nestOp = createNestingOp(NESTQ_EXISTS, NULL,
// 												  LIST_MAKE(outerHop, (QueryOperator *) innerSel),
// 												  NIL, nestAttrNames, nestDts);
// 		outerHop->parents = singleton((QueryOperator *) nestOp);
// 		((QueryOperator *) innerSel)->parents = singleton((QueryOperator *) nestOp);

// 		// Selection: WHERE nesting_eval_0 = TRUE
// 		int nestEvalPos = LIST_LENGTH(outerHop->schema->attrDefs);
// 		Node *existsCond = (Node *) createOpExpr("=", LIST_MAKE(
// 			createFullAttrReference(strdup("nesting_eval_0"), 0, nestEvalPos, 0, DT_BOOL),
// 			(Node *) createConstBool(TRUE)));
// 		SelectionOperator *existsSel = createSelectionOp(existsCond, (QueryOperator *) nestOp,
// 														 NIL, getAttrNames(((QueryOperator *) nestOp)->schema));
// 		((QueryOperator *) nestOp)->parents = singleton((QueryOperator *) existsSel);

// 		// Projection: keep only outer attrs, drop nesting_eval_0
// 		List *existsProjExprs  = NIL;
// 		List *existsAttrNames  = NIL;
// 		int j = 0;
// 		FOREACH(AttributeDef, ad, outerHop->schema->attrDefs)
// 		{
// 			existsProjExprs = appendToTailOfList(existsProjExprs,
// 				createFullAttrReference(strdup(ad->attrName), 0, j, INVALID_ATTR, ad->dataType));
// 			existsAttrNames = appendToTailOfList(existsAttrNames, strdup(ad->attrName));
// 			j++;
// 		}
// 		ProjectionOperator *existsProj = createProjectionOp(existsProjExprs,
// 															(QueryOperator *) existsSel,
// 															NIL, existsAttrNames);
// 		((QueryOperator *) existsSel)->parents = singleton((QueryOperator *) existsProj);

// 		// DISTINCT
// 		List *existsDupExprs = NIL;
// 		j = 0;
// 		FOREACH(AttributeDef, ad, ((QueryOperator *) existsProj)->schema->attrDefs)
// 		{
// 			existsDupExprs = appendToTailOfList(existsDupExprs,
// 				createFullAttrReference(strdup(ad->attrName), 0, j, INVALID_ATTR, ad->dataType));
// 			j++;
// 		}
// 		DuplicateRemoval *partTa_exists = createDuplicateRemovalOp(existsDupExprs,
// 																   (QueryOperator *) existsProj,
// 																   NIL, existsAttrNames);
// 		((QueryOperator *) existsProj)->parents = singleton((QueryOperator *) partTa_exists);
// 		SET_BOOL_STRING_PROP((Node *) partTa_exists, PROP_MATERIALIZE);
// 		INFO_OP_LOG("partTa_exists operator tree:", (Node *) partTa_exists);

// 		partTaOp = (QueryOperator *) partTa_exists;
// 	}
// 	return (Node *) partTaOp;
// #endif

	// --- Build Fta ---
	// SELECT *, count(za) OVER (PARTITION BY all-except-cost) AS numofza
	// FROM partTa

	DEBUG_LOG("leftZPos = %d", leftZPos);
	AttributeDef *zaDef = getAttrDefByPos(partTaOp, leftZPos);
	AttributeReference *zaRef = createFullAttrReference(
		strdup(zaDef->attrName), 0, leftZPos, INVALID_ATTR, zaDef->dataType);
	Node *cntFunc = (Node *) createFunctionCall(strdup("count"), singleton(zaRef));

	// PARTITION BY all attrs of partTa except the last (cost)
	int nPartTa = LIST_LENGTH(partTaOp->schema->attrDefs);
	List *partitionBy = NIL;
	i = 0;
	FOREACH(AttributeDef, ad, partTaOp->schema->attrDefs)
	{
		if (i < nPartTa - 1)
			partitionBy = appendToTailOfList(partitionBy,
				createFullAttrReference(strdup(ad->attrName), 0, i, INVALID_ATTR, ad->dataType));
		i++;
	}

	WindowOperator *fta = createWindowOp(
		cntFunc,
		partitionBy,
		NIL,   // no ORDER BY
		NULL,  // no frame
		strdup("numofza"),
		partTaOp,
		NIL
	);
	addParent(partTaOp, (QueryOperator *) fta);

	INFO_OP_LOG("Fta operator tree:", (Node *) fta);

	return (Node *) fta;
}


/* -------------------------------------------------------------------------
 * partTb + Ftb
 * ------------------------------------------------------------------------- */

static Node *
buildPartTb_Ftb (QueryOperator *op, int nLeft, int rightZPos)
{
	// Copy op (Selection → Join subtree) so partTb has an independent subtree.
	// Sharing op with partTa causes the SQL serializer to see op as a shared node
	// and pull partTa's CTE into the ftb output.
	QueryOperator *opCopy = (QueryOperator *) copyObject(op);
	opCopy->parents = NIL;

	// --- Build partTb ---
	// Project only the right-side attributes (positions nLeft..total-1) from the
	// join output, then wrap with DISTINCT.

	List *projExprsB = NIL;
	List *attrNamesB = NIL;
	int i = 0;
	FOREACH(AttributeDef, ad, opCopy->schema->attrDefs)
	{
		if (i >= nLeft)
		{
			projExprsB = appendToTailOfList(projExprsB,
				createFullAttrReference(strdup(ad->attrName), 0, i,
										INVALID_ATTR, ad->dataType));
			attrNamesB = appendToTailOfList(attrNamesB, strdup(ad->attrName));
		}
		i++;
	}

	ProjectionOperator *partTbProj = createProjectionOp(
		projExprsB, opCopy, NIL, attrNamesB);
	opCopy->parents = singleton((QueryOperator *) partTbProj);

	List *dupAttrExprsB = NIL;
	i = 0;
	FOREACH(AttributeDef, ad, ((QueryOperator *) partTbProj)->schema->attrDefs)
	{
		dupAttrExprsB = appendToTailOfList(dupAttrExprsB,
			createFullAttrReference(strdup(ad->attrName), 0, i,
									INVALID_ATTR, ad->dataType));
		i++;
	}

	DuplicateRemoval *partTb = createDuplicateRemovalOp(
		dupAttrExprsB, (QueryOperator *) partTbProj, NIL, attrNamesB);
	((QueryOperator *) partTbProj)->parents = singleton((QueryOperator *) partTb);
	SET_BOOL_STRING_PROP((Node *) partTb, PROP_MATERIALIZE);
	INFO_OP_LOG("partTb operator tree:", (Node *) partTb);

	// --- Build Ftb ---
	// SELECT *, count(zb) OVER (PARTITION BY all-except-cost) AS numofzb
	// FROM partTb

	QueryOperator *partTbOp = (QueryOperator *) partTb;

	DEBUG_LOG("rightZPos = %d", rightZPos);
	AttributeDef *zbDef = getAttrDefByPos(partTbOp, rightZPos);
	AttributeReference *zbRef = createFullAttrReference(
		strdup(zbDef->attrName), 0, rightZPos, INVALID_ATTR, zbDef->dataType);
	Node *cntFuncB = (Node *) createFunctionCall(strdup("count"), singleton(zbRef));

	// PARTITION BY all attrs of partTb except the last (cost)
	int nPartTb = LIST_LENGTH(partTbOp->schema->attrDefs);
	List *partitionByB = NIL;
	int posB = 0;
	FOREACH(AttributeDef, ad, partTbOp->schema->attrDefs)
	{
		if (posB < nPartTb - 1)
			partitionByB = appendToTailOfList(partitionByB,
				createFullAttrReference(strdup(ad->attrName), 0, posB, INVALID_ATTR, ad->dataType));
		posB++;
	}

	WindowOperator *ftb = createWindowOp(
		cntFuncB,
		partitionByB,
		NIL,
		NULL,
		strdup("numofzb"),
		partTbOp,
		NIL
	);
	addParent(partTbOp, (QueryOperator *) ftb);

	INFO_OP_LOG("Ftb operator tree:", (Node *) ftb);

	return (Node *) ftb;
}


/* -------------------------------------------------------------------------
 * Joinsize + temp1 + Stp + Tp + Ssp + Ssd + Wt
 * -------------------------------------------------------------------------
 * Joinsize: DISTINCT zb, y, cb, numofzb, (numofza * numofzb) AS joinsize
 *           FROM Fta JOIN Ftb ON Fta.za = Ftb.zb   -- materialized
 * temp1:    SELECT *, joinsize / numofzb AS temp1   FROM Joinsize
 * Stp:      SELECT *, SUM(temp1) OVER (PARTITION BY y) AS stp   FROM temp1
 * Tp:       SELECT *, SUM(temp1) OVER() AS totalprov   FROM Stp
 * Ssp:      SELECT *, (stp / totalprov) * 3.0 AS ssp   FROM Tp
 * Ssd:      SELECT *, (joinsize * ssp) / stp AS ssd   FROM Ssp
 * Wt:       SELECT *, ssd / joinsize AS weight   FROM Ssd  (returned directly)
 * ------------------------------------------------------------------------- */

static Node *
buildProvenance (Node *ftaNode, Node *ftbNode, int leftZPos, int rightZPos, int sampleSize)
{
	QueryOperator *fta = (QueryOperator *) ftaNode;
	QueryOperator *ftb = (QueryOperator *) ftbNode;
	int nFta = LIST_LENGTH(fta->schema->attrDefs);
	int nFtb = LIST_LENGTH(ftb->schema->attrDefs);

	// --- Build Joinsize ---
	// Join condition: Fta.za (leftZPos, fromClauseItem=0) = Ftb.zb (rightZPos, fromClauseItem=1)
	AttributeDef *zaJoinDef = getAttrDefByPos(fta, leftZPos);
	AttributeDef *zbJoinDef = getAttrDefByPos(ftb, rightZPos);
	Node *joinCond = (Node *) createOpExpr("=", LIST_MAKE(
		createFullAttrReference(strdup(zaJoinDef->attrName), 0, leftZPos,  INVALID_ATTR, zaJoinDef->dataType),
		createFullAttrReference(strdup(zbJoinDef->attrName), 1, rightZPos, INVALID_ATTR, zbJoinDef->dataType)));

	// Combined schema: Fta attrs then Ftb attrs
	List *joinAttrNames = NIL;
	FOREACH(AttributeDef, ad, fta->schema->attrDefs)
		joinAttrNames = appendToTailOfList(joinAttrNames, strdup(ad->attrName));
	FOREACH(AttributeDef, ad, ftb->schema->attrDefs)
		joinAttrNames = appendToTailOfList(joinAttrNames, strdup(ad->attrName));

	JoinOperator *jsJoin = createJoinOp(JOIN_INNER, joinCond,
		LIST_MAKE(fta, ftb), NIL, joinAttrNames);
	addParent(fta, (QueryOperator *) jsJoin);
	addParent(ftb, (QueryOperator *) jsJoin);

	// Projection: all Ftb attrs (zb, y, cb, numofzb) + numofza * numofzb AS joinsize
	// numofza = last Fta attr in join output (pos nFta-1)
	// numofzb = last Ftb attr in join output (pos nFta+nFtb-1)
	int numofzaPosInJoin = nFta - 1;
	int numofzbPosInJoin = nFta + nFtb - 1;

	List *jsProjExprs = NIL;
	List *jsAttrNames = NIL;
	int idx = 0;
	FOREACH(AttributeDef, ad, ((QueryOperator *) jsJoin)->schema->attrDefs)
	{
		if (idx >= nFta)  // skip Fta attrs; keep Ftb: zb, y, cb, numofzb
		{
			jsProjExprs = appendToTailOfList(jsProjExprs,
				createFullAttrReference(strdup(ad->attrName), 0, idx, INVALID_ATTR, ad->dataType));
			jsAttrNames = appendToTailOfList(jsAttrNames, strdup(ad->attrName));
		}
		idx++;
	}

	// numofza * numofzb AS joinsize
	AttributeDef *numofzaDef = getAttrDefByPos((QueryOperator *) jsJoin, numofzaPosInJoin);
	AttributeDef *numofzbDef = getAttrDefByPos((QueryOperator *) jsJoin, numofzbPosInJoin);
	Node *joinsizeExpr = (Node *) createOpExpr("*", LIST_MAKE(
		createFullAttrReference(strdup(numofzaDef->attrName), 0, numofzaPosInJoin, INVALID_ATTR, numofzaDef->dataType),
		createFullAttrReference(strdup(numofzbDef->attrName), 0, numofzbPosInJoin, INVALID_ATTR, numofzbDef->dataType)));
	jsProjExprs = appendToTailOfList(jsProjExprs, joinsizeExpr);
	jsAttrNames = appendToTailOfList(jsAttrNames, strdup("joinsize"));

	ProjectionOperator *jsProjOp = createProjectionOp(
		jsProjExprs, (QueryOperator *) jsJoin, NIL, jsAttrNames);
	((QueryOperator *) jsJoin)->parents = singleton((QueryOperator *) jsProjOp);

	// DISTINCT → materialize
	List *jsDupExprs = NIL;
	idx = 0;
	FOREACH(AttributeDef, ad, ((QueryOperator *) jsProjOp)->schema->attrDefs)
	{
		jsDupExprs = appendToTailOfList(jsDupExprs,
			createFullAttrReference(strdup(ad->attrName), 0, idx, INVALID_ATTR, ad->dataType));
		idx++;
	}
	DuplicateRemoval *joinsize = createDuplicateRemovalOp(
		jsDupExprs, (QueryOperator *) jsProjOp, NIL, jsAttrNames);
	((QueryOperator *) jsProjOp)->parents = singleton((QueryOperator *) joinsize);
	SET_BOOL_STRING_PROP((Node *) joinsize, PROP_MATERIALIZE);
	INFO_OP_LOG("Joinsize operator tree:", (Node *) joinsize);

	// --- Build temp1 ---
	// SELECT *, joinsize / numofzb AS temp1  FROM Joinsize
	// Joinsize schema: [zb(0), y(1), cb(2), numofzb(nFtb-1), joinsize(nFtb)]
	QueryOperator *joinsizeOp = (QueryOperator *) joinsize;
	int numofzbInJs  = nFtb - 1;  // numofzb position in Joinsize
	int joinsizeInJs = nFtb;      // joinsize position in Joinsize

	List *t1ProjExprs = NIL;
	List *t1AttrNames = NIL;
	idx = 0;
	FOREACH(AttributeDef, ad, joinsizeOp->schema->attrDefs)
	{
		t1ProjExprs = appendToTailOfList(t1ProjExprs,
			createFullAttrReference(strdup(ad->attrName), 0, idx, INVALID_ATTR, ad->dataType));
		t1AttrNames = appendToTailOfList(t1AttrNames, strdup(ad->attrName));
		idx++;
	}

	// joinsize / numofzb AS temp1
	AttributeDef *numofzbInJsDef  = getAttrDefByPos(joinsizeOp, numofzbInJs);
	AttributeDef *joinsizeInJsDef = getAttrDefByPos(joinsizeOp, joinsizeInJs);
	Node *temp1Expr = (Node *) createOpExpr("/", LIST_MAKE(
		createFullAttrReference(strdup(joinsizeInJsDef->attrName), 0, joinsizeInJs, INVALID_ATTR, joinsizeInJsDef->dataType),
		createFullAttrReference(strdup(numofzbInJsDef->attrName),  0, numofzbInJs,  INVALID_ATTR, numofzbInJsDef->dataType)));
	t1ProjExprs = appendToTailOfList(t1ProjExprs, temp1Expr);
	t1AttrNames = appendToTailOfList(t1AttrNames, strdup("temp1"));
	// currently bigint / bigint --> integer division truncates

	ProjectionOperator *temp1 = createProjectionOp(t1ProjExprs, joinsizeOp, NIL, t1AttrNames);
	joinsizeOp->parents = singleton((QueryOperator *) temp1);
	INFO_OP_LOG("temp1 operator tree:", (Node *) temp1);

	// --- Build Stp ---
	// SELECT *, SUM(temp1) OVER (PARTITION BY y) AS stp FROM temp1
	// temp1 schema: [zb(0), y(rightZPos+1), cb, numofzb, joinsize, temp1]
	QueryOperator *temp1Op = (QueryOperator *) temp1;
	int nTemp1 = LIST_LENGTH(temp1Op->schema->attrDefs);
	int temp1ColPos = nTemp1 - 1;   // temp1 column is the last attr
	int yPos = rightZPos + 1;       // y is right after zb in the Ftb portion

	AttributeDef *temp1ColDef = getAttrDefByPos(temp1Op, temp1ColPos);
	Node *sumTemp1 = (Node *) createFunctionCall(strdup("sum"),
		singleton(createFullAttrReference(strdup(temp1ColDef->attrName), 0,
			temp1ColPos, INVALID_ATTR, temp1ColDef->dataType)));

	AttributeDef *yDef = getAttrDefByPos(temp1Op, yPos);
	List *stpPartBy = singleton(
		createFullAttrReference(strdup(yDef->attrName), 0, yPos, INVALID_ATTR, yDef->dataType));

	WindowOperator *stp = createWindowOp(
		sumTemp1,
		stpPartBy,
		NIL,   // no ORDER BY
		NULL,  // no frame
		strdup("stp"),
		temp1Op,
		NIL
	);
	addParent(temp1Op, (QueryOperator *) stp);
	INFO_OP_LOG("Stp operator tree:", (Node *) stp);

	// --- Build Tp ---
	// SELECT *, SUM(temp1) OVER() AS totalprov FROM Stp
	// temp1 column is still at position temp1ColPos in Stp's schema
	QueryOperator *stpOp = (QueryOperator *) stp;

	AttributeDef *temp1InStpDef = getAttrDefByPos(stpOp, temp1ColPos);
	Node *sumTemp1ForTp = (Node *) createFunctionCall(strdup("sum"),
		singleton(createFullAttrReference(strdup(temp1InStpDef->attrName), 0,
			temp1ColPos, INVALID_ATTR, temp1InStpDef->dataType)));

	WindowOperator *tp = createWindowOp(
		sumTemp1ForTp,
		NIL,   // no PARTITION BY (OVER() = entire table)
		NIL,   // no ORDER BY
		NULL,  // no frame
		strdup("totalprov"),
		stpOp,
		NIL
	);
	addParent(stpOp, (QueryOperator *) tp);
	INFO_OP_LOG("Tp operator tree:", (Node *) tp);

	// --- Build Ssp ---
	// SELECT *, (stp / totalprov) * 3.0 AS ssp FROM Tp
	// Tp schema: [..., temp1(temp1ColPos), stp(temp1ColPos+1), totalprov(nTp-1)]
	QueryOperator *tpOp = (QueryOperator *) tp;
	int nTp              = LIST_LENGTH(tpOp->schema->attrDefs);
	int stpPosInTp       = temp1ColPos + 1;  // stp appended after temp1 by Stp
	int totalprovPos     = nTp - 1;          // totalprov is the last attr of Tp

	List *sspProjExprs = NIL;
	List *sspAttrNames = NIL;
	idx = 0;
	FOREACH(AttributeDef, ad, tpOp->schema->attrDefs)
	{
		sspProjExprs = appendToTailOfList(sspProjExprs,
			createFullAttrReference(strdup(ad->attrName), 0, idx, INVALID_ATTR, ad->dataType));
		sspAttrNames = appendToTailOfList(sspAttrNames, strdup(ad->attrName));
		idx++;
	}

	AttributeDef *stpDef       = getAttrDefByPos(tpOp, stpPosInTp);
	AttributeDef *totalprovDef = getAttrDefByPos(tpOp, totalprovPos);
	// (stp / totalprov) * sampleSize
	Node *sspExpr = (Node *) createOpExpr("*", LIST_MAKE(
		createOpExpr("/", LIST_MAKE(
			createFullAttrReference(strdup(stpDef->attrName),       0, stpPosInTp,  INVALID_ATTR, stpDef->dataType),
			createFullAttrReference(strdup(totalprovDef->attrName), 0, totalprovPos, INVALID_ATTR, totalprovDef->dataType))),
		(Node *) createConstFloat((double) sampleSize)));
	sspProjExprs = appendToTailOfList(sspProjExprs, sspExpr);
	sspAttrNames = appendToTailOfList(sspAttrNames, strdup("ssp"));

	ProjectionOperator *ssp = createProjectionOp(sspProjExprs, tpOp, NIL, sspAttrNames);
	tpOp->parents = singleton((QueryOperator *) ssp);
	INFO_OP_LOG("Ssp operator tree:", (Node *) ssp);

	// --- Build Ssd ---
	// SELECT *, (joinsize * ssp) / stp AS ssd FROM Ssp
	// Ssp schema = Tp schema + ssp; ssp is at pos nTp
	QueryOperator *sspOp  = (QueryOperator *) ssp;
	int sspColPos         = nTp;   // ssp appended as last column

	AttributeDef *joinsizeInSspDef = getAttrDefByPos(sspOp, nFtb);        // joinsize preserved at nFtb
	AttributeDef *sspColDef        = getAttrDefByPos(sspOp, sspColPos);
	AttributeDef *stpInSspDef      = getAttrDefByPos(sspOp, stpPosInTp);  // stp position unchanged

	List *ssdProjExprs = NIL;
	List *ssdAttrNames = NIL;
	idx = 0;
	FOREACH(AttributeDef, ad, sspOp->schema->attrDefs)
	{
		ssdProjExprs = appendToTailOfList(ssdProjExprs,
			createFullAttrReference(strdup(ad->attrName), 0, idx, INVALID_ATTR, ad->dataType));
		ssdAttrNames = appendToTailOfList(ssdAttrNames, strdup(ad->attrName));
		idx++;
	}

	// joinsize is DT_LONG while ssp/stp are DT_FLOAT; the type inference only
	// derives a numeric result type when both operands of an arithmetic op
	// match exactly, so cast joinsize to DT_FLOAT to keep ssd typed as float.
	// Must be a real CastExpr (not just a relabeled AttributeReference):
	// introduceCastsWhereNecessary() (query_operator_dt_inference.c) walks the
	// tree afterwards and resets any AttributeReference's recorded type back
	// to its true source type, which would silently undo a relabel-only
	// "fix" and reintroduce the DT_STRING fallback. CastExpr nodes are left
	// untouched by that pass, so this is the only fix that survives it.
	Node *joinsizeAsFloatForSsd = (Node *) createCastExpr(
		(Node *) createFullAttrReference(strdup(joinsizeInSspDef->attrName), 0, nFtb, INVALID_ATTR, joinsizeInSspDef->dataType),
		DT_FLOAT);
	Node *ssdExpr = (Node *) createOpExpr("/", LIST_MAKE(
		createOpExpr("*", LIST_MAKE(
			joinsizeAsFloatForSsd,
			createFullAttrReference(strdup(sspColDef->attrName),        0, sspColPos,  INVALID_ATTR, sspColDef->dataType))),
		createFullAttrReference(strdup(stpInSspDef->attrName),          0, stpPosInTp, INVALID_ATTR, stpInSspDef->dataType)));
	ssdProjExprs = appendToTailOfList(ssdProjExprs, ssdExpr);
	ssdAttrNames = appendToTailOfList(ssdAttrNames, strdup("ssd"));

	ProjectionOperator *ssd = createProjectionOp(ssdProjExprs, sspOp, NIL, ssdAttrNames);
	sspOp->parents = singleton((QueryOperator *) ssd);
	INFO_OP_LOG("Ssd operator tree:", (Node *) ssd);

	// return (Node *) ssd;

	// --- Build Wt ---
	// SELECT *, (ssd / joinsize) AS weight FROM Ssd
	QueryOperator *ssdOp = (QueryOperator *) ssd;
	int ssdColPos        = nTp + 1;
	AttributeDef *ssdColDef        = getAttrDefByPos(ssdOp, ssdColPos);
	AttributeDef *joinsizeInSsdDef = getAttrDefByPos(ssdOp, nFtb);
	List *wtProjExprs = NIL;
	List *wtAttrNames = NIL;
	idx = 0;
	FOREACH(AttributeDef, ad, ssdOp->schema->attrDefs)
	{
		wtProjExprs = appendToTailOfList(wtProjExprs,
			createFullAttrReference(strdup(ad->attrName), 0, idx, INVALID_ATTR, ad->dataType));
		wtAttrNames = appendToTailOfList(wtAttrNames, strdup(ad->attrName));
		idx++;
	}
	// joinsize is still DT_LONG here; cast (see Ssd above for why a real
	// CastExpr is required) to DT_FLOAT so it matches ssd's DT_FLOAT type
	// and the division infers as float.
	Node *joinsizeAsFloat = (Node *) createCastExpr(
		(Node *) createFullAttrReference(strdup(joinsizeInSsdDef->attrName), 0, nFtb, INVALID_ATTR, joinsizeInSsdDef->dataType),
		DT_FLOAT);
	Node *wtExpr = (Node *) createOpExpr("/", LIST_MAKE(
		createFullAttrReference(strdup(ssdColDef->attrName), 0, ssdColPos, INVALID_ATTR, ssdColDef->dataType),
		joinsizeAsFloat));
	wtProjExprs = appendToTailOfList(wtProjExprs, wtExpr);
	wtAttrNames = appendToTailOfList(wtAttrNames, strdup("weight"));
	ProjectionOperator *wt = createProjectionOp(wtProjExprs, ssdOp, NIL, wtAttrNames);
	ssdOp->parents = singleton((QueryOperator *) wt);
	INFO_OP_LOG("Wt operator tree:", (Node *) wt);

	// --- Build Sftb ---
	// SELECT *, ROW_NUMBER() OVER (PARTITION BY y ORDER BY ssd DESC, ssp DESC, random()) AS seqNum FROM Wt
	QueryOperator *wtOp        = (QueryOperator *) wt;
	AttributeDef *yInWtDef     = getAttrDefByPos(wtOp, yPos);
	AttributeDef *ssdInWtDef   = getAttrDefByPos(wtOp, ssdColPos);
	AttributeDef *sspInWtDef   = getAttrDefByPos(wtOp, sspColPos);

	List *sftbPartBy = singleton(
		createFullAttrReference(strdup(yInWtDef->attrName), 0, yPos, INVALID_ATTR, yInWtDef->dataType));

	List *sftbOrderBy = LIST_MAKE(
		createOrderExpr((Node *) createFullAttrReference(strdup(ssdInWtDef->attrName), 0, ssdColPos, INVALID_ATTR, ssdInWtDef->dataType),
			SORT_DESC, SORT_NULLS_LAST),
		createOrderExpr((Node *) createFullAttrReference(strdup(sspInWtDef->attrName), 0, sspColPos, INVALID_ATTR, sspInWtDef->dataType),
			SORT_DESC, SORT_NULLS_LAST),
		createOrderExpr((Node *) createFunctionCall(strdup("random"), NIL),
			SORT_ASC, SORT_NULLS_LAST));

	Node *rowNumCall = (Node *) createFunctionCall(strdup("row_number"), NIL);

	WindowOperator *sftb = createWindowOp(
		rowNumCall,
		sftbPartBy,
		sftbOrderBy,
		NULL,  // no frame
		strdup("seqNum"),
		wtOp,
		NIL
	);
	wtOp->parents = singleton((QueryOperator *) sftb);
	INFO_OP_LOG("Sftb operator tree:", (Node *) sftb);

	// --- Build Sftb2 ---
	// SELECT * FROM Sftb WHERE seqNum <= ROUND(ssp, 0)
	QueryOperator *sftbOp     = (QueryOperator *) sftb;
	int seqNumPos             = LIST_LENGTH(wtOp->schema->attrDefs);  // appended right after Wt's last attr
	AttributeDef *seqNumDef   = getAttrDefByPos(sftbOp, seqNumPos);
	AttributeDef *sspInSftbDef = getAttrDefByPos(sftbOp, sspColPos);  // position unchanged

	Node *roundSsp = (Node *) createFunctionCall(strdup("round"), LIST_MAKE(
		createFullAttrReference(strdup(sspInSftbDef->attrName), 0, sspColPos, INVALID_ATTR, sspInSftbDef->dataType),
		createConstInt(0)));

	Node *sftb2Cond = (Node *) createOpExpr("<=", LIST_MAKE(
		createFullAttrReference(strdup(seqNumDef->attrName), 0, seqNumPos, INVALID_ATTR, seqNumDef->dataType),
		roundSsp));

	SelectionOperator *sftb2 = createSelectionOp(sftb2Cond, sftbOp, NIL, NIL);
	sftbOp->parents = singleton((QueryOperator *) sftb2);
	INFO_OP_LOG("Sftb2 operator tree:", (Node *) sftb2);

	return (Node *) sftb2;
}


static List *children_Of_Join(QueryOperator *op, List *collectChildOps)
{
	if (isA(op, JoinOperator))
	{
		QueryOperator *lChild = OP_LCHILD(op);
		QueryOperator *rChild = OP_RCHILD(op);

		if (isA(lChild, JoinOperator))
			collectChildOps = children_Of_Join(lChild, collectChildOps);
		else
			collectChildOps = appendToTailOfList(collectChildOps, lChild);

		if (isA(rChild, JoinOperator))
			collectChildOps = children_Of_Join(rChild, collectChildOps);
		else
			collectChildOps = appendToTailOfList(collectChildOps, rChild);
	}

	return collectChildOps;
}
