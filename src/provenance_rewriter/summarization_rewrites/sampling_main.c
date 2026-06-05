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
// Toggle: define to stop after partTa (skip Fta window operator)
// #define TEST_PART_TA_ONLY

static Node *rewritePartition (Node *rewrittenTree);
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

//	DEBUG_LOG("sample size: %f", sampleSize);
//	result = (Node *) rewrittenTree;
//	return result;

	DEBUG_LOG("sampling options are: qType: %s, sample size: %f",
			  ProvQuestionToString(qType), sampleSize);

//	if(qType == PROV_Q_WHY)
//	{

	//TODO: implement the sampling algorithm
	Node *rewrittenHead = (Node *) getHeadOfListP((List *) rewrittenTree);
	INFO_OP_LOG("input rewritten trees:", rewrittenTree);

	//Step1: partitioning
	rewrittenTreePart = rewritePartition(rewrittenHead);
	result = (Node *) rewrittenTreePart;
//	}

	return result;
}


static Node *rewritePartition (Node *rewrittenTree)
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

	// --- Build partTa ---
	// Project only the left-side attributes (positions 0..nLeft-1) from the
	// join output, then wrap with DISTINCT.  The Selection (op) and Join
	// (joinOp) are reused as-is underneath.


	List *projExprs = NIL;
	List *attrNames = NIL;
	int i = 0;
	FOREACH(AttributeDef, ad, joinOp->schema->attrDefs)
	{
		if (i < nLeft) // Taking X, Z, C1 into projExprs
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

	// List *dupAttrExprs = NIL;
	// i = 0;
	// FOREACH(AttributeDef, ad, ((QueryOperator *) partTaProj)->schema->attrDefs)
	// {
	// 	dupAttrExprs = appendToTailOfList(dupAttrExprs,
	// 		createFullAttrReference(strdup(ad->attrName), 0, i,
	// 								INVALID_ATTR, ad->dataType));
	// 	i++;
	// }

	DuplicateRemoval *partTa = createDuplicateRemovalOp(
		projExprs, (QueryOperator *) partTaProj, NIL, attrNames);
	((QueryOperator *) partTaProj)->parents = singleton((QueryOperator *) partTa);

	// CTE for partTa to be referenced by Fta
	SET_BOOL_STRING_PROP((Node *) partTa, PROP_MATERIALIZE);
	INFO_OP_LOG("partTa operator tree:", (Node *) partTa);

#ifdef TEST_PART_TA_ONLY
	return (Node *) partTa;
#endif

	// Default: use the join-based partTa; uncomment USE_EXISTS_PART_TA to switch
	// #define USE_EXISTS_PART_TA
	QueryOperator *partTaOp = (QueryOperator *) partTa;
#ifdef USE_EXISTS_PART_TA
	{
		QueryOperator *rightHop  = (QueryOperator *) getNthOfListP(collectChildOps, 1);
		QueryOperator *outerHop  = (QueryOperator *) copyObject(leftChild);
		QueryOperator *innerHop  = (QueryOperator *) copyObject(rightHop);
		outerHop->parents = NIL;
		innerHop->parents = NIL;

		// f.x = t.z  (inner source = outer connecting node, correlated)
		AttributeDef *outerZ_def = getAttrDefByPos(outerHop, 1);
		AttributeDef *outerC_def = getAttrDefByPos(outerHop, 2);
		AttributeDef *innerX_def = getAttrDefByPos(innerHop, 0);
		AttributeDef *innerC_def = getAttrDefByPos(innerHop, 2);
		Node *ec1 = (Node *) createOpExpr("=", LIST_MAKE(
			createFullAttrReference(strdup(innerX_def->attrName), 0, 0, 0, innerX_def->dataType),
			createFullAttrReference(strdup(outerZ_def->attrName), 0, 1, 1, outerZ_def->dataType)));
		// f.c > t.c  (inner cost > outer cost, correlated)
		Node *ec2 = (Node *) createOpExpr(">", LIST_MAKE(
			createFullAttrReference(strdup(innerC_def->attrName), 0, 2, 0, innerC_def->dataType),
			createFullAttrReference(strdup(outerC_def->attrName), 0, 2, 1, outerC_def->dataType)));
		SelectionOperator *innerSel = createSelectionOp(AND_EXPRS(ec1, ec2), innerHop, NIL,
														getAttrNames(innerHop->schema));
		innerHop->parents = singleton((QueryOperator *) innerSel);

		// NestingOperator(EXISTS): schema = outer attrs + nesting_eval_0 BOOL
		List *nestAttrNames = getAttrNames(outerHop->schema);
		List *nestDts       = getDataTypes(outerHop->schema);
		nestAttrNames = appendToTailOfList(nestAttrNames, strdup("nesting_eval_0"));
		nestDts       = appendToTailOfListInt(nestDts, DT_BOOL);
		NestingOperator *nestOp = createNestingOp(NESTQ_EXISTS, NULL,
												  LIST_MAKE(outerHop, (QueryOperator *) innerSel),
												  NIL, nestAttrNames, nestDts);
		outerHop->parents = singleton((QueryOperator *) nestOp);
		((QueryOperator *) innerSel)->parents = singleton((QueryOperator *) nestOp);

		// Selection: WHERE nesting_eval_0 = TRUE
		int nestEvalPos = LIST_LENGTH(outerHop->schema->attrDefs);
		Node *existsCond = (Node *) createOpExpr("=", LIST_MAKE(
			createFullAttrReference(strdup("nesting_eval_0"), 0, nestEvalPos, 0, DT_BOOL),
			(Node *) createConstBool(TRUE)));
		SelectionOperator *existsSel = createSelectionOp(existsCond, (QueryOperator *) nestOp,
														 NIL, getAttrNames(((QueryOperator *) nestOp)->schema));
		((QueryOperator *) nestOp)->parents = singleton((QueryOperator *) existsSel);

		// Projection: keep only outer attrs, drop nesting_eval_0
		List *existsProjExprs  = NIL;
		List *existsAttrNames  = NIL;
		int j = 0;
		FOREACH(AttributeDef, ad, outerHop->schema->attrDefs)
		{
			existsProjExprs = appendToTailOfList(existsProjExprs,
				createFullAttrReference(strdup(ad->attrName), 0, j, INVALID_ATTR, ad->dataType));
			existsAttrNames = appendToTailOfList(existsAttrNames, strdup(ad->attrName));
			j++;
		}
		ProjectionOperator *existsProj = createProjectionOp(existsProjExprs,
															(QueryOperator *) existsSel,
															NIL, existsAttrNames);
		((QueryOperator *) existsSel)->parents = singleton((QueryOperator *) existsProj);

		// DISTINCT
		List *existsDupExprs = NIL;
		j = 0;
		FOREACH(AttributeDef, ad, ((QueryOperator *) existsProj)->schema->attrDefs)
		{
			existsDupExprs = appendToTailOfList(existsDupExprs,
				createFullAttrReference(strdup(ad->attrName), 0, j, INVALID_ATTR, ad->dataType));
			j++;
		}
		DuplicateRemoval *partTa_exists = createDuplicateRemovalOp(existsDupExprs,
																   (QueryOperator *) existsProj,
																   NIL, existsAttrNames);
		((QueryOperator *) existsProj)->parents = singleton((QueryOperator *) partTa_exists);
		SET_BOOL_STRING_PROP((Node *) partTa_exists, PROP_MATERIALIZE);
		INFO_OP_LOG("partTa_exists operator tree:", (Node *) partTa_exists);

		partTaOp = (QueryOperator *) partTa_exists;
	}
	return (Node *) partTaOp;
#endif

	// --- Build Fta ---
	// SELECT *, count(Z) OVER (PARTITION BY C_0_0, Z) AS numofz
	// FROM partTa  (or partTa_exists when USE_EXISTS_PART_TA is defined)

	// count(Z) — Z is position 1 in partTa schema (hardcoded the position based, use join attributes with nLeft)
	AttributeDef *zDef = getAttrDefByPos(partTaOp, 1);
	AttributeReference *zRef = createFullAttrReference(
		strdup(zDef->attrName), 0, 1, INVALID_ATTR, zDef->dataType);
	Node *cntFunc = (Node *) createFunctionCall(strdup("count"), singleton(zRef));

	// PARTITION BY C_0_0 (pos 0), Z (pos 1)
	AttributeDef *xDef = getAttrDefByPos(partTaOp, 0);
	List *partitionBy = LIST_MAKE(
		createFullAttrReference(strdup(xDef->attrName),  0, 0, INVALID_ATTR, xDef->dataType),
		createFullAttrReference(strdup(zDef->attrName), 0, 1, INVALID_ATTR, zDef->dataType)
	);
	// redundant attr ref, re-check

	WindowOperator *fta = createWindowOp(
		cntFunc,
		partitionBy,
		NIL,   // no ORDER BY
		NULL,  // no frame
		strdup("numofz"),
		partTaOp,
		NIL
	);
	addParent(partTaOp, (QueryOperator *) fta);

	INFO_OP_LOG("Fta operator tree:", (Node *) fta);

	return (Node *) fta;
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


