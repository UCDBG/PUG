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

static Node *rewritePartition (Node *rewrittenTree);
static Node *children_Of_Join (QueryOperator *op, List *collectChildOps);
//void children_Of_Join (QueryOperator *op, List *collectChildOps);


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

	// access join operator
	// TODO: always duplicate eliminator and projection operators
	QueryOperator *po = (QueryOperator *) getHeadOfListP(in->inputs);
	QueryOperator *op = (QueryOperator *) getHeadOfListP(po->inputs);

	// access children of join operator
	List *collectChildOps = NIL;
	Node *child = children_Of_Join(op, collectChildOps);

	INFO_OP_LOG("collected input operators:", (Node *) child);

//	// Example of creating a projection
//	int pos = 0;
//	List *projExpr = ((ProjectionOperator *) child)->projExprs;
//	ProjectionOperator *op;
//
//	FOREACH(AttributeDef,p,child->schema->attrDefs)
//	{
//		projExpr = appendToTailOfList(projExpr,
//				createFullAttrReference(strdup(p->attrName), 0, pos, 0, p->dataType));
//
//		pos++;
//	}
//
//	op = createProjectionOp(projExpr, child, NIL, getAttrNames(child->schema));
//	child->parents = singleton(op);
//	child = (QueryOperator *) op;

//	// Create the window function
//	WindowOperator *wo = NULL;
//	List *partitionBy = NIL;
//	partitionBy = ((ProjectionOperator *) child)->projExprs;
//
//	// add window functions for partitioning
//	AttributeReference *ar = (AttributeReference *) getNthOfListP(partitionBy,1);
//	Node *cntFunc = (Node *) createFunctionCall(strdup("COUNT"), singleton(ar));
//
//	wo = createWindowOp(cntFunc,
//			partitionBy,
//			NIL,
//			NULL,
//			strdup(RESULT_WO_ATTR),
//			child,
//			NIL
//	);
//
//	addParent(child, (QueryOperator *) wo);
//	INFO_OP_LOG("tree with added window function:", wo);


	return (Node *) child;
}


static Node *children_Of_Join(QueryOperator *op, List *collectChildOps)
{
	QueryOperator *lChild;
	QueryOperator *rChild;

	if(isA(op,JoinOperator))
	{
		lChild = OP_LCHILD(op);
	    rChild = OP_RCHILD(op);

	    if(isA(lChild,JoinOperator))
	    	children_Of_Join(lChild, collectChildOps);
	    else
			collectChildOps = appendToTailOfList(collectChildOps, copyObject(lChild));

	    if(isA(rChild,JoinOperator))
	    	children_Of_Join(rChild, collectChildOps);
	    else
	    	collectChildOps = appendToTailOfList(collectChildOps, copyObject(rChild));
	}

	return (Node *) collectChildOps;
}