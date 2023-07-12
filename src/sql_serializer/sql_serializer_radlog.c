/*-----------------------------------------------------------------------------
 *
 * sql_serializer_dl.c
 *			  
 *		
 *		AUTHOR: lord_pretzel
 *
 *		
 *
 *-----------------------------------------------------------------------------
 */

#include "common.h"
#include "instrumentation/timing_instrumentation.h"
#include "mem_manager/mem_mgr.h"
#include "log/logger.h"

#include "analysis_and_translate/translator_dl.h"
#include "sql_serializer/sql_serializer_oracle.h"
#include "model/node/nodetype.h"
#include "model/query_operator/query_operator.h"
#include "model/query_operator/operator_property.h"
#include "model/datalog/datalog_model.h"
#include "model/list/list.h"
#include "model/set/set.h"
#include "utility/string_utils.h"

static void fixProgramDataTypes(DLProgram *p, HashMap *predToRules);
//static void replaceSingleOccVarsWithUnderscore(DLProgram *p);
static void datalogToStr(StringInfo str, Node *n, int indent);
static Node *fixExpression(Node *n);
static Node *fixExpressionMutator (Node *n, void *context);
static void handleExpressions(StringInfo str, Node *n);
static char *exprToRDL (Node *e);
static void exprToRDLInternal (StringInfo str, Node *e);
static void funcToRDL(StringInfo str, FunctionCall *f);
static void opToRDL (StringInfo str, Operator *o);
static char *dataTypeToRDL (DataType d);
static char *constToRDL(Constant *c);
static int exprCount;
static int exprTotal;

char *
serializeOperatorModelRDL(Node *q)
{
    StringInfo str = makeStringInfo();
    HashMap *predToRules = NEW_MAP(Constant,List);

    //TODO change operators and functions in expressions to LogiQL equivalent

    // add a rule to output query result in Radlog
    DLProgram *p = (DLProgram *) q;

    // fix data types
    fixProgramDataTypes(p, predToRules);

    // add predicate
    char *headPred = NULL;
	int i = 0;
	int numArgs = 0;

	headPred = p->ans;

	if (headPred == NULL)
	{
	    DLRule *a = (DLRule *) getNthOfListP(p->rules,0);
        headPred = a->head->rel;
	}

	//replaceSingleOccVarsWithUnderscore(p);

	FOREACH(DLRule,r,p->rules)
    {
	    if (streq(headPred, getHeadPredName(r)))
	    {
	        DLAtom *a = r->head;
	        numArgs = LIST_LENGTH(a->args);
	    }
    }

/*
	// output query rule (predicate _ in Radlog)
	appendStringInfoString(str, "_(");
	for(i = 0; i < numArgs; i++)
	{
	    appendStringInfo(str, "X%u%s", i, (i < numArgs -1 ? ", " : ""));
	}
	appendStringInfo(str, ") <- _%s(", headPred);
	for(i = 0; i < numArgs; i++)
    {
        appendStringInfo(str, "X%u%s", i, (i < numArgs -1 ? ", " : ""));
    }
    appendStringInfoString(str, ").\n");
//	appendStringInfo(str,"%s",CONCAT_STRINGS("_(X,Y) <- _", headPred, "(X,Y).\n"));

*/

    numArgs = numArgs + 1;
    i = i + 1;
    
    datalogToStr(str, q, 0);

    return str->data;
}

//TODO 1) sanitize constants (remove '' from strings), they have to be lower-case), sanitize rel names (lowercase), translate expressions (e.g., string concat to skolems)


/*static void
replaceSingleOccVarsWithUnderscore(DLProgram *p)
{
	FOREACH(DLRule,r,p->rules)
	{
		List *headVars = getHeadExprVars(r);
		HashMap *varToCount = NEW_MAP(DLVar, Constant);
		List *allVars;

		// head vars cannot be replaced with _
		FOREACH(DLVar,v,headVars)
		{
		    MAP_INCR_STRING_KEY(varToCount,v->name);
		}

		// might be comparison atom
		FOREACH(DLAtom,a,r->body)
		{
			FOREACH(Node,n,a->args)
			{
	            Set *argVars = makeNodeSetFromList(getExprVars(n));

	            FOREACH_SET(DLVar,v,argVars)
	            {
	                MAP_INCR_STRING_KEY(varToCount,strdup(v->name));
	            }
			}
		}

		DEBUG_NODE_BEATIFY_LOG("var counts", varToCount);

		// replace all occurances of variables that
		allVars = getExprVars((Node *) r);
		FOREACH(DLVar,v,allVars)
		{
		    int c = INT_VALUE(MAP_GET_STRING(varToCount, v->name));
		    if (c == 0)
		    {
		        DEBUG_LOG("replace var %s with _", v->name);
		        v->name = strdup("_");
		    }
		}
	}
}*/

static void
fixProgramDataTypes(DLProgram *p, HashMap *predToRules)
{
    // determine pred -> rules
    FOREACH(DLRule,r,p->rules)
    {
        char *headPred = getHeadPredName(r);
        APPEND_TO_MAP_VALUE_LIST(predToRules,headPred,r);
    }
    FOREACH(DLAtom,f,p->facts)
    {
        char *relName = f->rel;
        APPEND_TO_MAP_VALUE_LIST(predToRules,relName,f);
    }

    // analyze rules to determine data types
    analyzeProgramDTs(p, predToRules);
}

static void
datalogToStr(StringInfo str, Node *n, int indent)
{
    if (n == NULL)
        return;

    switch(n->type)
    {
        case T_DLAtom:
        {
            DLAtom *a = (DLAtom *) n;
            int i = 1;
            int len = LIST_LENGTH(a->args);

            if (a->negated)
                appendStringInfoString(str, "! ");

            // make IDB predicate local
/*
            if (DL_HAS_PROP(a,DL_IS_IDB_REL) || !DL_HAS_PROP(a,DL_IS_EDB_REL))
                appendStringInfo(str, "%s(", CONCAT_STRINGS("_", a->rel));
            else
            	    appendStringInfo(str, "%s(", a->rel);
*/
            appendStringInfo(str, "%s(", a->rel);
            
            FOREACH(Node,arg,a->args)
            {
                datalogToStr(str, arg, indent);
                if (i++ < len)
                    appendStringInfoString(str, ",");
            }
            appendStringInfoString(str, ")");
        }
        break;
        case T_DLRule:
        {
            DLRule *r = (DLRule *) n;
            int i = 1;
            int len = LIST_LENGTH(r->body);
            
            indentString(str,indent);

            datalogToStr(str, (Node *) r->head, indent);
            appendStringInfoString(str, " <- ");
            FOREACH(Node,a,r->body)
            {
                datalogToStr(str, a, indent);
                if (i++ < len)
                    appendStringInfoString(str, ",");
            }

            handleExpressions(str, (Node *) r->head);
 
            appendStringInfoString(str, ".\n");
        }
        break;
        case T_DLComparison:
        {
            DLComparison *c = (DLComparison *) n;

            datalogToStr(str,getNthOfListP(c->opExpr->args, 0), indent);
            appendStringInfo(str, " %s ", c->opExpr->name);
            datalogToStr(str,getNthOfListP(c->opExpr->args, 1), indent);
//            appendStringInfo(str, "%s", exprToSQL((Node *) c->opExpr));
        }
        break;
        case T_DLVar:
        {
            DLVar *v = (DLVar *) n;

            appendStringInfo(str, "%s", v->name);
        }
        break;
        case T_DLProgram:
        {
            DLProgram *p = (DLProgram *) n;

            FOREACH(Node,f,p->facts)
            {
                datalogToStr(str,(Node *) f, 0);
            }
            FOREACH(Node,r,p->rules)
            {
                datalogToStr(str,(Node *) r, 0);
            }
        }
        break;
        case T_Constant:
            appendStringInfo(str, "%s",
                    constToRDL((Constant *) n));
        break;
        // provenance
        case T_List:
        {
            List *l = (List *) n;
            FOREACH(Node,el,l)
            datalogToStr(str,el, indent + 4);
        }
        break;
        default:
        {
            if (IS_EXPR(n))
            {
                DEBUG_NODE_BEATIFY_LOG("expr before transformation", n);
                // add casts where necessary
                n = addCastsToExpr(n, TRUE);
                DEBUG_NODE_BEATIFY_LOG("expr after adding casts", n);

                // translate operators and translate casts into radlog function calls
                n = fixExpression(n);
                DEBUG_NODE_BEATIFY_LOG("expr after fixing to RDL", n);

                // output expression
                char *result = exprToRDL(n);
                DEBUG_LOG("expr: %s", result);

                // Generates the X# variable name and replaces expression with the X# name in the rule head
                appendStringInfo(str, "X%u", exprTotal+1);
                // Increment total number of expressions in program
                exprTotal = exprTotal + 1;

//                char *result = NULL;
//                result = replaceSubstr(exprToSQL(n), " || ", " + ");
//                result = replaceSubstr(result, "'", "\"");
                //appendStringInfo(str, "%s", result);
            }
            else
                FATAL_LOG("should have never come here, datalog program should"
                        " not have nodes like this: %s",
                        beatify(nodeToString(n)));
        }
        break;
    }
}


// Function to handle expressions:
// If an argument in the head of a rule is an expression,
// create X# variable, then append the corresponding expression to the end of rule
static void
handleExpressions(StringInfo str, Node *n)
{
    DLAtom *a = (DLAtom *) n;

    FOREACH(Node,arg,a->args)
    {  
       if (IS_EXPR(arg))
       {
          // output expression
          char *result = exprToRDL(arg);
          
          // Resulting expression gets appended to the end of rule body to act as computed column in radlog             
          appendStringInfo(str, ", X%u = %s", exprCount+1, result);
          // increment expression count
          exprCount = exprCount + 1;
        }
        else
        {
          DEBUG_LOG("Arg is not expression");
        }
    }
    return;
}


static Node *
fixExpression(Node *n)
{
    n = fixExpressionMutator(n, NULL);
    return n;
}


static Node *
fixExpressionMutator (Node *n, void *context)
{
    if (n == NULL)
        return NULL;

    if(isA(n, Operator))
    {
        Operator *o = (Operator *) n;

        if (streq(o->name, "||"))
        {
            o->name = "+";
        }


        FOREACH_LC(arg,o->args)
        {
            Node *a = LC_P_VAL(arg);
            LC_P_VAL(arg) = fixExpressionMutator(a, context);
        }

        return (Node *) o;
    }

    if (isA(n, CastExpr))
    {
        CastExpr *c = (CastExpr *) n;
        FunctionCall *f;
        StringInfo fName;
        DataType inType = typeOf(c->expr);
        Node *arg;

        fName = makeStringInfo();
        appendStringInfo(fName, "%s:%s:convert", dataTypeToRDL(inType), dataTypeToRDL(c->resultDT));

        arg = fixExpressionMutator(c->expr, context);
        f = createFunctionCall(fName->data, singleton(arg));

        return (Node *) f;
    }

//    if(isA(n, FunctionCall))
//    {
//        FunctionCall *f = (FunctionCall *) n;
//
//    }

    return mutate(n, fixExpressionMutator, context);
}

static char *
exprToRDL (Node *e)
{
    StringInfo str = makeStringInfo();

    exprToRDLInternal(str, e);

    return str->data;
}

static void
exprToRDLInternal (StringInfo str, Node *e)
{
    if (e == NULL)
        return;

    switch(e->type)
    {
        case T_DLVar:
            appendStringInfo(str, "%s", ((DLVar *) e)->name);
            break;
        case T_Constant:
            appendStringInfoString(str,constToRDL((Constant *) e));
            break;
        case T_FunctionCall:
            funcToRDL(str, (FunctionCall *) e);
            break;
        case T_Operator:
            opToRDL(str, (Operator *) e);
            break;
        case T_List:
        {
            int i = 0;
            FOREACH(Node,arg,(List *) e)
            {
                appendStringInfoString(str, ((i++ == 0) ? "(" : ", "));
                exprToRDLInternal(str, arg);
            }
            appendStringInfoString(str,")");
        }
        break;
        default:
            FATAL_LOG("not an RDL supported expression node <%s>", nodeToString(e));
    }
}

static void
funcToRDL(StringInfo str, FunctionCall *f)
{
    appendStringInfoString(str, f->functionname);

    appendStringInfoString(str, "[");

    int i = 0;
    FOREACH(Node,arg,f->args)
    {
        appendStringInfoString(str, ((i++ == 0) ? "" : ", "));
        exprToRDLInternal(str, arg);
    }

    appendStringInfoString(str, "]");
}

static void
opToRDL (StringInfo str, Operator *o)
{
    appendStringInfoString(str, "(");

    FOREACH(Node,arg,o->args)
    {
        exprToRDLInternal(str,arg);
        if(arg_his_cell != o->args->tail)
            appendStringInfo(str, " %s ", o->name);
    }

    appendStringInfoString(str, ")");
}

static char *
dataTypeToRDL (DataType d)
{
    switch (d)
    {
        case DT_INT:
            return "int";
        case DT_STRING:
            return "string";
        case DT_FLOAT:
             return "float";
        case DT_BOOL:
             return "boolean";
        default:
            return "string"; //TODO
    }
}

static char *
constToRDL(Constant *c)
{
    if (CONST_IS_NULL(c))
        return strdup("null");
    if (c->constType == DT_STRING)
    {
        return CONCAT_STRINGS("\"",STRING_VALUE(c),"\"");
    }
    if (c->constType == DT_BOOL)
    {
        if (BOOL_VALUE(c))
            return "true";
        else
            return "false";
    }
    else
        return CONST_TO_STRING(c);
}

char *
serializeQueryRDL(QueryOperator *q)
{
    FATAL_LOG("should never have ended up here");
    return NULL;
}


char *
quoteIdentifierRDL (char *ident)
{
    return ident; //TODO
}
