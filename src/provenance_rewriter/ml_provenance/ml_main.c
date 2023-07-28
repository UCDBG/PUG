/*-----------------------------------------------------------------------------
 *
 * gp_main.c
 *			  
 *		
 *		AUTHOR: lord_pretzel & seokki
 *
 *		
 *
 *-----------------------------------------------------------------------------
 */

#include "common.h"
#include "log/logger.h"

#include "model/datalog/datalog_model.h"

#include "provenance_rewriter/ml_provenance/ml_main.h"
#include "provenance_rewriter/ml_provenance/ml_bottom_up_program.h"


Node *
rewriteForML(Node *input)
{

    if (isA(input, DLProgram))
    {
        DLProgram *p = (DLProgram *) input;
        if (IS_ML_PROV(p))
        {
            p = createBottomUpMLprogram(p);
            //TODO TopDown decide based on option
        }
        INFO_LOG("program for compute ML is:\n%s",
                datalogToOverviewString((Node *) p));
        DEBUG_NODE_BEATIFY_LOG("program details:", p);
        return (Node *) p;
    }
    else
        FATAL_LOG("currently only GP computation for DLPrograms supported.");

    return input;
}
