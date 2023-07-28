/*-----------------------------------------------------------------------------
 *
 * ml_bottom_up_program.h
 *		
 *
 *		AUTHOR: lord_pretzel
 *
 *-----------------------------------------------------------------------------
 */

#ifndef INCLUDE_PROVENANCE_REWRITER_GAME_PROVENANCE_ML_BOTTOM_UP_PROGRAM_H_
#define INCLUDE_PROVENANCE_REWRITER_GAME_PROVENANCE_ML_BOTTOM_UP_PROGRAM_H_

#include "model/datalog/datalog_model.h"

extern DLProgram *createBottomUpMLprogram (DLProgram *p);
extern HashMap *edbRels;

#endif /* INCLUDE_PROVENANCE_REWRITER_GAME_PROVENANCE_ML_BOTTOM_UP_PROGRAM_H_ */
