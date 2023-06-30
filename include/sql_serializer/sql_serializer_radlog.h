/*-----------------------------------------------------------------------------
 *
 * sql_serializer_radlog.h
 *		
 *
 *		AUTHOR: seokki
 *
 *-----------------------------------------------------------------------------
 */

#ifndef INCLUDE_SQL_SERIALIZER_SQL_SERIALIZER_RDL_H_
#define INCLUDE_SQL_SERIALIZER_SQL_SERIALIZER_RDL_H_

#include "model/node/nodetype.h"
#include "model/query_operator/query_operator.h"

extern char *serializeOperatorModelRDL(Node *q);
extern char *serializeQueryRDL(QueryOperator *q);
extern char *quoteIdentifierRDL (char *ident);


#endif /* INCLUDE_SQL_SERIALIZER_SQL_SERIALIZER_RDL_H_ */
