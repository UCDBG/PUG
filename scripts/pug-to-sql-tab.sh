#!/bin/bash
########################################
# VARS
# Directory this script resides in
pushd $(dirname "${0}") > /dev/null
DIR=$(pwd -L)
popd > /dev/null
#########################################
# READ USER CONFIGUATION
CONF_FILE=.pug
PUG=${DIR}/../src/command_line/gprom
PUG_CONF=${DIR}/../${CONF_FILE}
source ${DIR}/pug_basic.sh
#########################################
# PARAMETERS
PROGRAM="${2}"
LOG="-log -loglevel ${1}"

if [ $# -lt 2 ]; then
	echo "Description: translate Datalog program with provenance requests and regular path queries into SQL."
    echo "Usage: pass at least two parameters, the first one is the loglevel [0 : NONE up to 5 : TRACE] and the second one is a query."
    echo "pug-to-sql.sh 3 \"Q(X) :- R(X,Y). WHY(Q(1)).\""
    exit 1
fi
########################################
# RUN COMMAND
POSTGRES=""

# RUN COMMAND
if [[ ${CONNECTION_PARAMS} == *"oracle"* ]]; then
	ORACLE="-Boracle.servicename TRUE"
else
	ORACLE=${POSTGRES}
fi

${PUG} ${LOG} -sql "${PROGRAM}" ${CONNECTION_PARAMS} ${ORACLE} ${PUG_DL_PLUGINS} -Pexecutor sql -attr_dom -tabular -Cattr_reference_consistency FALSE -Cschema_consistency FALSE  -Cunique_attr_names FALSE -treeify-algebra-graphs FALSE ${*:3}

