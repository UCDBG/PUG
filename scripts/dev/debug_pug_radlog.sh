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
PUG=${DIR}/../../src/command_line/gprom
PUG_CONF=${DIR}/../../${CONF_FILE}
source ${DIR}/../pug_basic.sh
#########################################
if [ $# -le 1 ]; then
	echo "Description: use gdb to debug gprom for Datalog queries"
	echo " "
    echo "Usage: give at least two parameters, the first one is a loglevel, the second one is a Datalog query."
    echo "debug_pug.sh 3 \"Q(X) :- R(X,Y).;\""
    exit 1
fi

PROGRAM="${2}"
LOG="-log -loglevel ${1}"
###########################################
LLDB=lldb
GDB=gdb

if [[ $OSTYPE == darwin* ]]; then
	DEBUGGER=${LLDB}
	DEBUGOPT="--"
else
	DEBUGGER=${GDB}
	DEBUGOPT="--args"
fi
###########################################
POSTGRES=""

# RUN COMMAND
if [[ ${CONNECTION_PARAMS} == *"oracle"* ]]; then
	ORACLE="-Boracle.servicename TRUE"
else
	ORACLE=${POSTGRES}
fi


${DEBUGGER} ${DEBUGOPT} ${PUG} ${LOG} -sql "${PROGRAM}" ${CONNECTION_PARAMS} ${ORACLE} ${PUG_DL_PLUGINS} -Pparser dl -Panalyzer dl -Ptranslator dummy -Pexecutor dl -Psqlserializer radlog -whynot_adv -attr_dom -Cattr_reference_consistency FALSE -Cschema_consistency FALSE  -Cunique_attr_names FALSE ${*:3} 

