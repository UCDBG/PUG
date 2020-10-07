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
DLFILE="${1}"
OUT="${2}"
DOTFILE="${OUT}.dot"
PDFFILE="${OUT}.pdf"

if ! hash dot 2>/dev/null; then 
	echo "dot command not found (install graphviz)"
	exit 1
fi
	
if [ $# -lt 2 ]; then
	echo "Description: read a Datalog program with provenance requests from an input file, run it, create a dot script of the resulting provenance graph, and create a pdf from this dot script using graphviz."
    echo "Usage: pass at least two parameters, the first one is the file storing the Datalog query and provenance request and the second one is the name of the file name for the output provenance graph."
	echo " "
    echo "pug-from-file-to-provgraph.sh myquery.dl my_prov_graph" 
    exit 1
fi

if [ ! -f ${DLFILE} ]; then
	echo "File ${DLFILE} not found!"
	exit 1
fi

########################################
# RUN COMMAND
##########
echo "-- compute edge relation of provenance graph for ${DLFILE}"
if [[ ${CONNECTION_PARAMS} == *"oracle"* ]]; then
	${PUG} ${CONNECTION_PARAMS} -Boracle.servicename TRUE ${PUG_DL_PLUGINS} -Pexecutor gp -Cattr_reference_consistency FALSE -Cschema_consistency FALSE  -Cunique_attr_names FALSE -sqlfile ${DLFILE} ${*:3} > ${DOTFILE}
fi

if [[ ${CONNECTION_PARAMS} == *"postgres"* ]]; then
	${PUG} ${CONNECTION_PARAMS} ${PUG_DL_PLUGINS} -Pexecutor gp -Cattr_reference_consistency FALSE -Cschema_consistency FALSE  -Cunique_attr_names FALSE -sqlfile ${DLFILE} ${*:3} > ${DOTFILE}
fi
##########
echo "-- run graphviz on ${DOTFILE} to produce PDF file ${PDFFILE}"
dot -Tpdf -o ${PDFFILE} ${DOTFILE}

##########
echo "-- open the pdf file"
if [[ $OSTYPE == darwin* ]]; then
	echo "    - on a mac use open"
	open ${PDFFILE}
else
	for $P in $LINUX_PDFPROGS; do
		if checkProgram $P;
		then
			$P ${PDFFILE} > /dev/null 2>&1 &
			exit 0
		fi
		echo "    - apparently you do not have ${P}"
	done
	echo "did not find a pdf viewer, please open ${PDFFILE} manually"
fi
