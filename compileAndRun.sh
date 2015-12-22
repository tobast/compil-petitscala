#!/bin/bash

debug=""
if [ $1 = "-g" ] ; then
	debug="-g -O0 "
	shift
fi

./pscala -o "/tmp/pscala_tmp.s" "$1" && \
	gcc $debug -o "/tmp/pscala_tmp" "/tmp/pscala_tmp.s" && \
	(if [ "$debug" = "" ] ; then /tmp/pscala_tmp ; fi)

if [ "$debug" != "" ]; then
	gdb /tmp/pscala_tmp
fi

>&2 echo "[[return code: $?]]"

rm -f /tmp/pscala_tmp{.s,}
