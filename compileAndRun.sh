#!/bin/bash

debug=""
if [ $1 = "-g" ] ; then
	debug="-g "
	shift
fi

./pscala -o "/tmp/pscala_tmp.s" "$1" && \
	gcc $debug -o "/tmp/pscala_tmp" "/tmp/pscala_tmp.s" && \
	/tmp/pscala_tmp

if [ "$debug" != "" ]; then
	gdb /tmp/pscala_tmp
fi

>&2 echo "[[return code: $?]]"

rm -f /tmp/pscala_tmp{.s,}
