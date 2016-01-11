#!/usr/bin/bash

ver=`ocamlopt -version | sed 's/\.[^\.]*$//g'`
vercmp=`echo "$ver < 4.02" | bc -l`
if (( $vercmp )) ; then
	>&2 echo -e "\n\tFATAL: Bad OCaml version. You must have OCaml 4.02 or newer for this to work."
	exit 1
fi
