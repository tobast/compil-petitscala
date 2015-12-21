#!/bin/bash

./pscala -o "/tmp/pscala_tmp.s" "$1" && \
	gcc -o "/tmp/pscala_tmp" "/tmp/pscala_tmp.s" && \
	/tmp/pscala_tmp

rm -f /tmp/pscala_tmp{.s,}
