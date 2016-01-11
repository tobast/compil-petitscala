#!/bin/bash

score=0
scorePos=0
scoreNeg=0
max=0
maxPos=0
maxNeg=0

prgmFail=0

txtred='\e[0;31m'
txtrst='\e[0m'

if ! [ -d tests/exec_add ] ; then
	echo "Cloning exec_add repository..."
	git clone https://compil.tobast.fr/git/exec_add tests/exec_add
else
	echo "Pulling exec_add repository..."
	(cd tests/exec_add && git pull)
fi

echo "Tests positifs (fichiers dans tests/good/)"

for f in tests/exec/*.scala tests/exec_add/good/*.scala; do
    maxPos=`expr $maxPos + 1`;
    echo -n $f
	./pscala -o /tmp/pscala_tmp.s "$f" 2>&1 > /dev/null
	out=$?
	if [ -f /tmp/pscala_tmp.s ] ; then
		gcc -o /tmp/pscala_tmp /tmp/pscala_tmp.s 2>&1 > /dev/null
		out=`expr $out + $?`
	fi
	if (( $out > 0 )) ; then
		prgmFail=`expr $prgmFail + 1`
		echo -n -e "\r${txtred}ECHEC de pscala pour $f" 

	else
		outfile="`dirname $f`/`basename $f .scala`.out"
		/tmp/pscala_tmp 2>/dev/null | diff - "$outfile" > /dev/null
		if (( $? == 0 )); then
			scorePos=`expr $scorePos + 1`
		else
			echo -n -e "\r${txtred}ECHEC d'exécution pour $f"
		fi
	fi
	echo -e "${txtrst}"
done
echo

echo "Tests négatifs (fichiers dans tests/bad/)"

for f in tests/exec-fail/*.scala ; do
    maxNeg=`expr $maxNeg + 1`;
    echo $f
	./pscala -o /tmp/pscala_tmp.s "$f" > /dev/null 2>&1
	out=$?
	if [ -f /tmp/pscala_tmp.s ] ; then
		gcc -o /tmp/pscala_tmp /tmp/pscala_tmp.s 2>&1 >/dev/null
		out=`expr $out + $?`
	fi
	if (( $out == 0 )); then
		/tmp/pscala_tmp > /dev/null 2>&1
		if (( $? > 0 )); then
			scoreNeg=`expr $scoreNeg + 1`
		else
			echo "ERREUR: le programme, censé échouer, a terminé correctement."
		fi
	else
		scoreNeg=`expr $scoreNeg + 1`	
	fi
done

rm -f /tmp/pscala_tmp{,.s}

echo
max=`expr $maxPos + $maxNeg`
score=`expr $scorePos + $scoreNeg`
percent=`expr 100 \* $score / $max`;
echo "Score: $score / $max tests, soit $percent%"
echo "Dont $scorePos / $maxPos positifs, $scoreNeg / $maxNeg négatifs"
