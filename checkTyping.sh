#!/bin/bash

score=0
scorePos=0
scoreNeg=0
max=0
maxPos=0
maxNeg=0

prgmFail=0

echo "Tests positifs (fichiers dans tests/good/)"

for f in tests/typing/good/*.scala tests/typingAdd/good/*.scala tests/exec/*.scala tests/exec-fail/*.scala; do
    maxPos=`expr $maxPos + 1`;
    echo $f
    rm -f out
    ./pscala --type-only $f > out
	case $? in
		0) scorePos=`expr $scorePos + 1` ;;
		1) echo "  ECHEC du typing pour $f" ;;
		2) prgmFail=`expr $prgmFail + 1`;echo "  ECHEC du programme pour $f" ;;
    esac
done
echo

echo "Tests négatifs (fichiers dans tests/bad/)"

for f in tests/typing/bad/*.scala tests/typingAdd/bad/* ; do
    maxNeg=`expr $maxNeg + 1`;
    echo $f
    rm -f out
	./pscala --type-only $f > out 2>&1
	
	case $? in
		0) echo "  ECHEC : le typing de $f devrait échouer" ;;
   		1) scoreNeg=`expr $scoreNeg + 1` ;;
		2) prgmFail=`expr $prgmFail + 1`;echo "  ECHEC du programme pour $f" ;;
    esac
done

rm out

echo
max=`expr $maxPos + $maxNeg`
score=`expr $scorePos + $scoreNeg`
percent=`expr 100 \* $score / $max`;
echo "Score: $score / $max tests, soit $percent%"
echo "Dont $scorePos / $maxPos positifs, $scoreNeg / $maxNeg négatifs"
echo "Dont `expr $max - $prgmFail - $score` / $max mauvais résultats"
echo "Dont $prgmFail / $max échecs du programme (exit 2)"
