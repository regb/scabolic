#!/bin/sh

error=false
RUNNER="./scabolic smt"

echo "Running SMT solver on satisfiable instances ..."
for f in regression/smtlib/sat/*.smt2
do
  echo -n "Testing $f ..."
  if ! res=$(${RUNNER} $f 2> /dev/null); then
    echo "The solver did not exit correctly"
    error=true
  else
    echo " $res"
    if [ "$res" != "sat" ]; then error=true; echo "ERROR !!!"; fi
  fi
done

echo "Running SAT solver on unsatisfiable instances ..."
for f in regression/smtlib/unsat/*.smt2
do
  echo -n "Testing $f ..."
  if ! res=$(${RUNNER} $f 2> /dev/null); then
    echo "The solver did not exit correctly"
    error=true
  else
    echo " $res"
    if [ "$res" != "unsat" ]; then error=true; echo "ERROR !!!"; fi
  fi
done

if $error; then 
  echo "There were errors!"
  exit 1
fi

echo "All tests successful"
exit 0
