#!/bin/sh

error=false

echo "Running SAT solver on satisfiable instances ..."
for f in regression/dimacs/sat/*.cnf
do
  echo -n "Testing $f ..."
  if ! res=$(./regolic --dimacs $f 2> /dev/null); then
    echo "The solver did not exit correctly"
    error=true
  else
    echo " $res"
    if [ "$res" != "sat" ]; then error=true; echo "ERROR !!!"; fi
  fi
done

echo "Running SAT solver on unsatisfiable instances ..."
for f in regression/dimacs/unsat/*.cnf
do
  echo -n "Testing $f ..."
  if ! res=$(./regolic --dimacs $f 2> /dev/null); then
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
