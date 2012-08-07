#!/bin/sh

echo "Running SAT solver on satisfiable instances ..."
for f in regression/dimacs/sat/*.cnf
do
  echo -n "Testing $f ..."
  res=`./regolic --dimacs $f`
  echo " $res"
  if [ $res != "sat" ]; then echo "ERROR !!!"; fi
done

echo "Running SAT solver on unsatisfiable instances ..."
for f in regression/dimacs/unsat/*.cnf
do
  echo -n "Testing $f ..."
  res=`./regolic --dimacs $f`
  echo " $res"
  if [ $res != "unsat" ]; then echo "ERROR !!!"; fi
done
