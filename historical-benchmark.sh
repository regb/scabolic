MASTER="d1a05bc2" #MASTER contains the needed files for running benchmarks, not necessarly master branch
COMMITS="d1a05bc2"
RESULTS_DIR="results"

if [ ! -d $RESULTS_DIR ]; then mkdir $RESULTS_DIR; fi
for commit in $COMMITS; do

  git checkout $commit
  git checkout $MASTER run-benchmarks.sh
  git checkout $MASTER src/main/scala/regolic/Main.scala
  sbt compile
  ./run-benchmarks.sh > $RESULTS_DIR/$commit

done

git checkout master
