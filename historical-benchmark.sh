MASTER="master"
COMMITS="master"
RESULTS_DIR="results"

if [ ! -d $RESULTS_DIR ]; then mkdir $RESULTS_DIR; fi
for commit in $COMMITS; do

  git checkout $commit
  git checkout $MASTER run-benchmarks.sh
  git checkout $MASTER src/main/scala/regolic/Main.scala
  sbt compile
  ./run-benchmarks.sh > $RESULTS_DIR/$commit

done
