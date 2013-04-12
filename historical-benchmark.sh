MASTER="16cc4717" #MASTER contains the needed files for running benchmarks, not necessarly master branch
COMMITS="d947f11c2 66e5517 d43db7f3 e2294b10 94372963 391b6440"
RESULTS_DIR="results"

RUNNER=run-benchmark.sh
SRC=src/main/scala/regolic/Main.scala src/main/scala/regolic/Settings.scala

if [ ! -d $RESULTS_DIR ]; then mkdir $RESULTS_DIR; fi
for commit in $COMMITS; do

  git checkout $commit
  git checkout $MASTER $RUNNER
  git checkout $MASTER $SRC
  sbt compile
  ./$RUNNER > $RESULTS_DIR/$commit
  git reset HEAD $RUNNER
  git checkout $RUNNER
  git reset HEAD $SRC
  git checkout $SRC

done

git checkout master
