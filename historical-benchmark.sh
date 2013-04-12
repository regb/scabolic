MASTER="16cc4717" #MASTER contains the needed files for running benchmarks, not necessarly master branch
COMMITS="d43db7f3 e2294b10 94372963 391b6440"
RESULTS_DIR="results"

RUNNER=run-benchmark.sh
MAIN=src/main/scala/regolic/Main.scala
SETTINGS=src/main/scala/regolic/Settings.scala

if [ ! -d $RESULTS_DIR ]; then mkdir $RESULTS_DIR; fi
for commit in $COMMITS; do

  rm regolic
  git checkout $commit
  git checkout $MASTER $RUNNER
  git checkout $MASTER $MAIN
  git checkout $MASTER $SETTINGS
  sbt compile
  sbt script
  ./$RUNNER > $RESULTS_DIR/$commit
  git reset HEAD $RUNNER
  git checkout $RUNNER
  git reset HEAD $MAIN
  git checkout $MAIN
  git reset HEAD $SETTINGS
  git checkout $SETTINGS

done

git checkout master
