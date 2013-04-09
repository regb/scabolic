MASTER="dabd406b" #MASTER contains the needed files for running benchmarks, not necessarly master branch
COMMITS="dabd406b"
RESULTS_DIR="results"

if [ ! -d $RESULTS_DIR ]; then mkdir $RESULTS_DIR; fi
for commit in $COMMITS; do

  git checkout $commit
  git checkout $MASTER run-benchmarks.sh
  git checkout $MASTER src/main/scala/regolic/Main.scala
  sbt compile
  ./run-benchmarks.sh > $RESULTS_DIR/$commit
  git reset HEAD run-benchmarks.sh
  git checkout run-benchmarks.sh
  git reset HEAD src/main/scala/regolic/Main.scala
  git checkout src/main/scala/regolic/Main.scala

done

git checkout master
