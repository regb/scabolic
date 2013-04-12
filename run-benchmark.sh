TIMEFORMAT=%R
TIMEOUT=30
echo "#Benchmarking regolic"
echo "Timeout is set to ${TIMEOUT}s and results are in seconds"
for benchmarks in satlib/*; do
  echo "##Benchmarking $benchmarks"
  sum=0
  nbsuccess=0
  nbfailure=0
  for benchmark in $benchmarks/*.cnf; do
    echo -n "$benchmark ... "
    TIMERES=$(./regolic sat --timeout=${TIMEOUT} --time $benchmark | tail -n 1)
    status=$?
    if [ $status -eq 124 ]; then
      echo "Timeout"
      nbfailure=$((nbfailure + 1))
    elif [ $status -eq 0 ]; then
      echo $TIMERES
      nbsuccess=$((nbsuccess + 1))
      sum=$(echo "$sum + $TIMERES" | bc)
    else
      echo "ERROR !!!"
      nbfailure=$((nbfailure + 1))
    fi
  done
  echo "###Number of failure: $nbfailure"
  if [ $nbsuccess -eq 0 ]; then
    echo "###No benchmark completed"
  else
    echo "###Number of success: $nbsuccess"
    echo "###Average time over success: $(echo "scale=3;$sum / $nbsuccess" | bc)"
    echo "###Total average time: $(echo "scale=3;($sum + ($nbfailure * $TIMEOUT)) / ($nbsuccess + $nbfailure)" | bc)"
  fi
done
