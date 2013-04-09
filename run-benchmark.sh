TIMEFORMAT=%R
TIMEOUT=5m
echo "#Benchmarking regolic"
echo "Timeout is set to 5m and results are in seconds"
for benchmarks in satlib/*; do
  echo "##Benchmarking $benchmarks"
  sum=0
  nbsuccess=0
  nbtimeout=0
  for benchmark in $benchmarks/*.cnf; do
    echo -n "$benchmark ... "
    TIMERES=$( (time timeout $TIMEOUT ./regolic sat $benchmark > /dev/null) 2>&1)
    if [ $? -eq 124 ]; then
      echo "Timeout"
      nbtimeout=$((nbtimeout + 1))
    else
      echo $TIMERES
      nbsuccess=$((nbsuccess + 1))
      sum=$(echo "$sum + $TIMERES" | bc)
    fi
  done
  echo "###Number of timeouts: $nbtimeout"
  if [ $nbsuccess -eq 0 ]; then
    echo "###No benchmark completed"
  else
    echo "###Number of success: $nbsuccess"
    echo "###Average time over success: $(echo "scale=3;$sum / $nbsuccess" | bc)"
  fi
done
