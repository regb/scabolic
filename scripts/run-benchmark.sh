TIMEFORMAT=%R
TIMEOUT=20
echo "#Benchmarking scabolic"
echo "Timeout is set to ${TIMEOUT}s and results are in seconds"
for benchmarks in $@; do
  echo "##Benchmarking $benchmarks"
  ./scabolic satlib --timeout=${TIMEOUT} --time $benchmarks
done
