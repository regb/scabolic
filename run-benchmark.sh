for benchmarks in satlib/*; do
  echo "=== Benchmarking $benchmarks ==="
  timeout 5m ./regolic satlib $benchmarks
done
