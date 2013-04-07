for benchmarks in satlib/*; do
  echo "=== Benchmarking $benchmarks ==="
  if ! timeout 30m ./regolic satlib $benchmarks; then
    echo -e "\nTotal: Timeout > 30m"
  fi
done
