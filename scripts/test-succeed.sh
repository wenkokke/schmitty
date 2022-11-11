#!/bin/sh

fail="$(mktemp)"

TESTS=$(find . -type f -and -path './test/Succeed/*.agda')
set -- "$@" $TESTS

# Check each test file:
for TEST; do
  echo "Checking $TEST"
  agda -v0 -isrc -itest/Succeed "$TEST" || echo > "$fail"
done

# Check whether or not any subcommand failed:
if [ -s "$fail" ]; then
    rm "$fail"
    exit 1
else
    rm "$fail"
    exit 0
fi
