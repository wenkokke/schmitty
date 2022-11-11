#!/bin/sh

fail="$(mktemp)"

TESTS=$(find . -type f -and -path './test/Fail/*.agda')
set -- "$@" $TESTS

# Check each test file:
for TEST; do
  echo "Checking $TEST"
  GOLDEN=$(echo "$TEST" | sed -e 's/\.agda/.err/')
  agda -v0 -isrc -itest/Fail "$TEST" \
    | tail -n +2 \
	  | diff --suppress-common-lines "$GOLDEN" -
done

# Check whether or not any subcommand failed:
if [ -s "$fail" ]; then
    rm "$fail"
    exit 1
else
    rm "$fail"
    exit 0
fi
