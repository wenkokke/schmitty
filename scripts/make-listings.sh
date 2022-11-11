#!/bin/sh

# See: https://stackoverflow.com/a/4774063
ROOT_DIR="$(dirname "$( cd -- "$(dirname "$0")" >/dev/null 2>&1 || exit ; pwd -P )" )"

# Update "index.agda"
(cd "$ROOT_DIR" && ./scripts/make-index.sh > "index.agda")

# Compile listings
agda -v0 -i"$ROOT_DIR" -i"$ROOT_DIR/src" "$ROOT_DIR/index.agda" --html --html-dir=docs
