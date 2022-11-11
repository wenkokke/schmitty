#!/bin/sh

SOURCES=$(find . -type f -and -path './src/**/*.agda')
set -- "$@" $SOURCES

echo "{-# OPTIONS --guardedness #-}"
echo
echo "module index where"
echo
for SOURCE; do
  MODULE=$(echo "$SOURCE" | sed -e 's/^.\/src\///' | sed -e 's/\.agda$//' | sed -e 's/\//\./g')
  echo "import $MODULE"
done
