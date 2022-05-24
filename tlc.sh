#!/usr/bin/sh

set -e

echo "TLC verifying $1/$2"

dependencies=$(cat $1/dependencies.txt | while read line; do echo "$ROOT_FOLDER/$line" ; done)

echo "TLC dependencies: $dependencies"

java -XX:+UseParallelGC -Dfile.encoding=UTF-8 -classpath "$ROOT_FOLDER"/tla2tools.jar \
  -DTLA-Library="$dependencies" \
  tlc2.TLC -tool -modelcheck -cleanup "$1/$2"
