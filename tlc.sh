#!/usr/bin/sh

set -e
set -o xtrace

dependencies=$(cat $1/dependencies.txt | while read line; do echo -n "$ROOT_FOLDER/$line:" ; done)

java -cp "$ROOT_FOLDER"/tla2tools.jar -XX:+UseParallelGC \
  -DTLA-Library="$dependencies" tlc2.TLC "$1/$2" \
  -tool -modelcheck -cleanup -workers auto -config "$1/$3"
