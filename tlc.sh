#!/usr/bin/sh

set -e
set -o xtrace

dependencies=$(cat $1/dependencies.txt | while read line; do echo -n "$ROOT_FOLDER/$line:" ; done)
java -XX:+UseParallelGC -Dfile.encoding=UTF-8 -classpath "$ROOT_FOLDER"/tla2tools.jar \
  -DTLA-Library="$dependencies" \
  tlc2.TLC -tool -modelcheck -cleanup "$1/$2"
