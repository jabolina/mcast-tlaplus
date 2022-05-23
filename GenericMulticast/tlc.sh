#!/usr/bin/sh

set -e


java -Dfile.encoding=UTF-8 -classpath $PWD/../tla2tools.jar \
  -DTLA-Library=../AtomicBroadcast \
  tlc2.TLC -tool -modelcheck -coverage 1 /home/jab/git/mcast-tlaplus/GenericMulticast/GenericMulticast.tla