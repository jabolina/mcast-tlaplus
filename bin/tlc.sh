#!/usr/bin/sh

set -eo xtrace

# The other modules we depend to work. This will be loaded as libraries.
dependencies=$(while read -r line; do echo -n "$ROOT_FOLDER/$line:" ; done < "$1/dependencies.txt")

# We have the folder, so now we find the specification file.
# The folder must contain only a single file with the `.tla` extension.
if [[ $(find "$1/$2" -type f -name "*.tla" | wc -l) != 1 ]] ; then
  echo "More than one specification file. Exiting"
  exit 1
fi
spec_file=$(find "$1/$2" -type f -name "*.tla")

# We execute the specification with all the available configuration files.
for configuration in "$1"/"$2"/* ; do \
  if [[ $(echo -n "$configuration") == *".cfg" ]]; then \
    java -cp "$ROOT_FOLDER"/bin/tla2tools.jar -XX:+UseParallelGC \
      -DTLA-Library="$dependencies" tlc2.TLC "$spec_file" \
      -modelcheck -cleanup -workers auto -noGenerateSpecTE -config "$configuration"
  fi ;
done
