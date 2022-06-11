#!/usr/bin/sh

set -eo xtrace

find "$PWD" -type d -name 'states' -exec rm -rf $(printf '%s\n' '{}' +);
