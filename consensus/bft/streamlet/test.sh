#!/bin/bash

# USAGE: ./test libfilename

if test -z "${LIBDIRS}" ; then
    echo "set LIBDIRS for Scheme"
    exit 1
fi

if test -z "${1}" ; then
    echo "specify a library file name in src/test/scheme, without suffix"
    exit 1
elif test ! -e "src/test/scheme/${1}.ss" ; then
    echo "library file not found: src/test/scheme/${1}.ss"
    echo "specify a library file name in src/test/scheme, without suffix"
    exit 1
fi

echo "(reset-handler abort) (import (${1})) (run-tests)" | scheme -q --libdirs .:src/main/scheme:src/test/scheme:../../..:"${LIBDIRS}"
