#!/bin/sh

if [ $# -eq 0 ]; then
    ./gradlew run
else
    ./gradlew run --args="$*"
fi
