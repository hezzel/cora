#!/bin/bash
EXP_PATH="./benchmarks"

FILE_COUNTER=0

# Run paper experiments
echo "Running paper experiments..."

FILES="$EXP_PATH/esop2024/*"

for f in $FILES
do
    echo "Paper experiment $FILE_COUNTER..."
    ./bin/app "$f"
    echo "Done."
    FILE_COUNTER=$((FILE_COUNTER+1))
done
FILE_COUNTER=0

rm -rf result
rm -rf problem.smt2

# Run extra experiments
FILES="$EXP_PATH/ijcar2024/*"
for f in $FILES
do
    echo "Extra experiment $FILE_COUNTER..."
    ./bin/app "$f"
    echo "Done."
    FILE_COUNTER=$((FILE_COUNTER+1))
done

rm -rf result
rm -rf problem.smt2

# Run extra experiments
FILES="$EXP_PATH/tpdb_itrs/*"
for f in $FILES
do
    echo "Extra experiment $FILE_COUNTER..."
    ./bin/app "$f"
    echo "Done."
    FILE_COUNTER=$((FILE_COUNTER+1))
done

rm -rf result
rm -rf problem.smt2

# Run extra experiments
FILES="$EXP_PATH/extra/*"
for f in $FILES
do
    echo "Extra experiment $FILE_COUNTER..."
    ./bin/app "$f"
    echo "Done."
    FILE_COUNTER=$((FILE_COUNTER+1))
done

rm -rf result
rm -rf problem.smt2
