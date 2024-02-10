#!/bin/bash
# Terminal colors
BLUE='\033[1;34m'
PURPLE='\033[1;35m'
RED='\033[1;31m'
GREEN='\033[1;32m'
NC='\033[0m'

EXP_PATH="./benchmarks"

FILE_COUNTER=0

# Run paper experiments
echo "Running paper experiments..."

echo "Running experiments from ESOP2024..."
FILES="$EXP_PATH/esop2024/*"

for f in $FILES
do
    printf "${PURPLE}Experiment number $((FILE_COUNTER + 1))...${NC}\n"
    printf "${BLUE}Invoking cora on file $f ${NC}\n"
    ./bin/app "$f"
    printf "${GREEN}Done.${NC}\n\n"
    FILE_COUNTER=$((FILE_COUNTER+1))
done

rm -rf result
rm -rf problem.smt2

# Run extra experiments
echo "Running experiments from IJCAR2024..."
FILES="$EXP_PATH/ijcar2024/*"
for f in $FILES
do
    printf "${PURPLE}Experiment number $FILE_COUNTER...${NC}\n"
    printf "${BLUE}Invoking cora on file $f ${NC}\n"
    ./bin/app "$f"
    printf "${GREEN}Done.${NC}\n\n"
    FILE_COUNTER=$((FILE_COUNTER+1))
done

rm -rf result
rm -rf problem.smt2

echo "Running experiments from TPDB_ITRS..."
FILES="$EXP_PATH/tpdb_itrs/*"
for f in $FILES
do
    printf "${PURPLE}Experiment number $FILE_COUNTER...${NC}\n"
    printf "${BLUE}Invoking cora on file $f ${NC}\n"
    ./bin/app "$f"
    printf "${GREEN}Done.${NC}\n\n"
    FILE_COUNTER=$((FILE_COUNTER+1))
done

rm -rf result
rm -rf problem.smt2

echo "Running extra experiments..."
FILES="$EXP_PATH/extra/*"
for f in $FILES
do
    printf "${PURPLE}Experiment number $FILE_COUNTER...${NC}\n"
    printf "${BLUE}Invoking cora on file $f ${NC}\n"
    ./bin/app "$f"
    printf "${GREEN}Done.${NC}\n\n"
    FILE_COUNTER=$((FILE_COUNTER+1))
done

rm -rf result
rm -rf problem.smt2
