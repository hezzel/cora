#!/bin/bash
#yices-smt2 $1 --timeout 1 > $2
z3 $1 > $2
