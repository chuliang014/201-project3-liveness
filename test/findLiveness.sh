#!/bin/bash
rm -rf Test.out Test2.out
cd ../Pass/build/
cmake -DCMAKE_BUILD_TYPE=Release ../Transforms/LivenessAnalysis
make -j4
cd -
echo "-----------Start------------------"
opt -load ../Pass/build/libLivenessAnalysis.so  -Liveness < 1.ll > /dev/null
echo "-----------End--------------------"
echo "-----------Start------------------"
opt -load ../Pass/build/libLivenessAnalysis.so  -Liveness < 2.ll > /dev/null
echo "-----------End--------------------"
