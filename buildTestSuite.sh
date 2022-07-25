#!/bin/bash

# Temp directory for intermediate files
mkdir tmp

# Build test suite
# echo "Building test suite ..."
# ghc -o testsuite -odir ./tmp -hidir ./tmp --make ./Tests/TestSuite.hs

# Build profiler
# echo "Building profiler ..."
# ghc -o profiler -odir ./tmp -hidir ./tmp --make ./Tests/Profiler.hs

# ghc -prof -auto-all -rtsopts=all -osuf po -o profiler -odir ./tmp -hidir ./tmp --make ./Tests/Profiler.hs

# Build example gui tools
echo "Building examples ..."
ghc -o ml -odir ./tmp -hidir ./tmp --make ./Examples/GuiTool/MiniML.hs
ghc -o fj -odir ./tmp -hidir ./tmp --make ./Examples/GuiTool/FJ.hs

# remove intermediate files
rm -rf ./tmp
