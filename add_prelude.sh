#!/bin/sh
for arg do 
echo "open Basis\
" | cat - $arg > temp && 
mv temp $arg
done
