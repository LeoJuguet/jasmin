#! /usr/bin/env sh

filename=$(basename $1)

./jasa.exe -config config_jazz.json $1 -hook logs -debug _ | tee "output_${filename%.*}"
