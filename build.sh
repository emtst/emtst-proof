#!/bin/bash

REPO_DIR="$(dirname "$0")"
REPO_DIR_ABS="$(realpath "$REPO_DIR")"

function go_home {
    cd $REPO_DIR_ABS #switch to the repo's directory
}

## Just in case update opam env
eval $(opam config env)

## Build the finmap library
go_home

cd ext/finmap && ./generateMakefile && make

## Build the proof

go_home

./generateMakefile && make
