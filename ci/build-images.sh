#!/bin/bash
set -e

CURRENT_DIR=$(dirname "$(readlink -f "$0")")

pushd $CURRENT_DIR/..
git submodule update --init --recursive

pushd external/SLOT
docker build -t smt-dafny-compiler-slot:latest .
popd

docker build --file $CURRENT_DIR/Dockerfile --build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g) -t smt-dafny-compiler:latest .
popd