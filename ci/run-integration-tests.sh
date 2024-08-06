#!/bin/bash
set -e

CURRENT_DIR=$(dirname "$(readlink -f "$0")")
pushd $CURRENT_DIR/..
docker run --rm -v $(pwd):/home/ubuntu/smt-dafny-compiler/ smt-dafny-compiler:latest /usr/bin/bash -c "(cd \$SDC_SRC_DIR && ./ci/publish-self-contained.sh && lit -vv integration-tests)"
popd