#!/bin/bash
set -e

CURRENT_DIR=$(dirname "$(readlink -f "$0")")

pushd $CURRENT_DIR/../src/
dotnet publish -c Debug --self-contained -r linux-x64 -p:PublishReadyToRun=true
dotnet publish -c Release --self-contained -r linux-x64 -p:PublishReadyToRun=true
popd