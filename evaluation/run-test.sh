#!/bin/bash
set -e

# This script executes on an EC2 VM. It runs a replica that generates
# operations with a given inter-operation interval.

INTERVAL="${1?Please specify interval}"
REPLICA_ID="${2?Please specify replica ID}"
REMOTE1="${3?Please specify remote IP 1}"
REMOTE2="${4?Please specify remote IP 2}"
LOGFILE="data/logs/interval_$INTERVAL.log"

cd "$(dirname "$0")"

sed -i "s/\\(val OPERATION_INTERVAL =.*\\)([0-9]*)/\\1($INTERVAL)/" src/main/scala/TestReplica.scala

mkdir -p data/logs

if [ -f "$LOGFILE" ]; then
    echo "log file already exists"
    exit 1
fi

sbt "runMain TestReplica $REPLICA_ID $REMOTE1 $REMOTE2" | tee "$LOGFILE"
