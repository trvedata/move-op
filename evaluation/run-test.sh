#!/bin/bash
set -eo pipefail

# This script executes on an EC2 VM. It runs a replica that generates
# operations with a given inter-operation interval.

INTERVAL="${1?Please specify interval}"
USE_LEADER="${2?Please specify whether to use leader}"
USE_GENERATED_CODE="${3?Please specify whether to use generated code}"
REPLICA_ID="${4?Please specify replica ID}"
REMOTE1="$5"
REMOTE2="$6"

if [ "$USE_LEADER" = "true" ]; then
    LOGDIR="data/logs-leader"
else
    LOGDIR="data/logs"
fi

LOGFILE="$LOGDIR/interval_$INTERVAL.log"

cd "$(dirname "$0")"

sed -i~ -e "s/\\(val OPERATION_INTERVAL =.*\\)([0-9]*)/\\1($INTERVAL)/" \
    -e "s/\\(val USE_LEADER = \\).*/\\1$USE_LEADER/" \
    -e "s/\\(val USE_GENERATED_CODE = \\).*/\\1$USE_GENERATED_CODE/" \
    src/main/scala/TestReplica.scala

mkdir -p "$LOGDIR"

if [ -f "$LOGFILE" ]; then
    echo "log file already exists"
    exit 1
fi

sbt --mem 3072 "runMain TestReplica $REPLICA_ID $REMOTE1 $REMOTE2" 2>&1 | tee "$LOGFILE"
