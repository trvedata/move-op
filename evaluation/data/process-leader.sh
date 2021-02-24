#!/bin/bash
set -euo pipefail

LOGDIR="${1?Please specify directory containing log files}"

# Processes the log files produced by runs of the experiment in leader mode
# (state machine replication, USE_LEADER = true), and extracts the numbers
# we're interested in, in a format ready for Gnuplot. The output file contains
# the following columns:
#
#  1. Interval between generated ops (microseconds)
#  2. Operations/sec processed by all replicas
#  3. Requests/sec made by eu-west-1 replica to the leader (us-west-1)
#  4. Minimum    round trip time from eu-west-1 to the leader (microseconds)
#  5. Median     round trip time from eu-west-1 to the leader (microseconds)
#  6. 95th perc. round trip time from eu-west-1 to the leader (microseconds)
#  7. Requests/sec made by ap-southeast-1 replica to the leader (us-west-1)
#  8. Minimum    round trip time from ap-southeast-1 to the leader (microseconds)
#  9. Median     round trip time from ap-southeast-1 to the leader (microseconds)
# 10. 95th perc. round trip time from ap-southeast-1 to the leader (microseconds)

rm -f "$LOGDIR/summary.data"

for interval in $(ls "$LOGDIR"/*.log.gz | sed -e 's/.*interval_//' -e 's/_.*//' | uniq | sort -rn); do
    eu_times="$(cat "${LOGDIR}/interval_${interval}_eu_west_1.log.gz"      | gunzip | awk -f process-leader.awk | tail -n 2 | head -n 1 | tr '\n' ',')"
    ap_times="$(cat "${LOGDIR}/interval_${interval}_ap_southeast_1.log.gz" | gunzip | awk -f process-leader.awk | tail -n 2 | head -n 1 | tr '\n' ',')"
    echo "${interval},${eu_times}${ap_times#*,}" | tr ',' '\t' >> "$LOGDIR/summary.data"
done
