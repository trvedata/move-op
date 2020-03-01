#!/bin/bash

echo  ",,us_west_1,,,,,,,ap_southeast_1" > leader_mode.csv
echo -n "interval,total ops/sec," >> leader_mode.csv
echo -n "generated ops/sec,RTT min,RTT median,RTT p95,apply min,apply median,apply p95," >> leader_mode.csv
echo    "generated ops/sec,RTT min,RTT median,RTT p95,apply min,apply median,apply p95" >> leader_mode.csv

for interval in 100000 50000 20000 10000 5000 2000 1000 500 200 100 50 20 10; do
    eu_times="$(cat logs-leader/interval_${interval}_eu_west_1.log.gz      | gunzip | awk -f leader_mode.awk | tail -n 2 | head -n 1 | tr '\n' ',')"
    ap_times="$(cat logs-leader/interval_${interval}_ap_southeast_1.log.gz | gunzip | awk -f leader_mode.awk | tail -n 2 | head -n 1 | tr -d '\n')"
    echo "${interval},${eu_times}${ap_times#*,}" >> leader_mode.csv
done
