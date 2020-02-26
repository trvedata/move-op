#!/bin/bash

echo ",,us_west_1,,,,,,,eu_west_1,,,,,,,ap_southeast_1" >> processing_times.csv
echo -n "interval,ops/sec," >> processing_times.csv
echo -n "local min,local median,local p95,remote min,remote median,remote p95," >> processing_times.csv
echo -n "local min,local median,local p95,remote min,remote median,remote p95," >> processing_times.csv
echo    "local min,local median,local p95,remote min,remote median,remote p95"  >> processing_times.csv

for interval in 100000 50000 20000 14000 10000 7000 6000 5000 2000; do
    us_times="$(cat logs/interval_${interval}_us_west_1.log.gz      | gunzip | awk -f processing_times.awk | tail -n 2 | head -n 1 | tr '\n' ',')"
    eu_times="$(cat logs/interval_${interval}_eu_west_1.log.gz      | gunzip | awk -f processing_times.awk | tail -n 2 | head -n 1 | tr '\n' ',')"
    ap_times="$(cat logs/interval_${interval}_ap_southeast_1.log.gz | gunzip | awk -f processing_times.awk | tail -n 2 | head -n 1 | tr '\n' ',')"
    op_rate="$(echo "${us_times%%,*} + ${eu_times%%,*} + ${ap_times%%,*}" | bc)"
    echo "${interval},${op_rate},${us_times#*,}${eu_times#*,}${ap_times#*,}" >> processing_times.csv
done
