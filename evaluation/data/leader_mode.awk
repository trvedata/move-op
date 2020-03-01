BEGIN {
    print "apply ops/sec,generate ops/sec,RTT min,RTT median,RTT p95,apply min,apply median,apply p95"
}

/^ClientThread/,/95%/ {
    if ($1 == "1-minute") gen_rate = $4
    if ($1 == "min") rtt_min = $3
    if ($1 == "median") rtt_median = $3
    if ($1 == "95%") rtt_p95 = $3
}

/^ReplicaThread.remote/,/95%/ {
    if ($1 == "1-minute") apply_rate = $4
    if ($1 == "min") apply_min = $3
    if ($1 == "median") apply_median = $3
    if ($1 == "95%") print apply_rate "," gen_rate "," rtt_min "," rtt_median "," rtt_p95 "," apply_min "," apply_median "," $3
}
