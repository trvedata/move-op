/^ClientThread.*requests/,/95%/ {
    if ($1 == "1-minute") request_rate = $4
    if ($1 == "min") rtt_min = $3
    if ($1 == "median") rtt_median = $3
    if ($1 == "95%") rtt_p95 = $3
}

/^ReplicaThread.remote/,/95%/ {
    if ($1 == "1-minute") total_rate = $4
    if ($1 == "95%") print total_rate "," request_rate "," rtt_min "," rtt_median "," rtt_p95
}
