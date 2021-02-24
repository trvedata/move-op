/^ReplicaThread.local/,/95%/ {
    if ($1 == "1-minute") local_rate = $4
    if ($1 == "min") local_min = $3
    if ($1 == "median") local_median = $3
    if ($1 == "95%") local_p95 = $3
}

/^ReplicaThread.remote/,/95%/ {
    if ($1 == "min") remote_min = $3
    if ($1 == "median") remote_median = $3
    if ($1 == "95%") print local_rate "," local_min "," local_median "," local_p95 "," remote_min "," remote_median "," $3
}
