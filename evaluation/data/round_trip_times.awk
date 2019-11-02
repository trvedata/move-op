BEGIN {
    first_line = 1
}

/^-- Timers ---/ {
    first_ip = ""
    second_ip = ""
}

match($0, /^ClientThread\((.*)\)\.requests/, matches) {
    if (first_ip == "") first_ip = matches[1]; else second_ip = matches[1];
    if (second_ip != "" && first_line) {
        print first_ip "," second_ip
        first_line = 0
    }
}

/^ClientThread\(.*\)\.requests/,/median/ {
    if ($1 == "median") {
        if (second_ip == "") {
            first_time = $3
        } else {
            print first_time "," $3
        }
    }
}
