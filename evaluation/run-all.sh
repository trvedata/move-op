#!/bin/bash
set -e

US_WEST_1=18.144.1.184
EU_WEST_1=34.255.190.108
AP_SOUTHEAST_1=18.140.64.126

run_batch () {
    INTERVAL=$1

    ssh -i ~/.ec2/martin-aws-us-west-1.pem ubuntu@$US_WEST_1 /home/ubuntu/move-op/evaluation/run-test.sh $INTERVAL 1 $EU_WEST_1 $AP_SOUTHEAST_1 &
    PROC1=$!
    ssh -i ~/.ec2/martin-aws-eu-west-1.pem ubuntu@$EU_WEST_1 /home/ubuntu/move-op/evaluation/run-test.sh $INTERVAL 2 $US_WEST_1 $AP_SOUTHEAST_1 &
    PROC2=$!
    ssh -i ~/.ec2/martin-aws-ap-southeast-1.pem ubuntu@$AP_SOUTHEAST_1 /home/ubuntu/move-op/evaluation/run-test.sh $INTERVAL 3 $US_WEST_1 $EU_WEST_1 &
    PROC3=$!

    wait $PROC1
    wait $PROC2
    wait $PROC3
}

run_batch 100
