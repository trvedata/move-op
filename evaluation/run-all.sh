#!/bin/bash
set -e

# To run the experiments, log in to the AWS EC2 console and start up a c5.large
# instance running Ubuntu 18.04 in each of the three regions us-west-1, eu-west-1,
# and ap-southeast-1. Then fill in their IP addresses here:
US_WEST_1=18.144.1.184
EU_WEST_1=34.255.190.108
AP_SOUTHEAST_1=18.140.64.126

# Set up the security groups such that you can log in to the VMs by SSH (TCP port 22),
# and that they can all connect to each other on TCP port 8080.
# Then, to set up the VMs, log in to each by SSH and run the following:

# sudo apt-get update && sudo apt-get upgrade -y && sudo apt-get install -y apt-transport-https gnupg wget unzip
# echo "deb https://dl.bintray.com/sbt/debian /" | sudo tee -a /etc/apt/sources.list.d/sbt.list
# sudo apt-key adv --keyserver hkp://keyserver.ubuntu.com:80 --recv 2EE0EA64E40A89B84B2DF73499E82A75642AC823
# sudo apt-get update && sudo apt-get install -y openjdk-8-jdk-headless sbt
# git clone https://github.com/trvedata/move-op.git && cd move-op/evaluation && sbt compile

run_batch () {
    INTERVAL=$1

    ssh -i ~/.ec2/martin-aws-us-west-1.pem ubuntu@$US_WEST_1 /home/ubuntu/move-op/evaluation/run-test.sh $INTERVAL 1 $EU_WEST_1 $AP_SOUTHEAST_1 &
    ssh -i ~/.ec2/martin-aws-eu-west-1.pem ubuntu@$EU_WEST_1 /home/ubuntu/move-op/evaluation/run-test.sh $INTERVAL 2 $US_WEST_1 $AP_SOUTHEAST_1 &
    ssh -i ~/.ec2/martin-aws-ap-southeast-1.pem ubuntu@$AP_SOUTHEAST_1 /home/ubuntu/move-op/evaluation/run-test.sh $INTERVAL 3 $US_WEST_1 $EU_WEST_1 &
    wait

    scp -i ~/.ec2/martin-aws-us-west-1.pem ubuntu@$US_WEST_1:/home/ubuntu/move-op/evaluation/data/logs/interval_$INTERVAL.log data/logs/interval_${INTERVAL}_us_west_1.log
    scp -i ~/.ec2/martin-aws-eu-west-1.pem ubuntu@$EU_WEST_1:/home/ubuntu/move-op/evaluation/data/logs/interval_$INTERVAL.log data/logs/interval_${INTERVAL}_eu_west_1.log
    scp -i ~/.ec2/martin-aws-ap-southeast-1.pem ubuntu@$AP_SOUTHEAST_1:/home/ubuntu/move-op/evaluation/data/logs/interval_$INTERVAL.log data/logs/interval_${INTERVAL}_ap_southeast_1.log

    gzip data/logs/interval_${INTERVAL}_us_west_1.log data/logs/interval_${INTERVAL}_eu_west_1.log data/logs/interval_${INTERVAL}_ap_southeast_1.log
}

cd "$(dirname "$0")"
mkdir -p data/logs
run_batch 14
