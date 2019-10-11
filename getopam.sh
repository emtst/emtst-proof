#!/bin/bash

echo 'Update'
apt-get -y update && apt-get -y upgrade || { echo 'apt update failed' ; exit 1; }

echo 'Install opam 2.0 and m4'
apt-get -y install m4 && add-apt-repository -y ppa:avsm/ppa && \
apt-get -y install opam || { echo 'installing opam failed' ; exit 1; }
