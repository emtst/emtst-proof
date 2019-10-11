#!/bin/bash

echo 'installing opam (and your password will be required.)'
sudo ./getopam.sh || { echo 'failed to install opam.' ; exit 1; }

echo 'configure opam.'
opam init -y && eval $(opam config env) \
    && opam repo add coq-released https://coq.inria.fr/opam/released \
    || { echo 'failed to initialise opam and the Coq repo.' ; exit 1; }

echo 'install coq and ssreflect.'
opam install -y coq.8.9.0 \
    && opam install -y coq-mathcomp-ssreflect.1.7.0 \
    || { echo 'failed to initialise opam and the Coq repo.' ; exit 1; }
