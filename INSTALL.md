
# Build world: opam

_NB: you may need to add `sudo` everywhere_

## Install CompCertBin
```shell
# download source code to `YOUR_COMPCERT_DIR` and rename the unzip folder to `compcert` (it is very important!!!)
cd YOUR_COMPCERT_DIR/
# unzip

# rename the directory
mv CompCert compcert
cd compcert

# install coq-flocq.4.1.0
opam install coq-flocq.4.1.0
# install 32-bit compcert
./configure arm-linux -use-external-Flocq -clightgen
make all
make clightgen

# set COQPATH
# Important: if you recompile CompCert again, remember to comment COQPATH firstly!!!
vim /home/YOUR/.bashrc
# adding the line `export COQPATH="YOUR_COMPCERT_DIR"`
source /home/YOUR/.bashrc
```
## Install dx

```shell
# install dx:
git clone https://gitlab.univ-lille.fr/samuel.hym/dx.git
cd dx
make clean
./configure --cprinterdir="$(opam var lib)/dx" --compcertdir=YOUR_COMPCERT_DIR/compcert --install-compcert-printer
make install all
```
