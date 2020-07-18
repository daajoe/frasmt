# FraSMT (SMT-based decomposer for fractional hypertree decompositions)

## Download:
```bash
git clone --recurse-submodules  git@github.com:daajoe/frasmt.git
````

## Hypergraphs

### Fischl (hyperbench collection)
See: https://github.com/daajoe/hypergraphs or http://hyperbench.dbai.tuwien.ac.at/


## External Requirements (conda)
### Get Anaconda
https://www.anaconda.com/download/#macos

### Remark
Conda is a little memory hungry. So you want to give your system at least 1G memory.
If installation quits just quits, run with --verbose option.
In case you run into "CondaMemoryError does not take keyword arguments", then you
really want to increase available memory to conda.

### Setup Environment
```bash
conda update -n base conda
conda env create -f environment.yml  --name fhtd #(meanwhile get a yourself coffee; or two)
```
### Active Environment
```bash
source activate fhtd
```

### SMT solver (non-linux)
Unfortunately, anaconda packages for z3 are quite outdated (we need the optimization API from z3). 
I put together an experimental anaconda package (https://anaconda.org/daajoe/z3_experimental), but do not maintain this one at the moment. Should work, but only for linux. Otherwise see below.

#### Z3
https://github.com/Z3Prover/z3

with python support

python scripts/mk_make.py --prefix=/home/USERNAME/miniconda2 --python --pypkgdir=/home/USERNAME/miniconda2/lib/python-2.7/site-packages
cd build
make -j4
make install

## External Requirements (not using conda)
We highly recommend to use conda!!

#### pysmt (optional)
pysmt optimization open PR: https://github.com/pysmt/pysmt/pull/439

#### clingo
- conda: https://conda.io/docs/user-guide/tasks/manage-pkgs.html
- https://anaconda.org/potassco/clingo

#### cplex
https://www.ibm.com/support/knowledgecenter/es/SSSA5P_12.6.1/ilog.odms.studio.help/Optimization_Studio/topics/COS_installing.html
https://www.ibm.com/support/knowledgecenter/SSSA5P_12.7.0/ilog.odms.cplex.help/CPLEX/GettingStarted/topics/set_up/Python_setup.html

- Install Anaconda cplex from https://anaconda.org/IBMDecisionOptimization/cplex
- Download cplex (IBM Academic Initative)
  - Install it into your home (/home/myhome/cplex_1210)
  - Install python into local site packages somewhere (not into anaconda directory; https://or.stackexchange.com/questions/3114/python-does-not-identify-the-academic-version-of-cplex)
  - cp ~/cplex_1210/cplex/python/3.7/x86-64_linux/cplex/_internal/py37_cplex12100.so ~/anaconda3/envs/rb/lib/python3.7/site-packages/cplex/_internal/py37_cplex12100.so

## Test it
```bash
bin/fhtd -f tests/graphs/easy/c4.hg 
```
