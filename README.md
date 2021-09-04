# MyTools

Utility functions for calculating loop integrals

# Usage

This package is based on FeynCalc (https://github.com/FeynCalc/feyncalc) and FIRE 
(https://bitbucket.org/feynmanIntegrals/fire/src/master/). Please install these packages first. 

To use MyTools in Mathematica, simply type 
```Mathematica
Get["/path/to/MyTools/MyTools.wl"]
```
at the beginning of your notebook file. To load it in parallel kernels, one should load FeynCalc in
parallel explicitly before getting `MyTools.wl`: 
```Mathematica
ParallelNeeds["FeynCalc`"]
ParallelEvaluate[Get["/path/to/MyTools/MyTools.wl"]]
```

# File Description

  * `MyTools.wl`

    Package main source code. 

  * `prepareFIRE.wls`

    It's invoked by `MyTools.wl` to run the Mathematica part of FIRE for preparing start files. 
    It should be in the same directory as `MyTools.wl`. 

  * `master_integrals.nb`

    Template file for finding equivalent MIs between different bases. 

  * `BareSMQCD.mod`

    Modified version of `SMQCD.mod` to generate counter-terms that are derived from bare 
    perturbation theory. **Note that** the quark propagator and electroweak parts in the model `SM.mod` 
    are still unchanged. So one should assign values to those renormalization constants by hand to 
    fit the bare perturbation theory

  * `UnitarySMQCD.mod`

    Modified version of `UnitarySM.mod` to keep the ghost field for gluon. 
