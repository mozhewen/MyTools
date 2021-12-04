# MyTools

Utility functions for calculating loop integrals

## Usage

The main package `MyTools.wl` is based on 

 * FeynCalc (https://github.com/FeynCalc/feyncalc), 
 * FIRE (https://bitbucket.org/feynmanIntegrals/fire/src/master/). 

The tools for differential equations `MyTools4DEs.wl` requires FIRE and

* LiteRed (https://www.inp.nsk.su/~lee/programs/LiteRed/), 
* Libra (https://rnlee.bitbucket.io/Libra/), 

to be installed. The utilities for AMFlow `MyTools4AMF.wl` apparently depends on

* AMFlow (https://gitlab.com/xiaoliu222222/amflow-mma). 

Please install these dependencies before using the corresponding packages. 

To use MyTools in Mathematica, simply type 
```Mathematica
$FIREHome = "/path/to/fire/FIRE6";
Get["/path/to/MyTools/MyTools.wl"]
```
at the beginning of your notebook file. To load it in parallel kernels, you should load FeynCalc in
parallel explicitly before getting `MyTools.wl`: 

```Mathematica
ParallelNeeds["FeynCalc`"]
ParallelEvaluate[
	$FIREHome = "/path/to/fire/FIRE6";
	Get["/path/to/MyTools/MyTools.wl"]
]
```

## File Description

  * `MyTools.wl`

    Source code of the main package. 

* `MyTools4DEs.wl`

  Utility functions for deriving differential equations of scalar integrals. 

* `prepareFIRE.wls`

  It's invoked by `MyTools.wl` and `MyTools4DEs.wl` to run the Mathematica part of FIRE for preparing start files. It should be in the same directory as `MyTools.wl` and `MyTools4DEs.wl`. 

* `MyTools4AMF.wl`

  Utility functions for calculating Feynman integrals using the AMFlow package. 

* `BareSMQCD.mod`

  Modified version of `SMQCD.mod` to generate counter-terms (up to two loops) that are derived from the bare perturbation theory. 

  **Note that** only the quark-quark vertex in the model `SM.mod` is revised. The rest electroweak vertices in `SM.mod` are unchanged (e.g., There are still wave function RCs in the quark-quark-photon vertex). So one should use this file with care. 

* `UnitarySMQCD.mod`

  Modified version of `UnitarySM.mod` to keep the ghost field for gluon. 
