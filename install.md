# EMTST - Installation and documentation

## Instalation

There are two options, the first option installs the required software and
builds the development automatically. And the second options is how to build the
repository after installing the prequisites.

### Option 1: Automatic installation

Run the script: ```./go.sh``` from your user (the user must be able to run
sudo).

The script will:
- install opam 2.X from the avsm/ppa repository
- initialise opam and install:
  + Coq 8.9.0
  + Ssreflect 1.7.0
- build and validate the development.

### Option 2: Manual installation of requirements & building instructions

This option requires the following software:
- Coq 8.9.0
- Ssreflect 1.7.0

The recommended way is by installing them through opam using the following
package names: ```coq.8.9.0``` and ```coq-mathcomp-ssreflect.1.7.0```

To build and run Coq's typechecker, the command ```./build.sh``` will generate
the make files and make the whole project.

### Successful execution

A successful compilation and type checking should end in a similar maner to this:
``` 
...
COQC theories/Atom.v
COQC theories/AtomScopes.v
COQC theories/Env.v
COQC theories/SyntaxO.v
COQC theories/TypesO.v
COQC theories/SyntaxR.v
COQC theories/TypesR.v
COQC theories/SafetyR.v
Closed under the global context
```

where ```Closed under the global context``` is printed in response to the
command: ```Print Assumptions SubjectReduction.``` at the end of
```./theories/SafetyR.v```. This indicates that the subject reduction lemma is completely proved and it does not depend on any axioms or admitted theormes.

## Contents of the repository

Folder ```./theories/``` -- The main development
Folder ```./ext/``` -- An the library on finite maps.

### Theory files and description

The core of the development is in the ```./theories/``` directory, and
this are the important files:

| File         |  Description                                     |  Something   |
|--------------|--------------------------------------------------|------------- |
| Atom.v       | Definition of Atom as a module and a module type |    EMTST     |
| AtomScopes.v | Definition of multiple disjoint atom sets        |    EMTST     |
| Env.v        | Definition of environments and helper lemmas     |    EMTST     |
| SyntaxO.v    | LN Syntax of the original system                 |   Original   |
| TypesO.v     | Typing and counterexample of the original system |   Original   |
| SyntaxR.v    | Syntax for the revisited system                  |   Revisited  |
| TypesR.v     | Typing for the revisited system                  |   Revisited  |
| SafetyR.v    | Subject reduction and associated lemmas          |   Revisited  |

## Navigating the code base

To navigate the proofs and execute them line by line we recommend using the
[Emacs](https://www.gnu.org/software/emacs/) and [Proof
General](https://proofgeneral.github.io/).