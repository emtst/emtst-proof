# Manual build instructions

1. Build dependencies:
  From this repo's directory run:
  `cd ext/finmap && ./generateMakefile && make && cd ../../`

2. Build the proof:
   From this repo's directory run:
   `./generateMakefile && make`

After running the main make, the successful output should be something
like:

```
COQC theories/OddsAndEnds.v
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

The last line is confirming that the subject reduction theorem does
not depend on axioms or admitted lemmas.