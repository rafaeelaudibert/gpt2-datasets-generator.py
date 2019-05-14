# Version 1.15

The prover applied to a formula, seeks an intuitionist proof.
If there is none, the formula is not provable without RAA, then
the prover looks for a classic proof (if possible short).
If there is none, the formula is not valid, then
the prover gives a counter-example for the formula.

---

The command `assistant -p A` displays, on the standard output, the proof of the formula written in file A.
For example, A may have the formula `a => a.`, In other words, a formula followed by a dot. And the proof displayed is

```
assumes a.
therefore a => a.
```

The command `assistant -a B` annotate a given proof. File B has a formula followed by its proof without justification, for example it contains

```
a => a.
assumes a.
therefore a => a.
```

In this example, the command displays on the standard out

```
1 assumes a.
2 therefore a => a. => I 1,1
```

The command `assistant -b B` annotates the given evidence, but the justifications of a formula are in the line below the formula

```
1 assumes a.
2 therefore a => a.
      => I 1,1
```

This presentation is less beautiful than the one with the justifications on the right but it is more
adapted to mobiles.

---

Obs: Translated from the original, implemented at http://michel.levy.imag.free.fr/, and available at http://teachinglogic.liglab.fr/DN/download.php

