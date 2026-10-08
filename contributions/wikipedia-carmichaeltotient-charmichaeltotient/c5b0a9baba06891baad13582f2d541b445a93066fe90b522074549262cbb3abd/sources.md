# Sources and scope

This partial contribution formalizes elementary constraints on a hypothetical unique preimage of Euler's totient function. Its main reusable lemma forces `p^2 ∣ n` from primality of `p`, global uniqueness of the totient preimage, and `(p - 1)^2 ∣ n`. It derives `3261636 ∣ n`, excludes every prime power, and proves coprime transport of totient collisions. Three explicit collisions then prove Carmichael's conclusion for every `0 < n < 13046544`.

These are classical mathematical arguments formalized with AI assistance. No originality claim is made for the underlying mathematics. This is not a solution of the global conjecture, and it does not formalize Klee's or Ford's historical large lower bounds.

## References

- [Carmichael's totient conjecture task](https://conjectures.io/problems/carmichaeltotient-charmichaeltotient).
- [Kevin Ford, The distribution of totients, Section 7.3](https://arxiv.org/abs/1104.3264), for the classical Carmichael--Klee prime-square method. The predecessor-square lemma here is an elementary sufficient condition, not the full Carmichael--Klee lemma.
- [Mathlib, Nat.Totient](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Nat/Totient.lean), for multiplicativity, prime-power formulas, and the gcd product identity.

## Formal dependencies and validation

The single self-contained source imports only Mathlib. It does not invoke the unproved upstream conjecture or bound declarations. It contains 28 proved theorems/lemmas and one definition under `Contribution.CarmichaelTotient`.

The contribution pool pins Formal Conjectures commit `6a786f997e18e8f095762a2830d191b7e25e505e`, Lean `4.33.1`, and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. The source was compiled directly against those exact Lean and Mathlib versions, with warnings treated as errors and a 400000-heartbeat budget. All 29 declarations were audited for axioms; only `propext`, `Classical.choice`, and `Quot.sound` occur. The source also compiled under Lean `4.35.0-rc2` with Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`.

The forcing lemma keeps its essential predecessor-divisibility hypothesis. It does not establish that every prime factor of every hypothetical counterexample occurs to exponent at least two. The bounded conclusion is a Lean proof using explicit arithmetic witnesses; it does not depend on an external search program or native evaluation.
