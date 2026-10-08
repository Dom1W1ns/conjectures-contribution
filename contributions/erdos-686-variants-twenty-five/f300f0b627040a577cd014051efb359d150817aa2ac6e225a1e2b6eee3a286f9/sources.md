# Provenance, use, and limits

This is one combined partial contribution for the [multiplier-25 target](https://conjectures.io/problems/erdos686-erdos-686-variants-twenty-five), prepared by GitHub user Dom1W1ns with AI assistance. It is not a solution of the existential statement over all lengths. The formal contribution collects every completed original Lean module from this research session series; diagnostic copies are consolidated rather than submitted as duplicate claims.

## Concrete use by a later solver

All names are under `Contribution.Erdos686TwentyFive` unless qualified further.

- `k6_exclusion` and `k6_ratio_exclusion` rule out length six for every admissible pair of natural numbers. It is a complete fixed-length result, with an elementary polynomial and congruence argument followed by a kernel-checked finite decision. A solver may remove this length from a case split; this does not remove the other lengths.
- `lower_prime_le_width` and `upper_prime_le_width` constrain prime divisors of the two blocks by their total width, with the necessary exception for the multiplier's prime5. The compositeness corollaries make the additional span hypotheses explicit.
- `square_dvd_transport_of_coprime_complement` supplies a squared divisibility step when its coprimality hypothesis is established. It does not assert that hypothesis for every prime allocation.
- The three `higherContact_*` lemmas check the algebraic divisibility mechanism of a supplied contact certificate. The accompanying obstruction note explains why uniform full-support polynomial contact does not close the k=5 problem. These supporting lemmas are retained for reproducibility, with no separate reward claim for generic wrappers.
- `centeredFive_to_quotient` maps a nonzero centered rational solution to the explicit sextic equation. It supplies the algebraic step needed before the covering-curve analysis. It does not prove completeness of that analysis.
- `NormRelationBridge.relation_injective` and `relation_finrank_le` prove the abstract F2-linear consequence of a coefficient-five relation. The exact permutation certificate is supplied separately; its arithmetic class-group instantiation is not formalized in Lean and no numerical rank bound is claimed.

## Mathematical and software sources

- The target and bibliographic context are from [Erdős Problem686](https://www.erdosproblems.com/686) and the [pinned task repository](https://github.com/conjectures-io/conjectures-tasks/tree/2a58149e6edb0f1dc15b32391f8c29fdd85e9db3/pool/tier-1/erdos-686-variants-twenty-five-formalized).
- The formal proofs use [Mathlib at0df444a360eaa60ab8c11dca51a86af692955474](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474), with Lean4.33.1. The project source pin is [Formal Conjectures6a786f997e18e8f095762a2830d191b7e25e505e](https://github.com/google-deepmind/formal-conjectures/tree/6a786f997e18e8f095762a2830d191b7e25e505e).
- Related background includes [Bennett–van Luijk, Squares from blocks of consecutive integers](https://doi.org/10.1016/j.indag.2011.11.002) and [Erdős–Straus, On Products of Consecutive Integers](https://www.renyi.hu/~p_erdos/1977-18.pdf). Their theorems are not imported as unproved hypotheses.
- The written class-group correspondence interpretation uses [Etienne, Computing class groups by induction with generalised norm relations](https://arxiv.org/html/2411.13124v2), and the certification limitations are informed by [Biasse–Fieker–Hofmann–Page](https://www.normalesup.org/~page/Recherche/Documents/articles/brauer.pdf). Our explicit finite-group matrices, field specializations and accompanying checkers were developed during this work. These computational results are not presented as Lean theorems.
- The Cayley-resolvent construction uses the classical quintic-invariant setting discussed by [Dummit](https://site.uvm.edu/ddummit/files/2021/04/Solving_Solvable_Quintics__Math_Comp_57_no195_1991__pp_387_401.pdf). The included symbolic program derives its coefficients anew and checks polynomial identities. The quartic pair-product resolvent is classical.

No claim of priority is made for the underlying elementary arguments or classical constructions. The submitted delta is the target-specific formalization, its interfaces, and the explicitly scoped computational handoff. No source from the friend's erdos790 repository is incorporated. All new proof bodies were generated with AI assistance and checked against the stated environment.

At upstream base `be220ff2519ecfd61b28ba9e477321e4287ef6b4`, the official contribution listing contains no published records for this target. Therefore `parents` is empty. Recognition and payment remain decisions of the project under its [contribution contract](https://github.com/conjectures-io/conjectures-contribution/blob/main/contribution-contract.md).
