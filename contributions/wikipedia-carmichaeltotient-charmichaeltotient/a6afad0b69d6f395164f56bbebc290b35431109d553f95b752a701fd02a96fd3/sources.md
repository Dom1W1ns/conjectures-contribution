# Sources, scope, and use

This is a partial contribution for `CarmichaelTotient.charmichaelTotient`. The single self-contained Lean source supplies the full Carmichael--Klee prime-square forcing lemma, Pomerance's sufficient criterion for global totient uniqueness, a finite divisor certificate for that criterion, and a reduction of its witness class to squares of products of distinct primes. It also retains elementary forcing, collision transport, prime-power exclusions, the bound `3261636 ∣ n`, and the verified interval `0 < n < 13046544`.

## Concrete use by a later solver

All declarations are under `Contribution.CarmichaelTotient` or a subnamespace of it.

- `Klee.carmichael_klee`: assuming a positive globally unique totient preimage `n`, choose `d ∣ n` coprime to `n / d`, require the product of primes dividing `φ(d)` to divide `n`, and choose `e` dividing `(n / d)` after its distinct prime factors have been removed. If `p = 1 + e * φ(d)` is prime, the theorem supplies `p^2 ∣ n`. `Klee.carmichael_klee_support` exposes the equivalent factored interface for avoiding quotient arithmetic.
- `GlobalStrongerForcing.thirteen_or_nineteen_sq_dvd`: every hypothetical counterexample satisfies `13^2 ∣ n ∨ 19^2 ∣ n`, with separate lemmas for the `27 ∣ n` and `¬27 ∣ n` branches.
- `PomeranceCriterion.singleton_of_divisor_certificate`: a positive candidate `n` has a globally unique totient if, for every divisor `d` of `φ(n)`, primality of `d + 1` implies `(d + 1)^2 ∣ n`. This conclusion quantifies over every natural-number preimage. `refutes_carmichael_of_divisor_certificate` is the checked use site deriving the negation of the full target from a candidate and its certificate; it does not supply such a candidate.
- `SquareKernelCriterion.criterion_squareKernel` and `exists_criterion_iff_squareKernel`: a positive witness to Pomerance's sufficient criterion may be replaced by the square of the product of its distinct prime divisors. A search for that particular certificate class can therefore eliminate arbitrary prime exponents.
- `prime_scaling_totient_iff` and `prime_power_scaling_collision`: multiplying an equal-totient pair by a prime preserves equality exactly when the prime divides both inputs or neither. Compatible collisions extend through arbitrary powers of that prime and remain distinct.
- `ClosureAudit.predecessor_square_fixed_point`: the weaker predecessor-square rule alone closes at the seed `3261636`; all eligible primes are in `{2, 3, 7, 43}`. This prevents treating iteration of that weaker rule as a proof of infinitude. The seed itself already has a checked collision.

## Scope limitations

This is not a proof or refutation of Carmichael's conjecture. No integer satisfying Pomerance's certificate is asserted to exist. Its condition is sufficient, and is not proved necessary for all counterexamples. The square-kernel reduction applies only to that sufficient criterion's witness class. No infinitude of the recursively forced prime sets is assumed or proved. The earlier predecessor-forcing hypotheses remain explicit; the source does not assert that every Carmichael counterexample is powerful. Historical Klee/Ford large lower bounds are not formalized here.

## Lineage and formalization delta

This re-promotes the same pending, unmerged [pull request #139](https://github.com/conjectures-io/conjectures-contribution/pull/139) as one expanded contribution. It replaces its earlier draft record `c5b0a9baba06891baad13582f2d541b445a93066fe90b522074549262cbb3abd`; it does not request credit for two copies. No contribution for this target was present on canonical `main` at base `be220ff2519ecfd61b28ba9e477321e4287ef6b4`, so there is no published parent record to list.

The original 28 proved lemmas/theorems and one definition are retained. The expansion adds 29 proved lemmas/theorems and two definitions, including supporting API; the total is 57 proved declarations and three definitions. Declaration counts describe the contents and do not establish recognition value. The main formalization additions are the full forcing interface, the globally quantified sufficient uniqueness proof, and the exact square-kernel reduction. Mathlib supplies the underlying arithmetic and totient identities; these target-specific interfaces are proved from them.

The mathematics is classical except for routine deductions made in assembling the interfaces; no originality claim is made for the underlying Carmichael--Klee or Pomerance arguments. The Lean formalization and exposition were prepared with AI assistance.

## Primary references

- [Kevin Ford, The distribution of totients, Section 7.3, Lemma 7.2](https://arxiv.org/abs/1104.3264), for the full Carmichael--Klee forcing statement.
- [Kevin Ford, Sieving very thin sets of primes, and Pratt trees with missing primes, introduction](https://www.ford126.web.illinois.edu/wwwpapers/recurs.pdf), for the classical 13/19 case split, the conditional infinite-prime route, and Pomerance's sufficient criterion.
- [Carl Pomerance, On Carmichael's conjecture, Proc. Amer. Math. Soc. 43 (1974), 297--298](https://math.dartmouth.edu/~carlp/PDF/carmichaelconjecture.pdf), for the sufficient global uniqueness criterion.
- [Mathlib, Nat.Totient at the pinned revision](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Nat/Totient.lean), for multiplicativity, prime-power formulas, and Euler's product identities.
- [Target problem](https://conjectures.io/problems/carmichaeltotient-charmichaeltotient).

## Verification and dependencies

`script.lean` imports only Mathlib and does not invoke unproved declarations in Formal Conjectures. It contains no proof holes, custom axioms, native evaluation, sibling imports, private services, or local patches. Its bytes match the independently compiled 60-declaration module with SHA-256 `44a07ae4fdc8a971a471a8c29addf6726b33244b04d80ab0d60bb15f14597c47`.

The pinned environment is Formal Conjectures `6a786f997e18e8f095762a2830d191b7e25e505e`, Lean `4.33.1`, and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. The entire source and all 60 axiom reports compiled with warnings treated as errors and a 400000-heartbeat limit. The audit found only `propext`, `Classical.choice`, and `Quot.sound`. The local macOS elaboration environment does not provide the Linux user-namespace network isolation used by remote CI; remote sandbox verification remains a separate gate.
