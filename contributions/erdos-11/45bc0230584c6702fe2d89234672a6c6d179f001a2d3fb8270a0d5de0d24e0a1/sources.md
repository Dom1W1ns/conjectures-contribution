# Sources, scope, and handoff

This is one bundled partial contribution to `erdos-11`, usable in either mode.
It does **not** prove or refute the conjecture and does not supply a failing integer.

Target: [Erdős Problem 11](https://conjectures.io/problems/erdos11-erdos-11),
the proposition `∀ n : ℕ, Odd n → 1 < n → ∃ k l : ℕ, Squarefree k ∧ n = k + 2 ^ l`.
The proposition is written explicitly in the source, so the contribution does not
invoke the unproved `Erdos11.erdos_11` declaration.

## Parent contribution and marginal work

Parent:
[`9912bf43713402fa030c83358b48a3fe22041358846f121c30389f4e1775d74a`](https://github.com/conjectures-io/conjectures-contribution/tree/main/contributions/erdos-11/9912bf43713402fa030c83358b48a3fe22041358846f121c30389f4e1775d74a).
The signed metadata lists this parent. The parent's
`exists_squarefree_add_two_pow_iff` is reproduced with its original proof inside
`Contribution.Erdos11Certificates.Parent`, solely because each submitted file must
elaborate independently and cannot import a sibling contribution. No new credit
is claimed for that lemma or for the parent's other results.

The delta is the finite square-divisor certificate interface, exponent-periodicity
and finite-counting consequences, an unbounded obstruction-prefix construction in
the requested residue class, the fully checked positive certificate example, and
the exact short-window separation theorem described below. These statements do
not occur in the target's published contribution index at base commit
`be220ff2519ecfd61b28ba9e477321e4287ef6b4`.

The parent reduction for the not-four-divides variant assumes the original
conjecture. Neither that reduction nor this submission proves the original
conjecture on the residue class `1 mod 4`.

## Concrete reuse

All new public names start with `Contribution.Erdos11Certificates`.

1. **Finite counterexample certificates.**
   `not_representation_iff_prime_square_cover` converts absence of a representation
   into a bounded family of prime-square obstructions once `n ≤ 2^L` is supplied.
   `not_representation_of_square_divisors` accepts any explicitly nontrivial
   square divisors, so a solver need not factor every remainder inside Lean.
   `refute_of_three_mod_four_certificate` turns a *complete* such certificate for
   an integer `n % 4 = 3` into a refutation of the exact universal target.
   `refute_pinned_target_of_certificate` preserves the earlier task-interface name
   using that same explicit proposition; it is a convenience alias, not a separate
   mathematical advance. No complete counterexample certificate is provided.

2. **Periodicity and finite counting.**
   `blocking_exponents_congruent` shows that repeated obstructions from a modulus
   coprime to two lie in one exponent residue class modulo its multiplicative
   order. `blocking_exponents_card_le` bounds its capacity on a finite initial
   interval. `finite_cover_capacity` sums these capacities for a supplied complete
   covering pool. The finite rounding terms are retained: an asymptotic density
   estimate alone does not rule out a particular finite cover.

3. **Unbounded failed prefixes.**
   `exists_obstruction_progression` constructs a CRT progression forcing a
   prime-square obstruction for each exponent in an arbitrary finite prefix.
   `arbitrarily_long_obstruction_prefix` gives arbitrarily large members in
   `n % 4 = 3`, with all those powers strictly below `n`.
   `no_uniform_exponent_bound` rules out a fixed initial exponent cutoff as a
   universal proof strategy, even in this residue class. The integer depends on
   the cutoff; exchanging these quantifiers would not produce a counterexample.

4. **Prime-square separation below gap 110.**
   `ShortCollisions.prime_square_mersenne_lt_110` proves that if a prime square
   divides `2^d - 1` for `0 < d < 110`, its prime base is 3, 5, or 7.
   `ShortCollisions.no_repeated_large_prime` transfers this to two remainders
   `n - 2^a` and `n - 2^b`, using the stated bounds on natural subtraction.
   `ShortCollisions.large_blockers_injective` is a reusable search constraint:
   prime blockers at least 11 must be distinct within a window containing at most
   110 exponents. This does not bound the total number of different blockers.

5. **Checked use example.**
   `Regression.prefix_certificate` supplies twelve explicit failed remainders for
   `40448892456331339`. `Regression.successful_remainder` proves that the remainder
   at exponent 12 is squarefree, and `Regression.candidate_has_representation`
   supplies the positive representation. The primality chain for its largest
   factor is checked with Lucas certificates. This integer is not a counterexample.

## Mathematical and software provenance

- The witness-elimination lemma is copied from the parent linked above, with
  attribution and a local namespace. All other proof implementations in this
  package were developed during this task with OpenAI Codex assistance.
- The CRT construction follows the standard argument recorded in Remark 4 of
  Christian Hercher, [On the Sum of Squarefree Integers and a Power of Two](https://arxiv.org/html/2411.01964v1).
  The implementation here adds the `3 mod 4` constraint, an arbitrary lower bound,
  and a reusable progression interface. No claim is made that the underlying CRT
  argument is new.
- Multiplicative-order obstructions are part of the classical approach of
  Granville and Soundararajan,
  [A Binary Additive Problem of Erdős and the Order of 2 mod p²](https://dms.umontreal.ca/~andrew/PDF/wieferich.pdf).
  Their density results are not used as a proof of the universal conjecture.
- The short-window viewpoint was also informed by Harman and Paquin,
  [The One-Power Erdős Conjecture for Primes p ≡ 7 (mod 36)](https://arxiv.org/html/2610.07214v1).
  The finite extension through exponent gap 109 is established by the included
  certificates; no external paper is an axiom or proof dependency.
- The proofs use standard APIs from
  [Mathlib](https://github.com/leanprover-community/mathlib4), including
  squarefreeness, Chinese remaindering, multiplicative order, finite interval
  counting, and `lucas_primality`.
- Sage/PARI with primality proofs enabled generated factorization candidates.
  A local generator translated these into explicit Lean factorizations and 113
  large-prime Lucas certificates. The 109 gap cases are grouped into four private
  proofs. Every generated helper is used by the public finite separation theorem.
  The generator and external arithmetic are untrusted: Lean checks the emitted
  certificates using ordinary proof terms, `decide +kernel`, and Mathlib's
  proof-producing `reduce_mod_char` tactic. The latter supplies efficient modular
  exponentiation on the submission's older Lean version.

## Verification and limits

The final artifact is self-contained and imports only Mathlib modules. It uses
no unproved target theorem, extra axiom, `sorry`, `native_decide`, source patch,
sibling import, or external service during elaboration.

The constituent modules were checked under the original task's Lean 4.35.0-rc2
pin. The assembled contribution is separately checked under the current
submission pin, Lean 4.33.1 and Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`. The public declaration axiom audit permits
only `propext`, `Classical.choice`, and `Quot.sound`.

The large exploratory searches from the working session are not submitted as
kernel-certified bounds. This contribution requests recognition for the reusable
checked results and their integration, not for search volume, generated helper
count, or time spent. Acceptance, recognition weight, and any eventual payout are
determined by the repository's contribution contract.
