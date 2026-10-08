import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.ReduceModChar

/-!
# Erdős 11: obstruction certificates and exponent separation

This is partial progress on `Erdos11.erdos_11`, not a proof or refutation.
The exact target proposition is written explicitly; no unproved target theorem is imported.

The parent witness-elimination lemma is reproduced below for standalone elaboration,
with its original proof and a local namespace. Its credit belongs to contribution
9912bf43713402fa030c83358b48a3fe22041358846f121c30389f4e1775d74a.
See sources.md for lineage, known mathematics, generated certificates, and use sites.
-/

namespace Contribution.Erdos11Certificates.Parent

/-- Reproduced parent lemma; no novelty claimed for this declaration. -/
theorem exists_squarefree_add_two_pow_iff {n : ℕ} :
    (∃ k l : ℕ, Squarefree k ∧ n = k + 2 ^ l) ↔ ∃ l : ℕ, 2 ^ l < n ∧ Squarefree (n - 2 ^ l) := by
  constructor
  · rintro ⟨k, l, hk, rfl⟩
    have hk0 : k ≠ 0 := hk.ne_zero
    exact ⟨l, by omega, by simpa using hk⟩
  · rintro ⟨l, hlt, hk⟩
    exact ⟨n - 2 ^ l, l, hk, by omega⟩

end Contribution.Erdos11Certificates.Parent


/-!
# Finite square-divisor certificates for Erdős Problem 11

These lemmas verify a supplied obstruction certificate. They do not assert that such a
certificate exists. They use the published witness-elimination theorem from contribution
9912bf43713402fa030c83358b48a3fe22041358846f121c30389f4e1775d74a.
-/

namespace Contribution.Erdos11Certificates

open Contribution.Erdos11Certificates.Parent

/-- The power bound makes the search over admissible exponents finite. -/
theorem exponent_lt_of_pow_lt {n L l : ℕ} (hn : n ≤ 2 ^ L) (hl : 2 ^ l < n) :
    l < L := by
  by_contra h
  have hp : 2 ^ L ≤ 2 ^ l := Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-- A finite list of nonsquarefree remainders is equivalent to absence of a representation. -/
theorem not_representation_iff {n L : ℕ} (hn : n ≤ 2 ^ L) :
    (¬ ∃ k l : ℕ, Squarefree k ∧ n = k + 2 ^ l) ↔
      ∀ l < L, ¬ Squarefree (n - 2 ^ l) := by
  constructor
  · intro h l _ hs
    by_cases hl : 2 ^ l < n
    · exact h (exists_squarefree_add_two_pow_iff.mpr ⟨l, hl, hs⟩)
    · have hz : n - 2 ^ l = 0 := by omega
      exact not_squarefree_zero (hz ▸ hs)
  · intro h hr
    obtain ⟨l, hl, hs⟩ := exists_squarefree_add_two_pow_iff.mp hr
    exact h l (exponent_lt_of_pow_lt hn hl) hs

/-- Every failed representation has a prime-square obstruction at every bounded exponent. -/
theorem not_representation_iff_prime_square_cover {n L : ℕ} (hn : n ≤ 2 ^ L) :
    (¬ ∃ k l : ℕ, Squarefree k ∧ n = k + 2 ^ l) ↔
      ∀ l < L, ∃ p : ℕ, p.Prime ∧ p * p ∣ n - 2 ^ l := by
  classical
  rw [not_representation_iff hn]
  simp only [Nat.squarefree_iff_prime_squarefree, not_forall, not_not, exists_prop]

/-- Checking square divisors avoids factoring the remainders inside the Lean kernel. -/
theorem not_representation_of_square_divisors {n L : ℕ} (hn : n ≤ 2 ^ L)
    (d : ℕ → ℕ) (hd : ∀ l < L, 1 < d l ∧ d l * d l ∣ n - 2 ^ l) :
    ¬ ∃ k l : ℕ, Squarefree k ∧ n = k + 2 ^ l := by
  apply (not_representation_iff hn).mpr
  intro l hl hs
  obtain ⟨hlarge, hdiv⟩ := hd l hl
  have hone : d l = 1 := Nat.isUnit_iff.mp (hs (d l) hdiv)
  omega

/-- A certified candidate in the requested residue class refutes the exact original proposition. -/
theorem refute_of_three_mod_four_certificate {n L : ℕ} (hclass : n % 4 = 3)
    (hn : n ≤ 2 ^ L) (d : ℕ → ℕ)
    (hd : ∀ l < L, 1 < d l ∧ d l * d l ∣ n - 2 ^ l) :
    ¬ (∀ n : ℕ, Odd n → 1 < n → ∃ k l : ℕ, Squarefree k ∧ n = k + 2 ^ l) := by
  intro H
  have ho : Odd n := by rw [Nat.odd_iff]; omega
  exact not_representation_of_square_divisors hn d hd (H n ho (by omega))

/-- Repeated obstructions from a modulus coprime to two lie in one exponent residue class. -/
theorem blocking_exponents_congruent {n q a b : ℕ} (ha : 2 ^ a ≤ n) (hb : 2 ^ b ≤ n)
    (hc : Nat.Coprime 2 q) (hda : q ∣ n - 2 ^ a) (hdb : q ∣ n - 2 ^ b) :
    Nat.ModEq (orderOf (ZMod.unitOfCoprime 2 hc)) a b := by
  have hm : Nat.ModEq q (2 ^ a) (2 ^ b) :=
    ((Nat.modEq_iff_dvd' ha).mpr hda).trans ((Nat.modEq_iff_dvd' hb).mpr hdb).symm
  have hz : (2 : ZMod q) ^ a = (2 : ZMod q) ^ b := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      (ZMod.natCast_eq_natCast_iff (2 ^ a) (2 ^ b) q).mpr hm
  have hu : (ZMod.unitOfCoprime 2 hc) ^ a = (ZMod.unitOfCoprime 2 hc) ^ b := by
    apply Units.ext
    simpa using hz
  exact pow_eq_pow_iff_modEq.mp hu

end Contribution.Erdos11Certificates


/-!
# Arbitrarily long initial obstruction intervals

The Chinese remainder construction in Remark 4 of Christian Hercher's
"On the Sum of Squarefree Integers and a Power of Two"
(https://arxiv.org/html/2411.01964v1) also permits the restriction `n % 4 = 3`.
This rules out any proof strategy that checks only a fixed number of initial exponents.
It does not provide an integer for which every admissible exponent fails.
-/

namespace Contribution.Erdos11Certificates

/-- A common progression can force a prime-square obstruction at each of finitely many powers. -/
theorem exists_obstruction_progression (L : ℕ) :
    ∃ a M : ℕ, 0 < M ∧ 4 ∣ M ∧ a % 4 = 3 ∧
      ∀ l < L, ∃ p : ℕ, p.Prime ∧ p * p ∣ M ∧ Nat.ModEq (p * p) a (2 ^ l) := by
  induction L with
  | zero =>
      refine ⟨3, 4, by decide, by decide, by decide, ?_⟩
      intro l hl
      omega
  | succ L ih =>
      obtain ⟨a, M, hM, hfour, ha, hcover⟩ := ih
      obtain ⟨p, hpM, hp⟩ := Nat.exists_infinite_primes (M + 1)
      have hnotdvd : ¬ p ∣ M := by
        intro hd
        have := Nat.le_of_dvd hM hd
        omega
      have hcp : Nat.Coprime M p := (hp.coprime_iff_not_dvd.mpr hnotdvd).symm
      have hc : Nat.Coprime M (p * p) := hcp.mul_right hcp
      obtain ⟨c, hca, hcpow⟩ := Nat.chineseRemainder hc a (2 ^ L)
      have hc4 : c % 4 = 3 := by
        have hm : c % 4 = a % 4 := hca.of_dvd hfour
        exact hm.trans ha
      refine ⟨c, M * (p * p), Nat.mul_pos hM (Nat.mul_pos hp.pos hp.pos),
        dvd_mul_of_dvd_left hfour _, hc4, ?_⟩
      intro l hl
      by_cases heq : l = L
      · subst l
        exact ⟨p, hp, dvd_mul_left _ _, hcpow⟩
      · obtain ⟨q, hq, hqM, hqa⟩ := hcover l (by omega)
        exact ⟨q, hq, dvd_mul_of_dvd_left hqM _, (hca.of_dvd hqM).trans hqa⟩

/-- Even in the searched residue class, no fixed initial exponent interval always suffices. -/
theorem arbitrarily_long_obstruction_prefix (L B : ℕ) :
    ∃ n : ℕ, B < n ∧ n % 4 = 3 ∧ 2 ^ L < n ∧
      ∀ l < L, ¬ Squarefree (n - 2 ^ l) := by
  obtain ⟨a, M, hM, hfour, ha, hcover⟩ := exists_obstruction_progression L
  let n := a + M * (B + 2 ^ L + 1)
  have hlarge : B + 2 ^ L < n := by
    have hmul := Nat.le_mul_of_pos_left (B + 2 ^ L + 1) hM
    dsimp [n]
    omega
  have hna : Nat.ModEq M n a := by
    simp [n, Nat.ModEq]
  refine ⟨n, lt_of_le_of_lt (Nat.le_add_right _ _) hlarge, ?_,
    lt_of_le_of_lt (Nat.le_add_left _ _) hlarge, ?_⟩
  · have hm : n % 4 = a % 4 := hna.of_dvd hfour
    exact hm.trans ha
  · intro l hl hs
    obtain ⟨p, hp, hpM, hpa⟩ := hcover l hl
    have hm : Nat.ModEq (p * p) n (2 ^ l) := (hna.of_dvd hpM).trans hpa
    exact hp.ne_one (Nat.isUnit_iff.mp (hs p hm.symm.dvd'))

/-- There is no uniform finite cap on a successful exponent in the searched residue class. -/
theorem no_uniform_exponent_bound :
    ¬ ∃ L : ℕ, ∀ n : ℕ, n % 4 = 3 → 1 < n →
      ∃ l < L, Squarefree (n - 2 ^ l) := by
  rintro ⟨L, h⟩
  obtain ⟨n, hn, hclass, _, hfail⟩ := arbitrarily_long_obstruction_prefix L 1
  obtain ⟨l, hl, hs⟩ := h n hclass hn
  exact hfail l hl hs

end Contribution.Erdos11Certificates


/-!
# Finite exponent-cover capacity

Periodicity gives a finite-interval upper bound with a rounding term for each
obstructing modulus. Dropping those terms is not a valid pointwise argument.
The final theorem is conditional on a supplied complete obstruction pool;
it does not establish the missing bound for arbitrary integers.
-/

namespace Contribution.Erdos11Certificates

open Finset

/-- A fixed exponent residue class occupies at most `L / t + 1` places below `L`. -/
theorem exponent_residue_card_le (L t a : ℕ) (ht : 0 < t) :
    ((range L).filter (fun l => Nat.ModEq t l a)).card ≤ L / t + 1 := by
  rw [← Nat.count_eq_card_filter_range, Nat.count_modEq_card L ht a]
  split_ifs <;> omega

/-- The finite counting consequence of the inherited exponent-periodicity lemma. -/
theorem blocking_exponents_card_le {n q L : ℕ}
    (hn : ∀ l < L, 2 ^ l ≤ n) (hc : Nat.Coprime 2 q)
    (ht : 0 < orderOf (ZMod.unitOfCoprime 2 hc)) :
    ((range L).filter (fun l => q ∣ n - 2 ^ l)).card ≤
      L / orderOf (ZMod.unitOfCoprime 2 hc) + 1 := by
  classical
  by_cases he : ((range L).filter (fun l => q ∣ n - 2 ^ l)).Nonempty
  · obtain ⟨a, ha⟩ := he
    obtain ⟨haL, had⟩ := mem_filter.mp ha
    have hs : (range L).filter (fun l => q ∣ n - 2 ^ l) ⊆
        (range L).filter (fun l =>
          Nat.ModEq (orderOf (ZMod.unitOfCoprime 2 hc)) l a) := by
      intro l hl
      obtain ⟨hlL, hld⟩ := mem_filter.mp hl
      exact mem_filter.mpr ⟨hlL,
        blocking_exponents_congruent (hn l (mem_range.mp hlL))
          (hn a (mem_range.mp haL)) hc hld had⟩
    exact (card_le_card hs).trans (exponent_residue_card_le L _ a ht)
  · have hz := not_nonempty_iff_eq_empty.mp he
    simp [hz]

/-- A complete finite cover must have enough capacity, including finite rounding terms. -/
theorem finite_cover_capacity {n L : ℕ} (P : Finset ℕ)
    (hn : ∀ l < L, 2 ^ l ≤ n)
    (hc : ∀ q ∈ P, Nat.Coprime 2 q)
    (ht : ∀ q, ∀ hq : q ∈ P, 0 < orderOf (ZMod.unitOfCoprime 2 (hc q hq)))
    (hcover : ∀ l < L, ∃ q ∈ P, q ∣ n - 2 ^ l) :
    L ≤ ∑ q ∈ P.attach, (L / orderOf (ZMod.unitOfCoprime 2 (hc q q.property)) + 1) := by
  classical
  have hs : range L ⊆ P.attach.biUnion (fun q =>
      (range L).filter (fun l => q.val ∣ n - 2 ^ l)) := by
    intro l hl
    obtain ⟨q, hq, hd⟩ := hcover l (mem_range.mp hl)
    exact mem_biUnion.mpr ⟨⟨q, hq⟩, by simp, mem_filter.mpr ⟨hl, hd⟩⟩
  calc
    L = (range L).card := (card_range L).symm
    _ ≤ (P.attach.biUnion (fun q =>
        (range L).filter (fun l => q.val ∣ n - 2 ^ l))).card := card_le_card hs
    _ ≤ ∑ q ∈ P.attach, ((range L).filter (fun l => q.val ∣ n - 2 ^ l)).card :=
      card_biUnion_le
    _ ≤ ∑ q ∈ P.attach, (L / orderOf (ZMod.unitOfCoprime 2 (hc q q.property)) + 1) := by
      exact Finset.sum_le_sum (fun q _ =>
        blocking_exponents_card_le hn (hc q.val q.property) (ht q.val q.property))

end Contribution.Erdos11Certificates


/-!
# Check the deepest candidate from the finite CRT search

This is a positive example with twelve initial obstructions, not a counterexample.
All computations below produce kernel-checked proof terms.
-/

namespace Contribution.Erdos11Certificates.Regression

def blocker (l : ℕ) : ℕ :=
  ([17, 11, 3, 7, 19, 13, 5, 23, 3, 43, 317, 131] : List ℕ).getD l 1

/-- The first twelve powers leave remainders divisible by explicit nontrivial squares. -/
theorem prefix_certificate : ∀ l < 12,
    1 < blocker l ∧ blocker l * blocker l ∣ 40448892456331339 - 2 ^ l := by
  decide +kernel

/-- No exponent below twelve represents this candidate. -/
theorem prefix_failure : ∀ l < 12, ¬ Squarefree (40448892456331339 - 2 ^ l) := by
  intro l hl hs
  obtain ⟨hlarge, hdiv⟩ := prefix_certificate l hl
  have hone : blocker l = 1 := Nat.isUnit_iff.mp (hs (blocker l) hdiv)
  omega

/-- A small Lucas certificate used in the primality chain. -/
theorem prime_836337043 : Nat.Prime 836337043 := by
  apply lucas_primality 836337043 (2 : ZMod 836337043) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (3 * (3 * (3 * (443 * 34961)))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 443),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 34961)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

/-- The next Lucas certificate in the primality chain. -/
theorem prime_5018022259 : Nat.Prime 5018022259 := by
  apply lucas_primality 5018022259 (2 : ZMod 5018022259) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (3 * 836337043) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq prime_836337043] at hd
  rcases hd with rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

/-- The remaining large factor in the successful remainder is prime. -/
theorem large_factor_prime : Nat.Prime 60216267109 := by
  apply lucas_primality 60216267109 (2 : ZMod 60216267109) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (3 * 5018022259)) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq prime_5018022259] at hd
  rcases hd with rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

/-- The remainder at exponent twelve has five distinct prime factors. -/
theorem successful_remainder : Squarefree (40448892456331339 - 2 ^ 12 : ℕ) := by
  have h₁ : Squarefree (1103 * 60216267109 : ℕ) :=
    (Nat.squarefree_mul (by norm_num : Nat.Coprime 1103 60216267109)).mpr
      ⟨(by norm_num : Nat.Prime 1103).squarefree, large_factor_prime.squarefree⟩
  have h₂ : Squarefree (29 * (1103 * 60216267109) : ℕ) :=
    (Nat.squarefree_mul (by norm_num : Nat.Coprime 29 (1103 * 60216267109))).mpr
      ⟨(by norm_num : Nat.Prime 29).squarefree, h₁⟩
  have h₃ : Squarefree (7 * (29 * (1103 * 60216267109)) : ℕ) :=
    (Nat.squarefree_mul (by norm_num : Nat.Coprime 7 (29 * (1103 * 60216267109)))).mpr
      ⟨(by norm_num : Nat.Prime 7).squarefree, h₂⟩
  have h₄ : Squarefree (3 * (7 * (29 * (1103 * 60216267109))) : ℕ) :=
    (Nat.squarefree_mul (by norm_num : Nat.Coprime 3 (7 * (29 * (1103 * 60216267109))))).mpr
      ⟨(by norm_num : Nat.Prime 3).squarefree, h₃⟩
  exact h₄

/-- A checked positive representation of the deepest CRT search candidate. -/
theorem candidate_has_representation :
    ∃ k l : ℕ, Squarefree k ∧ 40448892456331339 = k + 2 ^ l := by
  exact ⟨40448892456331339 - 2 ^ 12, 12, successful_remainder, by norm_num⟩

end Contribution.Erdos11Certificates.Regression


namespace Contribution.Erdos11Certificates.ShortCollisions

private theorem prime_131071 : Nat.Prime 131071 := by
  apply lucas_primality 131071 (3 : ZMod 131071) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (3 * (5 * (17 * (257)))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 17),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 257)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_524287 : Nat.Prime 524287 := by
  apply lucas_primality 524287 (3 : ZMod 524287) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (3 * (3 * (3 * (7 * (19 * (73)))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 19),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 73)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_178481 : Nat.Prime 178481 := by
  apply lucas_primality 178481 (3 : ZMod 178481) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (2 * (5 * (23 * (97)))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 23),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 97)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_262657 : Nat.Prime 262657 := by
  apply lucas_primality 262657 (5 : ZMod 262657) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (3 * (3 * (3 * (19)))))))))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 19)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_2147483647 : Nat.Prime 2147483647 := by
  apply lucas_primality 2147483647 (7 : ZMod 2147483647) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (3 * (3 * (7 * (11 * (31 * (151 * (331))))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 11),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 31),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 151),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 331)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_599479 : Nat.Prime 599479 := by
  apply lucas_primality 599479 (6 : ZMod 599479) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (3 * (11 * (31 * (293)))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 11),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 31),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 293)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_122921 : Nat.Prime 122921 := by
  apply lucas_primality 122921 (3 : ZMod 122921) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (5 * (7 * (439))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 439)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_616318177 : Nat.Prime 616318177 := by
  apply lucas_primality 616318177 (5 : ZMod 616318177) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (2 * (2 * (3 * (37 * (167 * (1039)))))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 37),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 167),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 1039)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_174763 : Nat.Prime 174763 := by
  apply lucas_primality 174763 (17 : ZMod 174763) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (3 * (3 * (7 * (19 * (73))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 19),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 73)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_121369 : Nat.Prime 121369 := by
  apply lucas_primality 121369 (7 : ZMod 121369) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (3 * (13 * (389))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 13),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 389)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_164511353 : Nat.Prime 164511353 := by
  apply lucas_primality 164511353 (3 : ZMod 164511353) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (41 * (59 * (8501))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 41),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 59),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 8501)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_2099863 : Nat.Prime 2099863 := by
  apply lucas_primality 2099863 (3 : ZMod 2099863) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (3 * (3 * (43 * (2713)))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 43),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2713)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_2796203 : Nat.Prime 2796203 := by
  apply lucas_primality 2796203 (5 : ZMod 2796203) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (23 * (89 * (683))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 23),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 89),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 683)] at hd
  rcases hd with rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_13264529 : Nat.Prime 13264529 := by
  apply lucas_primality 13264529 (3 : ZMod 13264529) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (2 * (31 * (47 * (569)))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 31),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 47),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 569)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_4432676798593 : Nat.Prime 4432676798593 := by
  apply lucas_primality 4432676798593 (5 : ZMod 4432676798593) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (2 * (2 * (2 * (2 * (3 * (3 * (7 * (7 * (43 * (337 * (5419))))))))))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 43),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 337),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5419)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_20394401 : Nat.Prime 20394401 := by
  apply lucas_primality 20394401 (3 : ZMod 20394401) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (2 * (2 * (5 * (5 * (13 * (37 * (53))))))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 13),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 37),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 53)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_201961 : Nat.Prime 201961 := by
  apply lucas_primality 201961 (13 : ZMod 201961) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (3 * (3 * (3 * (5 * (11 * (17)))))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 11),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 17)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_15790321 : Nat.Prime 15790321 := by
  apply lucas_primality 15790321 (19 : ZMod 15790321) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (2 * (3 * (3 * (5 * (7 * (13 * (241))))))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 13),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 241)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_1212847 : Nat.Prime 1212847 := by
  apply lucas_primality 1212847 (5 : ZMod 1212847) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (3 * (19 * (10639))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 19),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 10639)] at hd
  rcases hd with rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_3033169 : Nat.Prime 3033169 := by
  apply lucas_primality 3033169 (7 : ZMod 3033169) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (2 * (3 * (29 * (2179)))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 29),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2179)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_179951 : Nat.Prime 179951 := by
  apply lucas_primality 179951 (7 : ZMod 179951) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (5 * (5 * (59 * (61)))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 59),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 61)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_8060489 : Nat.Prime 8060489 := by
  apply lucas_primality 8060489 (3 : ZMod 8060489) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (23 * (71 * (617))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 23),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 71),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 617)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_3203431780337 : Nat.Prime 3203431780337 := by
  apply lucas_primality 3203431780337 (3 : ZMod 3203431780337) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (2 * (59 * (421 * (8060489)))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 59),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 421),
    Nat.prime_dvd_prime_iff_eq hq prime_8060489] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_2305843009213693951 : Nat.Prime 2305843009213693951 := by
  apply lucas_primality 2305843009213693951 (37 : ZMod 2305843009213693951) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (3 * (3 * (5 * (5 * (7 * (11 * (13 * (31 * (41 * (61 * (151 * (331 * (1321))))))))))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 11),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 13),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 31),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 41),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 61),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 151),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 331),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 1321)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_715827883 : Nat.Prime 715827883 := by
  apply lucas_primality 715827883 (5 : ZMod 715827883) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (3 * (7 * (11 * (31 * (151 * (331)))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 11),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 31),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 151),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 331)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_649657 : Nat.Prime 649657 := by
  apply lucas_primality 649657 (5 : ZMod 649657) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (3 * (3 * (7 * (1289)))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 1289)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_6700417 : Nat.Prime 6700417 := by
  apply lucas_primality 6700417 (5 : ZMod 6700417) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (2 * (2 * (2 * (2 * (3 * (17449)))))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 17449)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_8620289 : Nat.Prime 8620289 := by
  apply lucas_primality 8620289 (3 : ZMod 8620289) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (151 * (223))))))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 151),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 223)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_2534364967 : Nat.Prime 2534364967 := by
  apply lucas_primality 2534364967 (3 : ZMod 2534364967) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (3 * (7 * (7 * (8620289)))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hq prime_8620289] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_145295143558111 : Nat.Prime 145295143558111 := by
  apply lucas_primality 145295143558111 (7 : ZMod 145295143558111) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (3 * (3 * (5 * (7 * (7 * (13 * (2534364967))))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 13),
    Nat.prime_dvd_prime_iff_eq hq prime_2534364967] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_193707721 : Nat.Prime 193707721 := by
  apply lucas_primality 193707721 (59 : ZMod 193707721) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (3 * (3 * (3 * (5 * (67 * (2677)))))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 67),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2677)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_761838257287 : Nat.Prime 761838257287 := by
  apply lucas_primality 761838257287 (3 : ZMod 761838257287) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (3 * (3 * (29 * (67 * (2551 * (8539)))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 29),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 67),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2551),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 8539)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_108943 : Nat.Prime 108943 := by
  apply lucas_primality 108943 (3 : ZMod 108943) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (3 * (67 * (271))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 67),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 271)] at hd
  rcases hd with rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_10052678938039 : Nat.Prime 10052678938039 := by
  apply lucas_primality 10052678938039 (6 : ZMod 10052678938039) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (3 * (11 * (23 * (89 * (683 * (108943)))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 11),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 23),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 89),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 683),
    Nat.prime_dvd_prime_iff_eq hq prime_108943] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_228479 : Nat.Prime 228479 := by
  apply lucas_primality 228479 (11 : ZMod 228479) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (71 * (1609)) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 71),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 1609)] at hd
  rcases hd with rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_48544121 : Nat.Prime 48544121 := by
  apply lucas_primality 48544121 (3 : ZMod 48544121) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (5 * (71 * (17093))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 71),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 17093)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_212885833 : Nat.Prime 212885833 := by
  apply lucas_primality 212885833 (11 : ZMod 212885833) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (3 * (17 * (71 * (7349)))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 17),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 71),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7349)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_2298041 : Nat.Prime 2298041 := by
  apply lucas_primality 2298041 (13 : ZMod 2298041) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (5 * (73 * (787))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 73),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 787)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_105465631 : Nat.Prime 105465631 := by
  apply lucas_primality 105465631 (3 : ZMod 105465631) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (3 * (5 * (263 * (13367)))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 263),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 13367)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_9361973132609 : Nat.Prime 9361973132609 := by
  apply lucas_primality 9361973132609 (3 : ZMod 9361973132609) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (2 * (2 * (2 * (19 * (73 * (105465631)))))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 19),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 73),
    Nat.prime_dvd_prime_iff_eq hq prime_105465631] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_116131 : Nat.Prime 116131 := by
  apply lucas_primality 116131 (2 : ZMod 116131) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (3 * (5 * (7 * (7 * (79))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 79)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_25781083 : Nat.Prime 25781083 := by
  apply lucas_primality 25781083 (5 : ZMod 25781083) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (3 * (37 * (116131))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 37),
    Nat.prime_dvd_prime_iff_eq hq prime_116131] at hd
  rcases hd with rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_100801 : Nat.Prime 100801 := by
  apply lucas_primality 100801 (11 : ZMod 100801) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (2 * (2 * (2 * (3 * (3 * (5 * (5 * (7)))))))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_10567201 : Nat.Prime 10567201 := by
  apply lucas_primality 10567201 (11 : ZMod 10567201) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (2 * (2 * (3 * (5 * (5 * (7 * (17 * (37)))))))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 17),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 37)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_525313 : Nat.Prime 525313 := by
  apply lucas_primality 525313 (5 : ZMod 525313) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (3 * (3 * (3 * (19))))))))))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 19)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_1310329 : Nat.Prime 1310329 := by
  apply lucas_primality 1310329 (7 : ZMod 1310329) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (3 * (3 * (18199))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 18199)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_13528921548413 : Nat.Prime 13528921548413 := by
  apply lucas_primality 13528921548413 (2 : ZMod 13528921548413) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (19 * (73 * (1861 * (1310329))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 19),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 73),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 1861),
    Nat.prime_dvd_prime_iff_eq hq prime_1310329] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_581283643249112959 : Nat.Prime 581283643249112959 := by
  apply lucas_primality 581283643249112959 (6 : ZMod 581283643249112959) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (3 * (3 * (7 * (11 * (31 * (13528921548413)))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 11),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 31),
    Nat.prime_dvd_prime_iff_eq hq prime_13528921548413] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_22366891 : Nat.Prime 22366891 := by
  apply lucas_primality 22366891 (3 : ZMod 22366891) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (3 * (3 * (5 * (7 * (13 * (2731)))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 13),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2731)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_202029703 : Nat.Prime 202029703 := by
  apply lucas_primality 202029703 (3 : ZMod 202029703) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (3 * (7 * (79 * (60889)))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 79),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 60889)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_8583937 : Nat.Prime 8583937 := by
  apply lucas_primality 8583937 (7 : ZMod 8583937) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (3 * (11177))))))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 11177)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_1113491139767 : Nat.Prime 1113491139767 := by
  apply lucas_primality 1113491139767 (5 : ZMod 1113491139767) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (79 * (821 * (8583937))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 79),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 821),
    Nat.prime_dvd_prime_iff_eq hq prime_8583937] at hd
  rcases hd with rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_4278255361 : Nat.Prime 4278255361 := by
  apply lucas_primality 4278255361 (23 : ZMod 4278255361) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (3 * (5 * (17 * (65537))))))))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 17),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 65537)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_602999 : Nat.Prime 602999 := by
  apply lucas_primality 602999 (11 : ZMod 602999) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (11 * (27409)) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 11),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 27409)] at hd
  rcases hd with rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_97685839 : Nat.Prime 97685839 := by
  apply lucas_primality 97685839 (6 : ZMod 97685839) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (3 * (3 * (3 * (3 * (602999))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq prime_602999] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_2991673 : Nat.Prime 2991673 := by
  apply lucas_primality 2991673 (7 : ZMod 2991673) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (3 * (3 * (37 * (1123)))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 37),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 1123)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_8831418697 : Nat.Prime 8831418697 := by
  apply lucas_primality 8831418697 (15 : ZMod 8831418697) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (3 * (3 * (41 * (2991673)))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 41),
    Nat.prime_dvd_prime_iff_eq hq prime_2991673] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_19628971 : Nat.Prime 19628971 := by
  apply lucas_primality 19628971 (2 : ZMod 19628971) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (3 * (5 * (73 * (8963)))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 73),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 8963)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_2812085643403 : Nat.Prime 2812085643403 := by
  apply lucas_primality 2812085643403 (3 : ZMod 2812085643403) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (3 * (3 * (3 * (7 * (379 * (19628971)))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 379),
    Nat.prime_dvd_prime_iff_eq hq prime_19628971] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_11248342573613 : Nat.Prime 11248342573613 := by
  apply lucas_primality 11248342573613 (2 : ZMod 11248342573613) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2812085643403)) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq prime_2812085643403] at hd
  rcases hd with rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_57912614113275649087721 : Nat.Prime 57912614113275649087721 := by
  apply lucas_primality 57912614113275649087721 (6 : ZMod 57912614113275649087721) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (5 * (83 * (383 * (4049 * (11248342573613))))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 83),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 383),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 4049),
    Nat.prime_dvd_prime_iff_eq hq prime_11248342573613] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_2598660833 : Nat.Prime 2598660833 := by
  apply lucas_primality 2598660833 (3 : ZMod 2598660833) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (2 * (2 * (47 * (709 * (2437))))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 47),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 709),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2437)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_9520972806333758431 : Nat.Prime 9520972806333758431 := by
  apply lucas_primality 9520972806333758431 (15 : ZMod 9520972806333758431) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (3 * (5 * (17 * (257 * (27953 * (2598660833)))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 17),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 257),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 27953),
    Nat.prime_dvd_prime_iff_eq hq prime_2598660833] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_2932031007403 : Nat.Prime 2932031007403 := by
  apply lucas_primality 2932031007403 (3 : ZMod 2932031007403) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (3 * (7 * (7 * (43 * (127 * (337 * (5419))))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 43),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 127),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 337),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5419)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_9857737155463 : Nat.Prime 9857737155463 := by
  apply lucas_primality 9857737155463 (5 : ZMod 9857737155463) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (3 * (7 * (29 * (37 * (4217 * (51871)))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 29),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 37),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 4217),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 51871)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_2931542417 : Nat.Prime 2931542417 := by
  apply lucas_primality 2931542417 (3 : ZMod 2931542417) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (2 * (11 * (1913 * (8707)))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 11),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 1913),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 8707)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_618970019642690137449562111 : Nat.Prime 618970019642690137449562111 := by
  apply lucas_primality 618970019642690137449562111 (3 : ZMod 618970019642690137449562111) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (3 * (5 * (17 * (23 * (89 * (353 * (397 * (683 * (2113 * (2931542417)))))))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 17),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 23),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 89),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 353),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 397),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 683),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2113),
    Nat.prime_dvd_prime_iff_eq hq prime_2931542417] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_18837001 : Nat.Prime 18837001 := by
  apply lucas_primality 18837001 (19 : ZMod 18837001) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (3 * (3 * (5 * (5 * (5 * (7 * (13 * (23)))))))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 13),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 23)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_112901153 : Nat.Prime 112901153 := by
  apply lucas_primality 112901153 (3 : ZMod 112901153) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (2 * (2 * (7 * (13 * (137 * (283)))))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 13),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 137),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 283)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_23140471537 : Nat.Prime 23140471537 := by
  apply lucas_primality 23140471537 (43 : ZMod 23140471537) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (2 * (3 * (3 * (7 * (13 * (17 * (109 * (953)))))))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 13),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 17),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 109),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 953)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_658812288653553079 : Nat.Prime 658812288653553079 := by
  apply lucas_primality 658812288653553079 (21 : ZMod 658812288653553079) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (3 * (3 * (11 * (31 * (83 * (151 * (331 * (1277 * (20261))))))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 11),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 31),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 83),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 151),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 331),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 1277),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 20261)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_165768537521 : Nat.Prime 165768537521 := by
  apply lucas_primality 165768537521 (3 : ZMod 165768537521) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (2 * (5 * (47 * (2887 * (15271))))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 47),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2887),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 15271)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_420778751 : Nat.Prime 420778751 := by
  apply lucas_primality 420778751 (7 : ZMod 420778751) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (5 * (5 * (5 * (5 * (7 * (19 * (2531))))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 19),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2531)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_2216897 : Nat.Prime 2216897 := by
  apply lucas_primality 2216897 (3 : ZMod 2216897) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (2 * (2 * (2 * (11 * (47 * (67)))))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 11),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 47),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 67)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_17735177 : Nat.Prime 17735177 := by
  apply lucas_primality 17735177 (3 : ZMod 17735177) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (2216897))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq prime_2216897] at hd
  rcases hd with rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_30327152671 : Nat.Prime 30327152671 := by
  apply lucas_primality 30327152671 (3 : ZMod 30327152671) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (3 * (3 * (5 * (19 * (17735177))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 19),
    Nat.prime_dvd_prime_iff_eq hq prime_17735177] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_115903 : Nat.Prime 115903 := by
  apply lucas_primality 115903 (3 : ZMod 115903) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (3 * (3 * (47 * (137)))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 47),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 137)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_22253377 : Nat.Prime 22253377 := by
  apply lucas_primality 22253377 (5 : ZMod 22253377) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (2 * (2 * (2 * (3 * (115903))))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq prime_115903] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_224968241 : Nat.Prime 224968241 := by
  apply lucas_primality 224968241 (6 : ZMod 224968241) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (2 * (5 * (7 * (31 * (12959))))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 31),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 12959)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_3415403 : Nat.Prime 3415403 := by
  apply lucas_primality 3415403 (2 : ZMod 3415403) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (17 * (17 * (19 * (311)))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 17),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 19),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 311)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_6113571371 : Nat.Prime 6113571371 := by
  apply lucas_primality 6113571371 (2 : ZMod 6113571371) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (5 * (179 * (3415403))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 179),
    Nat.prime_dvd_prime_iff_eq hq prime_3415403] at hd
  rcases hd with rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_13753593975618284111 : Nat.Prime 13753593975618284111 := by
  apply lucas_primality 13753593975618284111 (11 : ZMod 13753593975618284111) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (5 * (224968241 * (6113571371))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hq prime_224968241,
    Nat.prime_dvd_prime_iff_eq hq prime_6113571371] at hd
  rcases hd with rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_13842607235828485645766393 : Nat.Prime 13842607235828485645766393 := by
  apply lucas_primality 13842607235828485645766393 (3 : ZMod 13842607235828485645766393) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (97 * (1297 * (13753593975618284111))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 97),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 1297),
    Nat.prime_dvd_prime_iff_eq hq prime_13753593975618284111] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_4363953127297 : Nat.Prime 4363953127297 := by
  apply lucas_primality 4363953127297 (5 : ZMod 4363953127297) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (2 * (2 * (2 * (2 * (3 * (7 * (7 * (127 * (337 * (5419)))))))))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 127),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 337),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5419)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_153649 : Nat.Prime 153649 := by
  apply lucas_primality 153649 (7 : ZMod 153649) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (2 * (3 * (3 * (11 * (97))))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 11),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 97)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_220553 : Nat.Prime 220553 := by
  apply lucas_primality 220553 (3 : ZMod 220553) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (19 * (1451)))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 19),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 1451)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_33057806959 : Nat.Prime 33057806959 := by
  apply lucas_primality 33057806959 (3 : ZMod 33057806959) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (3 * (3 * (11 * (757 * (220553))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 11),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 757),
    Nat.prime_dvd_prime_iff_eq hq prime_220553] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_268501 : Nat.Prime 268501 := by
  apply lucas_primality 268501 (6 : ZMod 268501) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (3 * (5 * (5 * (5 * (179)))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 179)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_278557 : Nat.Prime 278557 := by
  apply lucas_primality 278557 (2 : ZMod 278557) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (3 * (139 * (167)))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 139),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 167)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_7432339208719 : Nat.Prime 7432339208719 := by
  apply lucas_primality 7432339208719 (3 : ZMod 7432339208719) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (3 * (101 * (44029 * (278557)))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 101),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 44029),
    Nat.prime_dvd_prime_iff_eq hq prime_278557] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_195241 : Nat.Prime 195241 := by
  apply lucas_primality 195241 (11 : ZMod 195241) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (3 * (5 * (1627))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 1627)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_295985357 : Nat.Prime 295985357 := by
  apply lucas_primality 295985357 (2 : ZMod 295985357) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (379 * (195241))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 379),
    Nat.prime_dvd_prime_iff_eq hq prime_195241] at hd
  rcases hd with rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_341117531003194129 : Nat.Prime 341117531003194129 := by
  apply lucas_primality 341117531003194129 (13 : ZMod 341117531003194129) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (2 * (3 * (3 * (101 * (79241 * (295985357)))))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 101),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 79241),
    Nat.prime_dvd_prime_iff_eq hq prime_295985357] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_2550183799 : Nat.Prime 2550183799 := by
  apply lucas_primality 2550183799 (11 : ZMod 2550183799) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (3 * (83 * (83 * (103 * (599))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 83),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 103),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 599)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_5409427 : Nat.Prime 5409427 := by
  apply lucas_primality 5409427 (3 : ZMod 5409427) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (3 * (11 * (11 * (7451)))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 11),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7451)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_32456563 : Nat.Prime 32456563 := by
  apply lucas_primality 32456563 (3 : ZMod 32456563) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (3 * (5409427)) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq prime_5409427] at hd
  rcases hd with rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_3976656429941438590393 : Nat.Prime 3976656429941438590393 := by
  apply lucas_primality 3976656429941438590393 (5 : ZMod 3976656429941438590393) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (3 * (103 * (149 * (4657 * (71429 * (32456563)))))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 103),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 149),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 4657),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 71429),
    Nat.prime_dvd_prime_iff_eq hq prime_32456563] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_858001 : Nat.Prime 858001 := by
  apply lucas_primality 858001 (17 : ZMod 858001) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (2 * (3 * (5 * (5 * (5 * (11 * (13))))))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 11),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 13)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_308761441 : Nat.Prime 308761441 := by
  apply lucas_primality 308761441 (17 : ZMod 308761441) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (2 * (2 * (3 * (5 * (13 * (49481)))))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 13),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 49481)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_106681 : Nat.Prime 106681 := by
  apply lucas_primality 106681 (23 : ZMod 106681) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (3 * (5 * (7 * (127)))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 127)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_152041 : Nat.Prime 152041 := by
  apply lucas_primality 152041 (11 : ZMod 152041) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (3 * (5 * (7 * (181)))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 181)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_67254877 : Nat.Prime 67254877 := by
  apply lucas_primality 67254877 (2 : ZMod 67254877) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (3 * (3 * (13 * (131 * (1097)))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 13),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 131),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 1097)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_28059810762433 : Nat.Prime 28059810762433 := by
  apply lucas_primality 28059810762433 (5 : ZMod 28059810762433) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (2 * (2 * (2 * (3 * (41 * (53 * (67254877))))))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 41),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 53),
    Nat.prime_dvd_prime_iff_eq hq prime_67254877] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_162259276829213363391578010288127 : Nat.Prime 162259276829213363391578010288127 := by
  apply lucas_primality 162259276829213363391578010288127 (3 : ZMod 162259276829213363391578010288127) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (3 * (107 * (6361 * (69431 * (20394401 * (28059810762433)))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 107),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 6361),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 69431),
    Nat.prime_dvd_prime_iff_eq hq prime_20394401,
    Nat.prime_dvd_prime_iff_eq hq prime_28059810762433] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_246241 : Nat.Prime 246241 := by
  apply lucas_primality 246241 (11 : ZMod 246241) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (2 * (2 * (3 * (3 * (3 * (3 * (5 * (19)))))))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 19)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_279073 : Nat.Prime 279073 := by
  apply lucas_primality 279073 (10 : ZMod 279073) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (2 * (2 * (3 * (3 * (3 * (17 * (19))))))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 17),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 19)] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_745988807 : Nat.Prime 745988807 := by
  apply lucas_primality 745988807 (5 : ZMod 745988807) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (107 * (109 * (31981))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 107),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 109),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 31981)] at hd
  rcases hd with rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_521981 : Nat.Prime 521981 := by
  apply lucas_primality 521981 (2 : ZMod 521981) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (5 * (26099))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 26099)] at hd
  rcases hd with rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_88736771 : Nat.Prime 88736771 := by
  apply lucas_primality 88736771 (2 : ZMod 88736771) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (5 * (17 * (521981))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 17),
    Nat.prime_dvd_prime_iff_eq hq prime_521981] at hd
  rcases hd with rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_5895671065241 : Nat.Prime 5895671065241 := by
  apply lucas_primality 5895671065241 (6 : ZMod 5895671065241) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (5 * (11 * (151 * (88736771)))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 11),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 151),
    Nat.prime_dvd_prime_iff_eq hq prime_88736771] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_11791342130483 : Nat.Prime 11791342130483 := by
  apply lucas_primality 11791342130483 (2 : ZMod 11791342130483) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (5895671065241) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq prime_5895671065241] at hd
  rcases hd with rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_16910977804748891839 : Nat.Prime 16910977804748891839 := by
  apply lucas_primality 16910977804748891839 (3 : ZMod 16910977804748891839) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (3 * (3 * (3 * (3 * (3 * (13 * (227 * (11791342130483)))))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 13),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 227),
    Nat.prime_dvd_prime_iff_eq hq prime_11791342130483] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_870035986098720987332873 : Nat.Prime 870035986098720987332873 := by
  apply lucas_primality 870035986098720987332873 (3 : ZMod 870035986098720987332873) (by reduce_mod_char)
  intro q hq hd
  change q ∣ 2 * (2 * (2 * (59 * (109 * (16910977804748891839))))) at hd
  simp only [hq.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 59),
    Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 109),
    Nat.prime_dvd_prime_iff_eq hq prime_16910977804748891839] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel


private theorem gaps_1_28 {d p : ℕ} (hlo : 1 ≤ d) (hhi : d < 28)
    (hp : p.Prime) (hdiv : p * p ∣ 2 ^ d - 1) : p = 3 ∨ p = 5 ∨ p = 7 := by
  interval_cases d
  · have hle := Nat.le_of_dvd (by decide : 0 < 1) hdiv
    have := hp.two_le
    nlinarith
  · have hpdiv : p ∣ 3 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 at hpdiv
    simp only [
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3)] at hpdiv
    rcases hpdiv with rfl
    · decide +kernel
  · have hpdiv : p ∣ 7 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 7 at hpdiv
    simp only [
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)] at hpdiv
    rcases hpdiv with rfl
    · decide +kernel
  · have hpdiv : p ∣ 15 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (5) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5)] at hpdiv
    rcases hpdiv with rfl | rfl
    · decide +kernel
    · decide +kernel
  · have hpdiv : p ∣ 31 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 31 at hpdiv
    simp only [
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 31)] at hpdiv
    rcases hpdiv with rfl
    · exact False.elim ((by decide +kernel : ¬ 31 * 31 ∣ 31) hdiv)
  · have hpdiv : p ∣ 63 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (3 * (7)) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)] at hpdiv
    rcases hpdiv with rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · decide +kernel
  · have hpdiv : p ∣ 127 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 127 at hpdiv
    simp only [
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 127)] at hpdiv
    rcases hpdiv with rfl
    · exact False.elim ((by decide +kernel : ¬ 127 * 127 ∣ 127) hdiv)
  · have hpdiv : p ∣ 255 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (5 * (17)) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 17)] at hpdiv
    rcases hpdiv with rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 17 * 17 ∣ 255) hdiv)
  · have hpdiv : p ∣ 511 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 7 * (73) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 73)] at hpdiv
    rcases hpdiv with rfl | rfl
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 73 * 73 ∣ 511) hdiv)
  · have hpdiv : p ∣ 1023 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (11 * (31)) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 11),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 31)] at hpdiv
    rcases hpdiv with rfl | rfl | rfl
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 11 * 11 ∣ 1023) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 31 * 31 ∣ 1023) hdiv)
  · have hpdiv : p ∣ 2047 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 23 * (89) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 23),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 89)] at hpdiv
    rcases hpdiv with rfl | rfl
    · exact False.elim ((by decide +kernel : ¬ 23 * 23 ∣ 2047) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 89 * 89 ∣ 2047) hdiv)
  · have hpdiv : p ∣ 4095 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (3 * (5 * (7 * (13)))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 13)] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 13 * 13 ∣ 4095) hdiv)
  · have hpdiv : p ∣ 8191 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 8191 at hpdiv
    simp only [
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 8191)] at hpdiv
    rcases hpdiv with rfl
    · exact False.elim ((by decide +kernel : ¬ 8191 * 8191 ∣ 8191) hdiv)
  · have hpdiv : p ∣ 16383 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (43 * (127)) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 43),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 127)] at hpdiv
    rcases hpdiv with rfl | rfl | rfl
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 43 * 43 ∣ 16383) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 127 * 127 ∣ 16383) hdiv)
  · have hpdiv : p ∣ 32767 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 7 * (31 * (151)) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 31),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 151)] at hpdiv
    rcases hpdiv with rfl | rfl | rfl
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 31 * 31 ∣ 32767) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 151 * 151 ∣ 32767) hdiv)
  · have hpdiv : p ∣ 65535 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (5 * (17 * (257))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 17),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 257)] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 17 * 17 ∣ 65535) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 257 * 257 ∣ 65535) hdiv)
  · have hpdiv : p ∣ 131071 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 131071 at hpdiv
    simp only [
      Nat.prime_dvd_prime_iff_eq hp prime_131071] at hpdiv
    rcases hpdiv with rfl
    · exact False.elim ((by decide +kernel : ¬ 131071 * 131071 ∣ 131071) hdiv)
  · have hpdiv : p ∣ 262143 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (3 * (3 * (7 * (19 * (73))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 19),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 73)] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 19 * 19 ∣ 262143) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 73 * 73 ∣ 262143) hdiv)
  · have hpdiv : p ∣ 524287 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 524287 at hpdiv
    simp only [
      Nat.prime_dvd_prime_iff_eq hp prime_524287] at hpdiv
    rcases hpdiv with rfl
    · exact False.elim ((by decide +kernel : ¬ 524287 * 524287 ∣ 524287) hdiv)
  · have hpdiv : p ∣ 1048575 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (5 * (5 * (11 * (31 * (41))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 11),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 31),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 41)] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 11 * 11 ∣ 1048575) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 31 * 31 ∣ 1048575) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 41 * 41 ∣ 1048575) hdiv)
  · have hpdiv : p ∣ 2097151 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 7 * (7 * (127 * (337))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 127),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 337)] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 127 * 127 ∣ 2097151) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 337 * 337 ∣ 2097151) hdiv)
  · have hpdiv : p ∣ 4194303 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (23 * (89 * (683))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 23),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 89),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 683)] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 23 * 23 ∣ 4194303) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 89 * 89 ∣ 4194303) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 683 * 683 ∣ 4194303) hdiv)
  · have hpdiv : p ∣ 8388607 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 47 * (178481) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 47),
      Nat.prime_dvd_prime_iff_eq hp prime_178481] at hpdiv
    rcases hpdiv with rfl | rfl
    · exact False.elim ((by decide +kernel : ¬ 47 * 47 ∣ 8388607) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 178481 * 178481 ∣ 8388607) hdiv)
  · have hpdiv : p ∣ 16777215 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (3 * (5 * (7 * (13 * (17 * (241)))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 13),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 17),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 241)] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 13 * 13 ∣ 16777215) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 17 * 17 ∣ 16777215) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 241 * 241 ∣ 16777215) hdiv)
  · have hpdiv : p ∣ 33554431 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 31 * (601 * (1801)) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 31),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 601),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 1801)] at hpdiv
    rcases hpdiv with rfl | rfl | rfl
    · exact False.elim ((by decide +kernel : ¬ 31 * 31 ∣ 33554431) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 601 * 601 ∣ 33554431) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 1801 * 1801 ∣ 33554431) hdiv)
  · have hpdiv : p ∣ 67108863 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (2731 * (8191)) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 2731),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 8191)] at hpdiv
    rcases hpdiv with rfl | rfl | rfl
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 2731 * 2731 ∣ 67108863) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 8191 * 8191 ∣ 67108863) hdiv)
  · have hpdiv : p ∣ 134217727 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 7 * (73 * (262657)) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 73),
      Nat.prime_dvd_prime_iff_eq hp prime_262657] at hpdiv
    rcases hpdiv with rfl | rfl | rfl
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 73 * 73 ∣ 134217727) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 262657 * 262657 ∣ 134217727) hdiv)

private theorem gaps_28_55 {d p : ℕ} (hlo : 28 ≤ d) (hhi : d < 55)
    (hp : p.Prime) (hdiv : p * p ∣ 2 ^ d - 1) : p = 3 ∨ p = 5 ∨ p = 7 := by
  interval_cases d
  · have hpdiv : p ∣ 268435455 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (5 * (29 * (43 * (113 * (127))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 29),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 43),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 113),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 127)] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 29 * 29 ∣ 268435455) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 43 * 43 ∣ 268435455) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 113 * 113 ∣ 268435455) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 127 * 127 ∣ 268435455) hdiv)
  · have hpdiv : p ∣ 536870911 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 233 * (1103 * (2089)) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 233),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 1103),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 2089)] at hpdiv
    rcases hpdiv with rfl | rfl | rfl
    · exact False.elim ((by decide +kernel : ¬ 233 * 233 ∣ 536870911) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 1103 * 1103 ∣ 536870911) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 2089 * 2089 ∣ 536870911) hdiv)
  · have hpdiv : p ∣ 1073741823 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (3 * (7 * (11 * (31 * (151 * (331)))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 11),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 31),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 151),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 331)] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 11 * 11 ∣ 1073741823) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 31 * 31 ∣ 1073741823) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 151 * 151 ∣ 1073741823) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 331 * 331 ∣ 1073741823) hdiv)
  · have hpdiv : p ∣ 2147483647 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 2147483647 at hpdiv
    simp only [
      Nat.prime_dvd_prime_iff_eq hp prime_2147483647] at hpdiv
    rcases hpdiv with rfl
    · exact False.elim ((by decide +kernel : ¬ 2147483647 * 2147483647 ∣ 2147483647) hdiv)
  · have hpdiv : p ∣ 4294967295 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (5 * (17 * (257 * (65537)))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 17),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 257),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 65537)] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 17 * 17 ∣ 4294967295) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 257 * 257 ∣ 4294967295) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 65537 * 65537 ∣ 4294967295) hdiv)
  · have hpdiv : p ∣ 8589934591 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 7 * (23 * (89 * (599479))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 23),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 89),
      Nat.prime_dvd_prime_iff_eq hp prime_599479] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 23 * 23 ∣ 8589934591) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 89 * 89 ∣ 8589934591) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 599479 * 599479 ∣ 8589934591) hdiv)
  · have hpdiv : p ∣ 17179869183 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (43691 * (131071)) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 43691),
      Nat.prime_dvd_prime_iff_eq hp prime_131071] at hpdiv
    rcases hpdiv with rfl | rfl | rfl
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 43691 * 43691 ∣ 17179869183) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 131071 * 131071 ∣ 17179869183) hdiv)
  · have hpdiv : p ∣ 34359738367 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 31 * (71 * (127 * (122921))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 31),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 71),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 127),
      Nat.prime_dvd_prime_iff_eq hp prime_122921] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl
    · exact False.elim ((by decide +kernel : ¬ 31 * 31 ∣ 34359738367) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 71 * 71 ∣ 34359738367) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 127 * 127 ∣ 34359738367) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 122921 * 122921 ∣ 34359738367) hdiv)
  · have hpdiv : p ∣ 68719476735 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (3 * (3 * (5 * (7 * (13 * (19 * (37 * (73 * (109))))))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 13),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 19),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 37),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 73),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 109)] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 13 * 13 ∣ 68719476735) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 19 * 19 ∣ 68719476735) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 37 * 37 ∣ 68719476735) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 73 * 73 ∣ 68719476735) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 109 * 109 ∣ 68719476735) hdiv)
  · have hpdiv : p ∣ 137438953471 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 223 * (616318177) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 223),
      Nat.prime_dvd_prime_iff_eq hp prime_616318177] at hpdiv
    rcases hpdiv with rfl | rfl
    · exact False.elim ((by decide +kernel : ¬ 223 * 223 ∣ 137438953471) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 616318177 * 616318177 ∣ 137438953471) hdiv)
  · have hpdiv : p ∣ 274877906943 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (174763 * (524287)) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp prime_174763,
      Nat.prime_dvd_prime_iff_eq hp prime_524287] at hpdiv
    rcases hpdiv with rfl | rfl | rfl
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 174763 * 174763 ∣ 274877906943) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 524287 * 524287 ∣ 274877906943) hdiv)
  · have hpdiv : p ∣ 549755813887 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 7 * (79 * (8191 * (121369))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 79),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 8191),
      Nat.prime_dvd_prime_iff_eq hp prime_121369] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 79 * 79 ∣ 549755813887) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 8191 * 8191 ∣ 549755813887) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 121369 * 121369 ∣ 549755813887) hdiv)
  · have hpdiv : p ∣ 1099511627775 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (5 * (5 * (11 * (17 * (31 * (41 * (61681))))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 11),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 17),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 31),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 41),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 61681)] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 11 * 11 ∣ 1099511627775) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 17 * 17 ∣ 1099511627775) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 31 * 31 ∣ 1099511627775) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 41 * 41 ∣ 1099511627775) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 61681 * 61681 ∣ 1099511627775) hdiv)
  · have hpdiv : p ∣ 2199023255551 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 13367 * (164511353) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 13367),
      Nat.prime_dvd_prime_iff_eq hp prime_164511353] at hpdiv
    rcases hpdiv with rfl | rfl
    · exact False.elim ((by decide +kernel : ¬ 13367 * 13367 ∣ 2199023255551) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 164511353 * 164511353 ∣ 2199023255551) hdiv)
  · have hpdiv : p ∣ 4398046511103 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (3 * (7 * (7 * (43 * (127 * (337 * (5419))))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 43),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 127),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 337),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5419)] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 43 * 43 ∣ 4398046511103) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 127 * 127 ∣ 4398046511103) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 337 * 337 ∣ 4398046511103) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 5419 * 5419 ∣ 4398046511103) hdiv)
  · have hpdiv : p ∣ 8796093022207 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 431 * (9719 * (2099863)) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 431),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 9719),
      Nat.prime_dvd_prime_iff_eq hp prime_2099863] at hpdiv
    rcases hpdiv with rfl | rfl | rfl
    · exact False.elim ((by decide +kernel : ¬ 431 * 431 ∣ 8796093022207) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 9719 * 9719 ∣ 8796093022207) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 2099863 * 2099863 ∣ 8796093022207) hdiv)
  · have hpdiv : p ∣ 17592186044415 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (5 * (23 * (89 * (397 * (683 * (2113)))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 23),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 89),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 397),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 683),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 2113)] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 23 * 23 ∣ 17592186044415) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 89 * 89 ∣ 17592186044415) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 397 * 397 ∣ 17592186044415) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 683 * 683 ∣ 17592186044415) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 2113 * 2113 ∣ 17592186044415) hdiv)
  · have hpdiv : p ∣ 35184372088831 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 7 * (31 * (73 * (151 * (631 * (23311))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 31),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 73),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 151),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 631),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 23311)] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 31 * 31 ∣ 35184372088831) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 73 * 73 ∣ 35184372088831) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 151 * 151 ∣ 35184372088831) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 631 * 631 ∣ 35184372088831) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 23311 * 23311 ∣ 35184372088831) hdiv)
  · have hpdiv : p ∣ 70368744177663 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (47 * (178481 * (2796203))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 47),
      Nat.prime_dvd_prime_iff_eq hp prime_178481,
      Nat.prime_dvd_prime_iff_eq hp prime_2796203] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 47 * 47 ∣ 70368744177663) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 178481 * 178481 ∣ 70368744177663) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 2796203 * 2796203 ∣ 70368744177663) hdiv)
  · have hpdiv : p ∣ 140737488355327 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 2351 * (4513 * (13264529)) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 2351),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 4513),
      Nat.prime_dvd_prime_iff_eq hp prime_13264529] at hpdiv
    rcases hpdiv with rfl | rfl | rfl
    · exact False.elim ((by decide +kernel : ¬ 2351 * 2351 ∣ 140737488355327) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 4513 * 4513 ∣ 140737488355327) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 13264529 * 13264529 ∣ 140737488355327) hdiv)
  · have hpdiv : p ∣ 281474976710655 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (3 * (5 * (7 * (13 * (17 * (97 * (241 * (257 * (673))))))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 13),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 17),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 97),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 241),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 257),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 673)] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 13 * 13 ∣ 281474976710655) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 17 * 17 ∣ 281474976710655) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 97 * 97 ∣ 281474976710655) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 241 * 241 ∣ 281474976710655) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 257 * 257 ∣ 281474976710655) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 673 * 673 ∣ 281474976710655) hdiv)
  · have hpdiv : p ∣ 562949953421311 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 127 * (4432676798593) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 127),
      Nat.prime_dvd_prime_iff_eq hp prime_4432676798593] at hpdiv
    rcases hpdiv with rfl | rfl
    · exact False.elim ((by decide +kernel : ¬ 127 * 127 ∣ 562949953421311) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 4432676798593 * 4432676798593 ∣ 562949953421311) hdiv)
  · have hpdiv : p ∣ 1125899906842623 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (11 * (31 * (251 * (601 * (1801 * (4051)))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 11),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 31),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 251),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 601),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 1801),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 4051)] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 11 * 11 ∣ 1125899906842623) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 31 * 31 ∣ 1125899906842623) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 251 * 251 ∣ 1125899906842623) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 601 * 601 ∣ 1125899906842623) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 1801 * 1801 ∣ 1125899906842623) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 4051 * 4051 ∣ 1125899906842623) hdiv)
  · have hpdiv : p ∣ 2251799813685247 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 7 * (103 * (2143 * (11119 * (131071)))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 103),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 2143),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 11119),
      Nat.prime_dvd_prime_iff_eq hp prime_131071] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 103 * 103 ∣ 2251799813685247) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 2143 * 2143 ∣ 2251799813685247) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 11119 * 11119 ∣ 2251799813685247) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 131071 * 131071 ∣ 2251799813685247) hdiv)
  · have hpdiv : p ∣ 4503599627370495 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (5 * (53 * (157 * (1613 * (2731 * (8191)))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 53),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 157),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 1613),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 2731),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 8191)] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 53 * 53 ∣ 4503599627370495) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 157 * 157 ∣ 4503599627370495) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 1613 * 1613 ∣ 4503599627370495) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 2731 * 2731 ∣ 4503599627370495) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 8191 * 8191 ∣ 4503599627370495) hdiv)
  · have hpdiv : p ∣ 9007199254740991 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 6361 * (69431 * (20394401)) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 6361),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 69431),
      Nat.prime_dvd_prime_iff_eq hp prime_20394401] at hpdiv
    rcases hpdiv with rfl | rfl | rfl
    · exact False.elim ((by decide +kernel : ¬ 6361 * 6361 ∣ 9007199254740991) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 69431 * 69431 ∣ 9007199254740991) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 20394401 * 20394401 ∣ 9007199254740991) hdiv)
  · have hpdiv : p ∣ 18014398509481983 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (3 * (3 * (3 * (7 * (19 * (73 * (87211 * (262657)))))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 19),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 73),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 87211),
      Nat.prime_dvd_prime_iff_eq hp prime_262657] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 19 * 19 ∣ 18014398509481983) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 73 * 73 ∣ 18014398509481983) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 87211 * 87211 ∣ 18014398509481983) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 262657 * 262657 ∣ 18014398509481983) hdiv)

private theorem gaps_55_82 {d p : ℕ} (hlo : 55 ≤ d) (hhi : d < 82)
    (hp : p.Prime) (hdiv : p * p ∣ 2 ^ d - 1) : p = 3 ∨ p = 5 ∨ p = 7 := by
  interval_cases d
  · have hpdiv : p ∣ 36028797018963967 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 23 * (31 * (89 * (881 * (3191 * (201961))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 23),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 31),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 89),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 881),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3191),
      Nat.prime_dvd_prime_iff_eq hp prime_201961] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl
    · exact False.elim ((by decide +kernel : ¬ 23 * 23 ∣ 36028797018963967) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 31 * 31 ∣ 36028797018963967) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 89 * 89 ∣ 36028797018963967) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 881 * 881 ∣ 36028797018963967) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 3191 * 3191 ∣ 36028797018963967) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 201961 * 201961 ∣ 36028797018963967) hdiv)
  · have hpdiv : p ∣ 72057594037927935 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (5 * (17 * (29 * (43 * (113 * (127 * (15790321))))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 17),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 29),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 43),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 113),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 127),
      Nat.prime_dvd_prime_iff_eq hp prime_15790321] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 17 * 17 ∣ 72057594037927935) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 29 * 29 ∣ 72057594037927935) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 43 * 43 ∣ 72057594037927935) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 113 * 113 ∣ 72057594037927935) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 127 * 127 ∣ 72057594037927935) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 15790321 * 15790321 ∣ 72057594037927935) hdiv)
  · have hpdiv : p ∣ 144115188075855871 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 7 * (32377 * (524287 * (1212847))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 32377),
      Nat.prime_dvd_prime_iff_eq hp prime_524287,
      Nat.prime_dvd_prime_iff_eq hp prime_1212847] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 32377 * 32377 ∣ 144115188075855871) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 524287 * 524287 ∣ 144115188075855871) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 1212847 * 1212847 ∣ 144115188075855871) hdiv)
  · have hpdiv : p ∣ 288230376151711743 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (59 * (233 * (1103 * (2089 * (3033169))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 59),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 233),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 1103),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 2089),
      Nat.prime_dvd_prime_iff_eq hp prime_3033169] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 59 * 59 ∣ 288230376151711743) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 233 * 233 ∣ 288230376151711743) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 1103 * 1103 ∣ 288230376151711743) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 2089 * 2089 ∣ 288230376151711743) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 3033169 * 3033169 ∣ 288230376151711743) hdiv)
  · have hpdiv : p ∣ 576460752303423487 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 179951 * (3203431780337) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp prime_179951,
      Nat.prime_dvd_prime_iff_eq hp prime_3203431780337] at hpdiv
    rcases hpdiv with rfl | rfl
    · exact False.elim ((by decide +kernel : ¬ 179951 * 179951 ∣ 576460752303423487) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 3203431780337 * 3203431780337 ∣ 576460752303423487) hdiv)
  · have hpdiv : p ∣ 1152921504606846975 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (3 * (5 * (5 * (7 * (11 * (13 * (31 * (41 * (61 * (151 * (331 * (1321)))))))))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 11),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 13),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 31),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 41),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 61),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 151),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 331),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 1321)] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 11 * 11 ∣ 1152921504606846975) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 13 * 13 ∣ 1152921504606846975) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 31 * 31 ∣ 1152921504606846975) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 41 * 41 ∣ 1152921504606846975) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 61 * 61 ∣ 1152921504606846975) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 151 * 151 ∣ 1152921504606846975) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 331 * 331 ∣ 1152921504606846975) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 1321 * 1321 ∣ 1152921504606846975) hdiv)
  · have hpdiv : p ∣ 2305843009213693951 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 2305843009213693951 at hpdiv
    simp only [
      Nat.prime_dvd_prime_iff_eq hp prime_2305843009213693951] at hpdiv
    rcases hpdiv with rfl
    · exact False.elim ((by decide +kernel : ¬ 2305843009213693951 * 2305843009213693951 ∣ 2305843009213693951) hdiv)
  · have hpdiv : p ∣ 4611686018427387903 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (715827883 * (2147483647)) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp prime_715827883,
      Nat.prime_dvd_prime_iff_eq hp prime_2147483647] at hpdiv
    rcases hpdiv with rfl | rfl | rfl
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 715827883 * 715827883 ∣ 4611686018427387903) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 2147483647 * 2147483647 ∣ 4611686018427387903) hdiv)
  · have hpdiv : p ∣ 9223372036854775807 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 7 * (7 * (73 * (127 * (337 * (92737 * (649657)))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 73),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 127),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 337),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 92737),
      Nat.prime_dvd_prime_iff_eq hp prime_649657] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 73 * 73 ∣ 9223372036854775807) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 127 * 127 ∣ 9223372036854775807) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 337 * 337 ∣ 9223372036854775807) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 92737 * 92737 ∣ 9223372036854775807) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 649657 * 649657 ∣ 9223372036854775807) hdiv)
  · have hpdiv : p ∣ 18446744073709551615 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (5 * (17 * (257 * (641 * (65537 * (6700417)))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 17),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 257),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 641),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 65537),
      Nat.prime_dvd_prime_iff_eq hp prime_6700417] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 17 * 17 ∣ 18446744073709551615) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 257 * 257 ∣ 18446744073709551615) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 641 * 641 ∣ 18446744073709551615) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 65537 * 65537 ∣ 18446744073709551615) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 6700417 * 6700417 ∣ 18446744073709551615) hdiv)
  · have hpdiv : p ∣ 36893488147419103231 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 31 * (8191 * (145295143558111)) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 31),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 8191),
      Nat.prime_dvd_prime_iff_eq hp prime_145295143558111] at hpdiv
    rcases hpdiv with rfl | rfl | rfl
    · exact False.elim ((by decide +kernel : ¬ 31 * 31 ∣ 36893488147419103231) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 8191 * 8191 ∣ 36893488147419103231) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 145295143558111 * 145295143558111 ∣ 36893488147419103231) hdiv)
  · have hpdiv : p ∣ 73786976294838206463 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (3 * (7 * (23 * (67 * (89 * (683 * (20857 * (599479)))))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 23),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 67),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 89),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 683),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 20857),
      Nat.prime_dvd_prime_iff_eq hp prime_599479] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 23 * 23 ∣ 73786976294838206463) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 67 * 67 ∣ 73786976294838206463) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 89 * 89 ∣ 73786976294838206463) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 683 * 683 ∣ 73786976294838206463) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 20857 * 20857 ∣ 73786976294838206463) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 599479 * 599479 ∣ 73786976294838206463) hdiv)
  · have hpdiv : p ∣ 147573952589676412927 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 193707721 * (761838257287) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp prime_193707721,
      Nat.prime_dvd_prime_iff_eq hp prime_761838257287] at hpdiv
    rcases hpdiv with rfl | rfl
    · exact False.elim ((by decide +kernel : ¬ 193707721 * 193707721 ∣ 147573952589676412927) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 761838257287 * 761838257287 ∣ 147573952589676412927) hdiv)
  · have hpdiv : p ∣ 295147905179352825855 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (5 * (137 * (953 * (26317 * (43691 * (131071)))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 137),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 953),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 26317),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 43691),
      Nat.prime_dvd_prime_iff_eq hp prime_131071] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 137 * 137 ∣ 295147905179352825855) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 953 * 953 ∣ 295147905179352825855) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 26317 * 26317 ∣ 295147905179352825855) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 43691 * 43691 ∣ 295147905179352825855) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 131071 * 131071 ∣ 295147905179352825855) hdiv)
  · have hpdiv : p ∣ 590295810358705651711 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 7 * (47 * (178481 * (10052678938039))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 47),
      Nat.prime_dvd_prime_iff_eq hp prime_178481,
      Nat.prime_dvd_prime_iff_eq hp prime_10052678938039] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 47 * 47 ∣ 590295810358705651711) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 178481 * 178481 ∣ 590295810358705651711) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 10052678938039 * 10052678938039 ∣ 590295810358705651711) hdiv)
  · have hpdiv : p ∣ 1180591620717411303423 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (11 * (31 * (43 * (71 * (127 * (281 * (86171 * (122921)))))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 11),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 31),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 43),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 71),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 127),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 281),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 86171),
      Nat.prime_dvd_prime_iff_eq hp prime_122921] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 11 * 11 ∣ 1180591620717411303423) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 31 * 31 ∣ 1180591620717411303423) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 43 * 43 ∣ 1180591620717411303423) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 71 * 71 ∣ 1180591620717411303423) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 127 * 127 ∣ 1180591620717411303423) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 281 * 281 ∣ 1180591620717411303423) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 86171 * 86171 ∣ 1180591620717411303423) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 122921 * 122921 ∣ 1180591620717411303423) hdiv)
  · have hpdiv : p ∣ 2361183241434822606847 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 228479 * (48544121 * (212885833)) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp prime_228479,
      Nat.prime_dvd_prime_iff_eq hp prime_48544121,
      Nat.prime_dvd_prime_iff_eq hp prime_212885833] at hpdiv
    rcases hpdiv with rfl | rfl | rfl
    · exact False.elim ((by decide +kernel : ¬ 228479 * 228479 ∣ 2361183241434822606847) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 48544121 * 48544121 ∣ 2361183241434822606847) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 212885833 * 212885833 ∣ 2361183241434822606847) hdiv)
  · have hpdiv : p ∣ 4722366482869645213695 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (3 * (3 * (5 * (7 * (13 * (17 * (19 * (37 * (73 * (109 * (241 * (433 * (38737))))))))))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 13),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 17),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 19),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 37),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 73),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 109),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 241),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 433),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 38737)] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 13 * 13 ∣ 4722366482869645213695) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 17 * 17 ∣ 4722366482869645213695) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 19 * 19 ∣ 4722366482869645213695) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 37 * 37 ∣ 4722366482869645213695) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 73 * 73 ∣ 4722366482869645213695) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 109 * 109 ∣ 4722366482869645213695) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 241 * 241 ∣ 4722366482869645213695) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 433 * 433 ∣ 4722366482869645213695) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 38737 * 38737 ∣ 4722366482869645213695) hdiv)
  · have hpdiv : p ∣ 9444732965739290427391 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 439 * (2298041 * (9361973132609)) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 439),
      Nat.prime_dvd_prime_iff_eq hp prime_2298041,
      Nat.prime_dvd_prime_iff_eq hp prime_9361973132609] at hpdiv
    rcases hpdiv with rfl | rfl | rfl
    · exact False.elim ((by decide +kernel : ¬ 439 * 439 ∣ 9444732965739290427391) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 2298041 * 2298041 ∣ 9444732965739290427391) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 9361973132609 * 9361973132609 ∣ 9444732965739290427391) hdiv)
  · have hpdiv : p ∣ 18889465931478580854783 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (223 * (1777 * (25781083 * (616318177)))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 223),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 1777),
      Nat.prime_dvd_prime_iff_eq hp prime_25781083,
      Nat.prime_dvd_prime_iff_eq hp prime_616318177] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 223 * 223 ∣ 18889465931478580854783) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 1777 * 1777 ∣ 18889465931478580854783) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 25781083 * 25781083 ∣ 18889465931478580854783) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 616318177 * 616318177 ∣ 18889465931478580854783) hdiv)
  · have hpdiv : p ∣ 37778931862957161709567 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 7 * (31 * (151 * (601 * (1801 * (100801 * (10567201)))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 31),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 151),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 601),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 1801),
      Nat.prime_dvd_prime_iff_eq hp prime_100801,
      Nat.prime_dvd_prime_iff_eq hp prime_10567201] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 31 * 31 ∣ 37778931862957161709567) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 151 * 151 ∣ 37778931862957161709567) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 601 * 601 ∣ 37778931862957161709567) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 1801 * 1801 ∣ 37778931862957161709567) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 100801 * 100801 ∣ 37778931862957161709567) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 10567201 * 10567201 ∣ 37778931862957161709567) hdiv)
  · have hpdiv : p ∣ 75557863725914323419135 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (5 * (229 * (457 * (174763 * (524287 * (525313)))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 229),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 457),
      Nat.prime_dvd_prime_iff_eq hp prime_174763,
      Nat.prime_dvd_prime_iff_eq hp prime_524287,
      Nat.prime_dvd_prime_iff_eq hp prime_525313] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 229 * 229 ∣ 75557863725914323419135) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 457 * 457 ∣ 75557863725914323419135) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 174763 * 174763 ∣ 75557863725914323419135) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 524287 * 524287 ∣ 75557863725914323419135) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 525313 * 525313 ∣ 75557863725914323419135) hdiv)
  · have hpdiv : p ∣ 151115727451828646838271 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 23 * (89 * (127 * (581283643249112959))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 23),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 89),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 127),
      Nat.prime_dvd_prime_iff_eq hp prime_581283643249112959] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl
    · exact False.elim ((by decide +kernel : ¬ 23 * 23 ∣ 151115727451828646838271) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 89 * 89 ∣ 151115727451828646838271) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 127 * 127 ∣ 151115727451828646838271) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 581283643249112959 * 581283643249112959 ∣ 151115727451828646838271) hdiv)
  · have hpdiv : p ∣ 302231454903657293676543 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (3 * (7 * (79 * (2731 * (8191 * (121369 * (22366891))))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 79),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 2731),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 8191),
      Nat.prime_dvd_prime_iff_eq hp prime_121369,
      Nat.prime_dvd_prime_iff_eq hp prime_22366891] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 79 * 79 ∣ 302231454903657293676543) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 2731 * 2731 ∣ 302231454903657293676543) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 8191 * 8191 ∣ 302231454903657293676543) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 121369 * 121369 ∣ 302231454903657293676543) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 22366891 * 22366891 ∣ 302231454903657293676543) hdiv)
  · have hpdiv : p ∣ 604462909807314587353087 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 2687 * (202029703 * (1113491139767)) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 2687),
      Nat.prime_dvd_prime_iff_eq hp prime_202029703,
      Nat.prime_dvd_prime_iff_eq hp prime_1113491139767] at hpdiv
    rcases hpdiv with rfl | rfl | rfl
    · exact False.elim ((by decide +kernel : ¬ 2687 * 2687 ∣ 604462909807314587353087) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 202029703 * 202029703 ∣ 604462909807314587353087) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 1113491139767 * 1113491139767 ∣ 604462909807314587353087) hdiv)
  · have hpdiv : p ∣ 1208925819614629174706175 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (5 * (5 * (11 * (17 * (31 * (41 * (257 * (61681 * (4278255361))))))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 11),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 17),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 31),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 41),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 257),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 61681),
      Nat.prime_dvd_prime_iff_eq hp prime_4278255361] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 11 * 11 ∣ 1208925819614629174706175) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 17 * 17 ∣ 1208925819614629174706175) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 31 * 31 ∣ 1208925819614629174706175) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 41 * 41 ∣ 1208925819614629174706175) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 257 * 257 ∣ 1208925819614629174706175) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 61681 * 61681 ∣ 1208925819614629174706175) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 4278255361 * 4278255361 ∣ 1208925819614629174706175) hdiv)
  · have hpdiv : p ∣ 2417851639229258349412351 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 7 * (73 * (2593 * (71119 * (262657 * (97685839))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 73),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 2593),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 71119),
      Nat.prime_dvd_prime_iff_eq hp prime_262657,
      Nat.prime_dvd_prime_iff_eq hp prime_97685839] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 73 * 73 ∣ 2417851639229258349412351) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 2593 * 2593 ∣ 2417851639229258349412351) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 71119 * 71119 ∣ 2417851639229258349412351) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 262657 * 262657 ∣ 2417851639229258349412351) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 97685839 * 97685839 ∣ 2417851639229258349412351) hdiv)

private theorem gaps_82_110 {d p : ℕ} (hlo : 82 ≤ d) (hhi : d < 110)
    (hp : p.Prime) (hdiv : p * p ∣ 2 ^ d - 1) : p = 3 ∨ p = 5 ∨ p = 7 := by
  interval_cases d
  · have hpdiv : p ∣ 4835703278458516698824703 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (83 * (13367 * (164511353 * (8831418697)))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 83),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 13367),
      Nat.prime_dvd_prime_iff_eq hp prime_164511353,
      Nat.prime_dvd_prime_iff_eq hp prime_8831418697] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 83 * 83 ∣ 4835703278458516698824703) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 13367 * 13367 ∣ 4835703278458516698824703) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 164511353 * 164511353 ∣ 4835703278458516698824703) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 8831418697 * 8831418697 ∣ 4835703278458516698824703) hdiv)
  · have hpdiv : p ∣ 9671406556917033397649407 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 167 * (57912614113275649087721) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 167),
      Nat.prime_dvd_prime_iff_eq hp prime_57912614113275649087721] at hpdiv
    rcases hpdiv with rfl | rfl
    · exact False.elim ((by decide +kernel : ¬ 167 * 167 ∣ 9671406556917033397649407) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 57912614113275649087721 * 57912614113275649087721 ∣ 9671406556917033397649407) hdiv)
  · have hpdiv : p ∣ 19342813113834066795298815 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (3 * (5 * (7 * (7 * (13 * (29 * (43 * (113 * (127 * (337 * (1429 * (5419 * (14449))))))))))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 13),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 29),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 43),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 113),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 127),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 337),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 1429),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5419),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 14449)] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 13 * 13 ∣ 19342813113834066795298815) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 29 * 29 ∣ 19342813113834066795298815) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 43 * 43 ∣ 19342813113834066795298815) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 113 * 113 ∣ 19342813113834066795298815) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 127 * 127 ∣ 19342813113834066795298815) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 337 * 337 ∣ 19342813113834066795298815) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 1429 * 1429 ∣ 19342813113834066795298815) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 5419 * 5419 ∣ 19342813113834066795298815) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 14449 * 14449 ∣ 19342813113834066795298815) hdiv)
  · have hpdiv : p ∣ 38685626227668133590597631 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 31 * (131071 * (9520972806333758431)) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 31),
      Nat.prime_dvd_prime_iff_eq hp prime_131071,
      Nat.prime_dvd_prime_iff_eq hp prime_9520972806333758431] at hpdiv
    rcases hpdiv with rfl | rfl | rfl
    · exact False.elim ((by decide +kernel : ¬ 31 * 31 ∣ 38685626227668133590597631) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 131071 * 131071 ∣ 38685626227668133590597631) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 9520972806333758431 * 9520972806333758431 ∣ 38685626227668133590597631) hdiv)
  · have hpdiv : p ∣ 77371252455336267181195263 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (431 * (9719 * (2099863 * (2932031007403)))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 431),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 9719),
      Nat.prime_dvd_prime_iff_eq hp prime_2099863,
      Nat.prime_dvd_prime_iff_eq hp prime_2932031007403] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 431 * 431 ∣ 77371252455336267181195263) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 9719 * 9719 ∣ 77371252455336267181195263) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 2099863 * 2099863 ∣ 77371252455336267181195263) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 2932031007403 * 2932031007403 ∣ 77371252455336267181195263) hdiv)
  · have hpdiv : p ∣ 154742504910672534362390527 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 7 * (233 * (1103 * (2089 * (4177 * (9857737155463))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 233),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 1103),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 2089),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 4177),
      Nat.prime_dvd_prime_iff_eq hp prime_9857737155463] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 233 * 233 ∣ 154742504910672534362390527) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 1103 * 1103 ∣ 154742504910672534362390527) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 2089 * 2089 ∣ 154742504910672534362390527) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 4177 * 4177 ∣ 154742504910672534362390527) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 9857737155463 * 9857737155463 ∣ 154742504910672534362390527) hdiv)
  · have hpdiv : p ∣ 309485009821345068724781055 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (5 * (17 * (23 * (89 * (353 * (397 * (683 * (2113 * (2931542417))))))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 17),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 23),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 89),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 353),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 397),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 683),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 2113),
      Nat.prime_dvd_prime_iff_eq hp prime_2931542417] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 17 * 17 ∣ 309485009821345068724781055) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 23 * 23 ∣ 309485009821345068724781055) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 89 * 89 ∣ 309485009821345068724781055) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 353 * 353 ∣ 309485009821345068724781055) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 397 * 397 ∣ 309485009821345068724781055) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 683 * 683 ∣ 309485009821345068724781055) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 2113 * 2113 ∣ 309485009821345068724781055) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 2931542417 * 2931542417 ∣ 309485009821345068724781055) hdiv)
  · have hpdiv : p ∣ 618970019642690137449562111 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 618970019642690137449562111 at hpdiv
    simp only [
      Nat.prime_dvd_prime_iff_eq hp prime_618970019642690137449562111] at hpdiv
    rcases hpdiv with rfl
    · exact False.elim ((by decide +kernel : ¬ 618970019642690137449562111 * 618970019642690137449562111 ∣ 618970019642690137449562111) hdiv)
  · have hpdiv : p ∣ 1237940039285380274899124223 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (3 * (3 * (7 * (11 * (19 * (31 * (73 * (151 * (331 * (631 * (23311 * (18837001)))))))))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 11),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 19),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 31),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 73),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 151),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 331),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 631),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 23311),
      Nat.prime_dvd_prime_iff_eq hp prime_18837001] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 11 * 11 ∣ 1237940039285380274899124223) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 19 * 19 ∣ 1237940039285380274899124223) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 31 * 31 ∣ 1237940039285380274899124223) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 73 * 73 ∣ 1237940039285380274899124223) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 151 * 151 ∣ 1237940039285380274899124223) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 331 * 331 ∣ 1237940039285380274899124223) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 631 * 631 ∣ 1237940039285380274899124223) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 23311 * 23311 ∣ 1237940039285380274899124223) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 18837001 * 18837001 ∣ 1237940039285380274899124223) hdiv)
  · have hpdiv : p ∣ 2475880078570760549798248447 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 127 * (911 * (8191 * (112901153 * (23140471537)))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 127),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 911),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 8191),
      Nat.prime_dvd_prime_iff_eq hp prime_112901153,
      Nat.prime_dvd_prime_iff_eq hp prime_23140471537] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl
    · exact False.elim ((by decide +kernel : ¬ 127 * 127 ∣ 2475880078570760549798248447) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 911 * 911 ∣ 2475880078570760549798248447) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 8191 * 8191 ∣ 2475880078570760549798248447) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 112901153 * 112901153 ∣ 2475880078570760549798248447) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 23140471537 * 23140471537 ∣ 2475880078570760549798248447) hdiv)
  · have hpdiv : p ∣ 4951760157141521099596496895 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (5 * (47 * (277 * (1013 * (1657 * (30269 * (178481 * (2796203)))))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 47),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 277),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 1013),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 1657),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 30269),
      Nat.prime_dvd_prime_iff_eq hp prime_178481,
      Nat.prime_dvd_prime_iff_eq hp prime_2796203] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 47 * 47 ∣ 4951760157141521099596496895) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 277 * 277 ∣ 4951760157141521099596496895) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 1013 * 1013 ∣ 4951760157141521099596496895) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 1657 * 1657 ∣ 4951760157141521099596496895) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 30269 * 30269 ∣ 4951760157141521099596496895) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 178481 * 178481 ∣ 4951760157141521099596496895) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 2796203 * 2796203 ∣ 4951760157141521099596496895) hdiv)
  · have hpdiv : p ∣ 9903520314283042199192993791 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 7 * (2147483647 * (658812288653553079)) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7),
      Nat.prime_dvd_prime_iff_eq hp prime_2147483647,
      Nat.prime_dvd_prime_iff_eq hp prime_658812288653553079] at hpdiv
    rcases hpdiv with rfl | rfl | rfl
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 2147483647 * 2147483647 ∣ 9903520314283042199192993791) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 658812288653553079 * 658812288653553079 ∣ 9903520314283042199192993791) hdiv)
  · have hpdiv : p ∣ 19807040628566084398385987583 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (283 * (2351 * (4513 * (13264529 * (165768537521))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 283),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 2351),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 4513),
      Nat.prime_dvd_prime_iff_eq hp prime_13264529,
      Nat.prime_dvd_prime_iff_eq hp prime_165768537521] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 283 * 283 ∣ 19807040628566084398385987583) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 2351 * 2351 ∣ 19807040628566084398385987583) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 4513 * 4513 ∣ 19807040628566084398385987583) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 13264529 * 13264529 ∣ 19807040628566084398385987583) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 165768537521 * 165768537521 ∣ 19807040628566084398385987583) hdiv)
  · have hpdiv : p ∣ 39614081257132168796771975167 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 31 * (191 * (524287 * (420778751 * (30327152671)))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 31),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 191),
      Nat.prime_dvd_prime_iff_eq hp prime_524287,
      Nat.prime_dvd_prime_iff_eq hp prime_420778751,
      Nat.prime_dvd_prime_iff_eq hp prime_30327152671] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl
    · exact False.elim ((by decide +kernel : ¬ 31 * 31 ∣ 39614081257132168796771975167) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 191 * 191 ∣ 39614081257132168796771975167) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 524287 * 524287 ∣ 39614081257132168796771975167) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 420778751 * 420778751 ∣ 39614081257132168796771975167) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 30327152671 * 30327152671 ∣ 39614081257132168796771975167) hdiv)
  · have hpdiv : p ∣ 79228162514264337593543950335 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (3 * (5 * (7 * (13 * (17 * (97 * (193 * (241 * (257 * (673 * (65537 * (22253377)))))))))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 13),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 17),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 97),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 193),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 241),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 257),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 673),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 65537),
      Nat.prime_dvd_prime_iff_eq hp prime_22253377] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 13 * 13 ∣ 79228162514264337593543950335) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 17 * 17 ∣ 79228162514264337593543950335) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 97 * 97 ∣ 79228162514264337593543950335) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 193 * 193 ∣ 79228162514264337593543950335) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 241 * 241 ∣ 79228162514264337593543950335) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 257 * 257 ∣ 79228162514264337593543950335) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 673 * 673 ∣ 79228162514264337593543950335) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 65537 * 65537 ∣ 79228162514264337593543950335) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 22253377 * 22253377 ∣ 79228162514264337593543950335) hdiv)
  · have hpdiv : p ∣ 158456325028528675187087900671 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 11447 * (13842607235828485645766393) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 11447),
      Nat.prime_dvd_prime_iff_eq hp prime_13842607235828485645766393] at hpdiv
    rcases hpdiv with rfl | rfl
    · exact False.elim ((by decide +kernel : ¬ 11447 * 11447 ∣ 158456325028528675187087900671) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 13842607235828485645766393 * 13842607235828485645766393 ∣ 158456325028528675187087900671) hdiv)
  · have hpdiv : p ∣ 316912650057057350374175801343 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (43 * (127 * (4363953127297 * (4432676798593)))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 43),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 127),
      Nat.prime_dvd_prime_iff_eq hp prime_4363953127297,
      Nat.prime_dvd_prime_iff_eq hp prime_4432676798593] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 43 * 43 ∣ 316912650057057350374175801343) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 127 * 127 ∣ 316912650057057350374175801343) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 4363953127297 * 4363953127297 ∣ 316912650057057350374175801343) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 4432676798593 * 4432676798593 ∣ 316912650057057350374175801343) hdiv)
  · have hpdiv : p ∣ 633825300114114700748351602687 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 7 * (23 * (73 * (89 * (199 * (153649 * (599479 * (33057806959))))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 23),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 73),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 89),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 199),
      Nat.prime_dvd_prime_iff_eq hp prime_153649,
      Nat.prime_dvd_prime_iff_eq hp prime_599479,
      Nat.prime_dvd_prime_iff_eq hp prime_33057806959] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 23 * 23 ∣ 633825300114114700748351602687) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 73 * 73 ∣ 633825300114114700748351602687) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 89 * 89 ∣ 633825300114114700748351602687) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 199 * 199 ∣ 633825300114114700748351602687) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 153649 * 153649 ∣ 633825300114114700748351602687) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 599479 * 599479 ∣ 633825300114114700748351602687) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 33057806959 * 33057806959 ∣ 633825300114114700748351602687) hdiv)
  · have hpdiv : p ∣ 1267650600228229401496703205375 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (5 * (5 * (5 * (11 * (31 * (41 * (101 * (251 * (601 * (1801 * (4051 * (8101 * (268501))))))))))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 11),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 31),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 41),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 101),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 251),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 601),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 1801),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 4051),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 8101),
      Nat.prime_dvd_prime_iff_eq hp prime_268501] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 11 * 11 ∣ 1267650600228229401496703205375) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 31 * 31 ∣ 1267650600228229401496703205375) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 41 * 41 ∣ 1267650600228229401496703205375) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 101 * 101 ∣ 1267650600228229401496703205375) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 251 * 251 ∣ 1267650600228229401496703205375) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 601 * 601 ∣ 1267650600228229401496703205375) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 1801 * 1801 ∣ 1267650600228229401496703205375) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 4051 * 4051 ∣ 1267650600228229401496703205375) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 8101 * 8101 ∣ 1267650600228229401496703205375) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 268501 * 268501 ∣ 1267650600228229401496703205375) hdiv)
  · have hpdiv : p ∣ 2535301200456458802993406410751 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 7432339208719 * (341117531003194129) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp prime_7432339208719,
      Nat.prime_dvd_prime_iff_eq hp prime_341117531003194129] at hpdiv
    rcases hpdiv with rfl | rfl
    · exact False.elim ((by decide +kernel : ¬ 7432339208719 * 7432339208719 ∣ 2535301200456458802993406410751) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 341117531003194129 * 341117531003194129 ∣ 2535301200456458802993406410751) hdiv)
  · have hpdiv : p ∣ 5070602400912917605986812821503 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (3 * (7 * (103 * (307 * (2143 * (2857 * (6529 * (11119 * (43691 * (131071)))))))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 103),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 307),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 2143),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 2857),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 6529),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 11119),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 43691),
      Nat.prime_dvd_prime_iff_eq hp prime_131071] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 103 * 103 ∣ 5070602400912917605986812821503) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 307 * 307 ∣ 5070602400912917605986812821503) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 2143 * 2143 ∣ 5070602400912917605986812821503) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 2857 * 2857 ∣ 5070602400912917605986812821503) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 6529 * 6529 ∣ 5070602400912917605986812821503) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 11119 * 11119 ∣ 5070602400912917605986812821503) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 43691 * 43691 ∣ 5070602400912917605986812821503) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 131071 * 131071 ∣ 5070602400912917605986812821503) hdiv)
  · have hpdiv : p ∣ 10141204801825835211973625643007 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 2550183799 * (3976656429941438590393) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp prime_2550183799,
      Nat.prime_dvd_prime_iff_eq hp prime_3976656429941438590393] at hpdiv
    rcases hpdiv with rfl | rfl
    · exact False.elim ((by decide +kernel : ¬ 2550183799 * 2550183799 ∣ 10141204801825835211973625643007) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 3976656429941438590393 * 3976656429941438590393 ∣ 10141204801825835211973625643007) hdiv)
  · have hpdiv : p ∣ 20282409603651670423947251286015 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (5 * (17 * (53 * (157 * (1613 * (2731 * (8191 * (858001 * (308761441))))))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 17),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 53),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 157),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 1613),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 2731),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 8191),
      Nat.prime_dvd_prime_iff_eq hp prime_858001,
      Nat.prime_dvd_prime_iff_eq hp prime_308761441] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 17 * 17 ∣ 20282409603651670423947251286015) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 53 * 53 ∣ 20282409603651670423947251286015) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 157 * 157 ∣ 20282409603651670423947251286015) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 1613 * 1613 ∣ 20282409603651670423947251286015) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 2731 * 2731 ∣ 20282409603651670423947251286015) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 8191 * 8191 ∣ 20282409603651670423947251286015) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 858001 * 858001 ∣ 20282409603651670423947251286015) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 308761441 * 308761441 ∣ 20282409603651670423947251286015) hdiv)
  · have hpdiv : p ∣ 40564819207303340847894502572031 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 7 * (7 * (31 * (71 * (127 * (151 * (337 * (29191 * (106681 * (122921 * (152041)))))))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 31),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 71),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 127),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 151),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 337),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 29191),
      Nat.prime_dvd_prime_iff_eq hp prime_106681,
      Nat.prime_dvd_prime_iff_eq hp prime_122921,
      Nat.prime_dvd_prime_iff_eq hp prime_152041] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 31 * 31 ∣ 40564819207303340847894502572031) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 71 * 71 ∣ 40564819207303340847894502572031) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 127 * 127 ∣ 40564819207303340847894502572031) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 151 * 151 ∣ 40564819207303340847894502572031) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 337 * 337 ∣ 40564819207303340847894502572031) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 29191 * 29191 ∣ 40564819207303340847894502572031) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 106681 * 106681 ∣ 40564819207303340847894502572031) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 122921 * 122921 ∣ 40564819207303340847894502572031) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 152041 * 152041 ∣ 40564819207303340847894502572031) hdiv)
  · have hpdiv : p ∣ 81129638414606681695789005144063 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (107 * (6361 * (69431 * (20394401 * (28059810762433))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 107),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 6361),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 69431),
      Nat.prime_dvd_prime_iff_eq hp prime_20394401,
      Nat.prime_dvd_prime_iff_eq hp prime_28059810762433] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 107 * 107 ∣ 81129638414606681695789005144063) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 6361 * 6361 ∣ 81129638414606681695789005144063) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 69431 * 69431 ∣ 81129638414606681695789005144063) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 20394401 * 20394401 ∣ 81129638414606681695789005144063) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 28059810762433 * 28059810762433 ∣ 81129638414606681695789005144063) hdiv)
  · have hpdiv : p ∣ 162259276829213363391578010288127 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 162259276829213363391578010288127 at hpdiv
    simp only [
      Nat.prime_dvd_prime_iff_eq hp prime_162259276829213363391578010288127] at hpdiv
    rcases hpdiv with rfl
    · exact False.elim ((by decide +kernel : ¬ 162259276829213363391578010288127 * 162259276829213363391578010288127 ∣ 162259276829213363391578010288127) hdiv)
  · have hpdiv : p ∣ 324518553658426726783156020576255 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 3 * (3 * (3 * (3 * (5 * (7 * (13 * (19 * (37 * (73 * (109 * (87211 * (246241 * (262657 * (279073)))))))))))))) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 3),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 13),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 19),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 37),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 73),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 109),
      Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 87211),
      Nat.prime_dvd_prime_iff_eq hp prime_246241,
      Nat.prime_dvd_prime_iff_eq hp prime_262657,
      Nat.prime_dvd_prime_iff_eq hp prime_279073] at hpdiv
    rcases hpdiv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · exact False.elim ((by decide +kernel : ¬ 13 * 13 ∣ 324518553658426726783156020576255) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 19 * 19 ∣ 324518553658426726783156020576255) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 37 * 37 ∣ 324518553658426726783156020576255) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 73 * 73 ∣ 324518553658426726783156020576255) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 109 * 109 ∣ 324518553658426726783156020576255) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 87211 * 87211 ∣ 324518553658426726783156020576255) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 246241 * 246241 ∣ 324518553658426726783156020576255) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 262657 * 262657 ∣ 324518553658426726783156020576255) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 279073 * 279073 ∣ 324518553658426726783156020576255) hdiv)
  · have hpdiv : p ∣ 649037107316853453566312041152511 := dvd_trans (dvd_mul_right p p) hdiv
    change p ∣ 745988807 * (870035986098720987332873) at hpdiv
    simp only [hp.dvd_mul,
      Nat.prime_dvd_prime_iff_eq hp prime_745988807,
      Nat.prime_dvd_prime_iff_eq hp prime_870035986098720987332873] at hpdiv
    rcases hpdiv with rfl | rfl
    · exact False.elim ((by decide +kernel : ¬ 745988807 * 745988807 ∣ 649037107316853453566312041152511) hdiv)
    · exact False.elim ((by decide +kernel : ¬ 870035986098720987332873 * 870035986098720987332873 ∣ 649037107316853453566312041152511) hdiv)

/-- Exact finite certificate: for exponent gaps 1 through 109, only 3, 5, and 7 can
occur as prime-square divisors of the corresponding Mersenne number. -/
theorem prime_square_mersenne_lt_110 {d p : ℕ} (hd0 : 0 < d) (hd : d < 110)
    (hp : p.Prime) (hdiv : p * p ∣ 2 ^ d - 1) : p = 3 ∨ p = 5 ∨ p = 7 := by
  by_cases h₁ : d < 28
  · exact gaps_1_28 (by omega) h₁ hp hdiv
  by_cases h₂ : d < 55
  · exact gaps_28_55 (by omega) h₂ hp hdiv
  by_cases h₃ : d < 82
  · exact gaps_55_82 (by omega) h₃ hp hdiv
  exact gaps_82_110 (by omega) hd hp hdiv

end Contribution.Erdos11Certificates.ShortCollisions


/-!
# Separation of large prime-square obstructions

The finite Mersenne certificate proves that any prime at least eleven
can obstruct at most one exponent in a window containing at most 110 exponents.
This does not bound the number of different primes in a complete certificate.
-/

namespace Contribution.Erdos11Certificates.ShortCollisions

/-- Two obstructions less than 110 exponents apart cannot share a prime at least eleven. -/
theorem no_repeated_large_prime {n a b p : ℕ} (hp : p.Prime) (hlarge : 11 ≤ p)
    (hab : a < b) (hwidth : b < a + 110) (ha : 2 ^ a ≤ n) (hb : 2 ^ b ≤ n)
    (hda : p * p ∣ n - 2 ^ a) (hdb : p * p ∣ n - 2 ^ b) : False := by
  have hcp : Nat.Coprime 2 p := by
    apply (hp.coprime_iff_not_dvd.mpr ?_).symm
    intro h
    have := Nat.le_of_dvd (by decide : 0 < 2) h
    omega
  have hc : Nat.Coprime 2 (p * p) := hcp.mul_right hcp
  have hm : Nat.ModEq (p * p) (2 ^ a) (2 ^ b) :=
    ((Nat.modEq_iff_dvd' ha).mpr hda).trans ((Nat.modEq_iff_dvd' hb).mpr hdb).symm
  have hdiff : p * p ∣ 2 ^ b - 2 ^ a := hm.dvd'
  have heq : 2 ^ b - 2 ^ a = 2 ^ a * (2 ^ (b - a) - 1) := by
    calc
      2 ^ b - 2 ^ a = 2 ^ (a + (b - a)) - 2 ^ a := by
        rw [show a + (b - a) = b by omega]
      _ = 2 ^ a * (2 ^ (b - a) - 1) := by
        rw [pow_add, Nat.mul_sub_left_distrib, mul_one]
  rw [heq] at hdiff
  have hd : p * p ∣ 2 ^ (b - a) - 1 :=
    (hc.pow_left a).symm.dvd_of_dvd_mul_left hdiff
  rcases prime_square_mersenne_lt_110 (by omega) (by omega) hp hd with h | h | h <;> omega

/-- A square-divisor certificate using only primes at least eleven must use distinct primes
throughout a window of length at most 110. -/
theorem large_blockers_injective {n A W : ℕ} (hW : W ≤ 110)
    (d : Fin W → ℕ) (hn : ∀ i : Fin W, 2 ^ (A + i.val) ≤ n)
    (hd : ∀ i : Fin W, (d i).Prime ∧ 11 ≤ d i ∧
      d i * d i ∣ n - 2 ^ (A + i.val)) : Function.Injective d := by
  intro i j hij
  apply Fin.ext
  by_contra hne
  obtain ⟨hpi, hli, hdi⟩ := hd i
  obtain ⟨hpj, hlj, hdj⟩ := hd j
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [← hij] at hdj
    exact no_repeated_large_prime hpi hli (by omega) (by omega) (hn i) (hn j) hdi hdj
  · rw [hij] at hdi
    exact no_repeated_large_prime hpj hlj (by omega) (by omega) (hn j) (hn i) hdj hdi

end Contribution.Erdos11Certificates.ShortCollisions


/-! Bind the conditional certificate verifier to the pinned task's explicit proposition. -/

namespace Contribution.Erdos11Certificates

/-- A complete square-divisor certificate would refute the pinned target without invoking it. -/
theorem refute_pinned_target_of_certificate {n L : ℕ} (hclass : n % 4 = 3)
    (hn : n ≤ 2 ^ L) (d : ℕ → ℕ)
    (hd : ∀ l < L, 1 < d l ∧ d l * d l ∣ n - 2 ^ l) :
    ¬ (∀ n : ℕ, Odd n → 1 < n → ∃ k l : ℕ, Squarefree k ∧ n = k + 2 ^ l) :=
  refute_of_three_mod_four_certificate hclass hn d hd

end Contribution.Erdos11Certificates
