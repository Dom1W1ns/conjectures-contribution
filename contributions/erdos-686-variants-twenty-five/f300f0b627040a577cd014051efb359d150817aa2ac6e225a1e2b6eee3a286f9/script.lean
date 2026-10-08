/-
Partial contribution concerning Erdős problem 686, multiplier 25.

This file proves the complete fixed-length k=6 exclusion and several necessary
conditions and algebraic bridges.  It does not prove the full all-length
statement, the k=5 exclusion, class-group completeness, or elliptic rank bounds.

The six original proof bodies and namespaces are preserved below, followed by a
direct-use lemma for the original rational-ratio statement.  Imports are
consolidated here; development-time diagnostic commands are kept in the
separate audit harness.  Source provenance and theorem scope accompany this file.
-/


import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Positivity
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions

/- Original module: work/session4/K6.lean -/

/-
Fixed-length k=6 exclusion for Erdős 686, multiplier 25.
This is a partial result, not the complete bounty target.
The mathematical argument is in work/session3/algebra/k6_elementary_audit.md.
Compiled with Lean 4.33.1 and the pinned Mathlib environment.
No unproved declarations are used.
-/

namespace Contribution.Erdos686TwentyFive

private def sixProduct (a : ℕ) : ℕ :=
  (a + 1) * (a + 2) * (a + 3) * (a + 4) * (a + 5) * (a + 6)

private def centralProduct (x : ℤ) : ℤ :=
  (x ^ 2 - 1) * (x ^ 2 - 9) * (x ^ 2 - 25)

private def centralQ (x : ℤ) : ℤ := 2 * x ^ 3 - 35 * x

private lemma centralProduct_eq (n : ℕ) :
    centralProduct (2 * (n : ℤ) + 7) = 64 * (sixProduct n : ℤ) := by
  unfold centralProduct sixProduct
  push_cast
  ring

private lemma central_identity (x : ℤ) :
    centralQ x ^ 2 - 4 * centralProduct x = 189 * x ^ 2 + 900 := by
  unfold centralQ centralProduct
  ring

private lemma centralQ_pos {x : ℤ} (hx : 7 ≤ x) : 0 < centralQ x := by
  have hxpos : 0 < x := by omega
  have hi : 0 < 2 * x ^ 2 - 35 := by nlinarith [sq_nonneg (x - 7)]
  have hp := mul_pos hxpos hi
  unfold centralQ
  nlinarith [hp]

private lemma centralQ_mod (n : ℕ) :
    centralQ (2 * (n : ℤ) + 7) % 6 = 3 := by
  have hr : (n : ℤ) % 3 = 0 ∨ (n : ℤ) % 3 = 1 ∨ (n : ℤ) % 3 = 2 := by omega
  have hd : (n : ℤ) = 3 * ((n : ℤ) / 3) + (n : ℤ) % 3 := by omega
  rcases hr with h | h | h
  all_goals
    rw [h] at hd
    unfold centralQ
    rw [hd]
    ring_nf
    omega

private lemma sixProduct_pos (n : ℕ) : 0 < sixProduct n := by
  unfold sixProduct
  positivity

private lemma upper_bound (n m : ℕ)
    (heq : sixProduct m = 25 * sixProduct n) : m < 2 * n + 6 := by
  by_contra h
  have hm : 2 * n + 6 ≤ m := by omega
  have hp : 64 * sixProduct n ≤ sixProduct m := by
    calc
      64 * sixProduct n =
          (2 * (n + 1)) * (2 * (n + 2)) * (2 * (n + 3)) *
          (2 * (n + 4)) * (2 * (n + 5)) * (2 * (n + 6)) := by
        unfold sixProduct
        ring
      _ ≤ sixProduct m := by
        unfold sixProduct
        gcongr <;> omega
  have hpos := sixProduct_pos n
  omega

private theorem sixProduct_ne (n m : ℕ) (hmn : n + 6 ≤ m) :
    sixProduct m ≠ 25 * sixProduct n := by
  intro heq
  have hmu := upper_bound n m heq
  let x : ℤ := 2 * (n : ℤ) + 7
  let y : ℤ := 2 * (m : ℤ) + 7
  have hx : 7 ≤ x := by dsimp [x]; omega
  have hy : 7 ≤ y := by dsimp [y]; omega
  have hxy : x < y := by dsimp [x, y]; omega
  have hy5 : y < 5 * x := by dsimp [x, y]; omega
  have heqz : (sixProduct m : ℤ) = 25 * (sixProduct n : ℤ) := by
    exact_mod_cast heq
  have hP : centralProduct y = 25 * centralProduct x := by
    dsimp [x, y]
    rw [centralProduct_eq, centralProduct_eq]
    nlinarith [heqz]
  have hqx := centralQ_pos hx
  have hqy := centralQ_pos hy
  have hix := central_identity x
  have hiy := central_identity y
  have hysq : y ^ 2 < 25 * x ^ 2 := by
    have hp : 0 < (5 * x - y) * (5 * x + y) :=
      mul_pos (by omega) (by omega)
    nlinarith [hp]
  have hqsq : centralQ y ^ 2 < 25 * centralQ x ^ 2 := by
    nlinarith [hix, hiy, hP, hysq]
  have hq_lt : centralQ y < 5 * centralQ x := by
    nlinarith [hqsq]
  have hmx : centralQ x % 6 = 3 := centralQ_mod n
  have hmy : centralQ y % 6 = 3 := centralQ_mod m
  have hgap : 6 ≤ 5 * centralQ x - centralQ y := by omega
  have hsquare : centralQ y ^ 2 ≤ (5 * centralQ x - 6) ^ 2 := by
    have hp : 0 ≤ (5 * centralQ x - 6 - centralQ y) *
        (5 * centralQ x - 6 + centralQ y) := mul_nonneg (by omega) (by omega)
    nlinarith [hp]
  have h60 : 60 * centralQ x ≤ 4725 * x ^ 2 - 189 * y ^ 2 + 21636 := by
    nlinarith [hix, hiy, hP, hsquare]
  have hxy_sq : x ^ 2 < y ^ 2 := by
    have hp : 0 < (y - x) * (y + x) := mul_pos (by omega) (by omega)
    nlinarith [hp]
  have hF : 120 * x ^ 3 - 4536 * x ^ 2 - 2100 * x - 21636 < 0 := by
    unfold centralQ at h60
    nlinarith [h60, hxy_sq]
  have hn : n < 16 := by
    by_contra hn
    have ht : 0 ≤ x - 39 := by dsimp [x]; omega
    have ht2 : 0 ≤ (x - 39) ^ 2 := sq_nonneg _
    have ht3 : 0 ≤ (x - 39) ^ 3 := pow_nonneg ht _
    nlinarith [hF, ht, ht2, ht3]
  have hm : m < 36 := by omega
  have finite_check : ∀ a : Fin 16, ∀ b : Fin 36,
      a.val + 6 ≤ b.val → b.val ≤ 2 * a.val + 5 →
      sixProduct b.val ≠ 25 * sixProduct a.val := by decide
  exact finite_check ⟨n, hn⟩ ⟨m, hm⟩ hmn (by change m ≤ 2 * n + 5; omega) heq

/-- The multiplier 25 has no admissible representation with block length 6. -/
theorem k6_exclusion (n m : ℕ) (hmn : n + 6 ≤ m) :
    (∏ i ∈ Finset.Icc 1 6, (m + i)) ≠
      25 * (∏ i ∈ Finset.Icc 1 6, (n + i)) := by
  have hprod (a : ℕ) : (∏ i ∈ Finset.Icc 1 6, (a + i)) = sixProduct a := by
    norm_num [Finset.prod_Icc_succ_top, Finset.Icc_self, sixProduct]
  simpa only [hprod] using sixProduct_ne n m hmn

end Contribution.Erdos686TwentyFive

/- Original module: work/session6/PrimeTransport.lean -/

/-
Universal prime-divisor transport for the Erdős 686 multiplier-25 equation.
This is an unbounded necessary condition, not a solution of the bounty.
-/

namespace Contribution.Erdos686TwentyFive

private lemma prime_dvd_finset_prod {p : ℕ} (hp : p.Prime)
    (s : Finset ℕ) (f : ℕ → ℕ) (h : p ∣ ∏ i ∈ s, f i) :
    ∃ i ∈ s, p ∣ f i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty] at h
      exact False.elim (hp.not_dvd_one h)
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha] at h
      rcases hp.dvd_mul.mp h with h | h
      · exact ⟨a, Finset.mem_insert_self a s, h⟩
      · obtain ⟨i, hi, hd⟩ := ih h
        exact ⟨i, Finset.mem_insert_of_mem hi, hd⟩

/-- A prime occurring in both disjoint blocks is bounded by their total width. -/
theorem common_prime_le_width (n m k p : ℕ) (hp : p.Prime)
    (hmn : n + k ≤ m)
    (hlower : p ∣ ∏ i ∈ Finset.Icc 1 k, (n + i))
    (hupper : p ∣ ∏ i ∈ Finset.Icc 1 k, (m + i)) :
    p ≤ m - n + k - 1 := by
  obtain ⟨i, hi, hpi⟩ := prime_dvd_finset_prod hp _ _ hlower
  obtain ⟨j, hj, hpj⟩ := prime_dvd_finset_prod hp _ _ hupper
  rcases Finset.mem_Icc.mp hi with ⟨hi1, hik⟩
  rcases Finset.mem_Icc.mp hj with ⟨hj1, hjk⟩
  have hpos : 0 < (m + j) - (n + i) := by omega
  have hpd : p ∣ (m + j) - (n + i) := Nat.dvd_sub hpj hpi
  have hle := Nat.le_of_dvd hpos hpd
  omega

/-- Every prime divisor of the lower block is at most m-n+k-1. -/
theorem lower_prime_le_width (n m k p : ℕ) (hp : p.Prime)
    (hmn : n + k ≤ m)
    (heq : (∏ i ∈ Finset.Icc 1 k, (m + i)) =
      25 * (∏ i ∈ Finset.Icc 1 k, (n + i)))
    (hlower : p ∣ ∏ i ∈ Finset.Icc 1 k, (n + i)) :
    p ≤ m - n + k - 1 := by
  apply common_prime_le_width n m k p hp hmn hlower
  rw [heq]
  exact dvd_mul_of_dvd_right hlower 25

/-- Every prime divisor of the upper block other than 5 has the same width bound. -/
theorem upper_prime_le_width (n m k p : ℕ) (hp : p.Prime)
    (hp5 : p ≠ 5) (hmn : n + k ≤ m)
    (heq : (∏ i ∈ Finset.Icc 1 k, (m + i)) =
      25 * (∏ i ∈ Finset.Icc 1 k, (n + i)))
    (hupper : p ∣ ∏ i ∈ Finset.Icc 1 k, (m + i)) :
    p ≤ m - n + k - 1 := by
  have hnot25 : ¬ p ∣ 25 := by
    intro h
    have hpow : p ∣ 5 ^ 2 := h
    have hfive := hp.dvd_of_dvd_pow hpow
    exact hp5 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp hfive)
  have hlower : p ∣ ∏ i ∈ Finset.Icc 1 k, (n + i) := by
    rw [heq] at hupper
    exact (hp.dvd_mul.mp hupper).resolve_left hnot25
  exact lower_prime_le_width n m k p hp hmn heq hlower

/-- If both blocks lie below 2n, every entry of the lower block is composite. -/
theorem lower_block_not_prime (n m k : ℕ) (hmn : n + k ≤ m)
    (heq : (∏ i ∈ Finset.Icc 1 k, (m + i)) =
      25 * (∏ i ∈ Finset.Icc 1 k, (n + i)))
    (hspan : m + k < 2 * n) (i : ℕ) (hi : i ∈ Finset.Icc 1 k) :
    ¬ (n + i).Prime := by
  intro hp
  have hd : n + i ∣ ∏ j ∈ Finset.Icc 1 k, (n + j) :=
    Finset.dvd_prod_of_mem (fun j => n + j) hi
  have hb := lower_prime_le_width n m k (n + i) hp hmn heq hd
  rcases Finset.mem_Icc.mp hi with ⟨hi1, hik⟩
  omega

/-- Under the same span bound and n≥5, every entry of the upper block is composite. -/
theorem upper_block_not_prime (n m k : ℕ) (hn : 5 ≤ n) (hmn : n + k ≤ m)
    (heq : (∏ i ∈ Finset.Icc 1 k, (m + i)) =
      25 * (∏ i ∈ Finset.Icc 1 k, (n + i)))
    (hspan : m + k < 2 * n) (i : ℕ) (hi : i ∈ Finset.Icc 1 k) :
    ¬ (m + i).Prime := by
  intro hp
  have hd : m + i ∣ ∏ j ∈ Finset.Icc 1 k, (m + j) :=
    Finset.dvd_prod_of_mem (fun j => m + j) hi
  rcases Finset.mem_Icc.mp hi with ⟨hi1, hik⟩
  have hp5 : m + i ≠ 5 := by omega
  have hb := upper_prime_le_width n m k (m + i) hp hp5 hmn heq hd
  omega

end Contribution.Erdos686TwentyFive

/- Original module: work/session6/GapSquareTransport.lean -/

/-
Squared divisibility transported through an exact finite-product ratio.
This is a reusable necessary condition, not the Erdős 686 bounty target.
-/

namespace Contribution.Erdos686TwentyFive

section CommRing

variable {R ι : Type*} [CommRing R]

/-- Shifting every factor by a multiple of q preserves the product modulo q. -/
theorem dvd_shifted_prod_sub_prod (s : Finset ι) (A : ι → R) (q d : R)
    (hd : q ∣ d) :
    q ∣ (∏ j ∈ s, (A j + d)) - ∏ j ∈ s, A j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have hidentity :
          (A a + d) * (∏ j ∈ s, (A j + d)) - A a * (∏ j ∈ s, A j) =
          (A a + d) * ((∏ j ∈ s, (A j + d)) - ∏ j ∈ s, A j) +
            d * (∏ j ∈ s, A j) := by ring
      rw [hidentity]
      exact dvd_add (dvd_mul_of_dvd_right ih _) (dvd_mul_of_dvd_left hd _)

/-- Algebraic square gain after separating the distinguished factor. -/
theorem square_dvd_of_coprime_product_complement
    (a C C' d q N : R) (ha : q ∣ a) (hd : q ∣ d)
    (hcop : IsCoprime q C) (hshift : q ∣ C' - C)
    (heq : (a + d) * C' = N * (a * C)) :
    q ^ 2 ∣ (N - 1) * a - d := by
  have hcop2 : IsCoprime (q ^ 2) C := by
    simpa only [pow_two] using hcop.mul_left hcop
  apply hcop2.dvd_of_dvd_mul_left
  have hprod : q * q ∣ (a + d) * (C' - C) :=
    mul_dvd_mul (dvd_add ha hd) hshift
  have hidentity : (a + d) * (C' - C) = C * ((N - 1) * a - d) := by
    calc
      (a + d) * (C' - C) = (a + d) * C' - (a + d) * C := by ring
      _ = N * (a * C) - (a + d) * C := by rw [heq]
      _ = C * ((N - 1) * a - d) := by ring
  simpa only [pow_two, hidentity] using hprod

/-- If q divides the distinguished term and the common shift, while being
coprime to the complementary product, the exact product ratio forces a square
divisibility. No primality, positivity or nonzero assumptions are needed. -/
theorem square_dvd_transport_of_coprime_complement [DecidableEq ι]
    (s : Finset ι) (A : ι → R) (i : ι) (hi : i ∈ s) (d q N : R)
    (hAi : q ∣ A i) (hd : q ∣ d)
    (hcop : IsCoprime q (∏ j ∈ s.erase i, A j))
    (heq : (∏ j ∈ s, (A j + d)) = N * (∏ j ∈ s, A j)) :
    q ^ 2 ∣ (N - 1) * A i - d := by
  apply square_dvd_of_coprime_product_complement
    (A i) (∏ j ∈ s.erase i, A j) (∏ j ∈ s.erase i, (A j + d)) d q N
    hAi hd hcop (dvd_shifted_prod_sub_prod (s.erase i) A q d hd)
  calc
    (A i + d) * (∏ j ∈ s.erase i, (A j + d)) =
        ∏ j ∈ s, (A j + d) := Finset.mul_prod_erase s (fun j => A j + d) hi
    _ = N * (∏ j ∈ s, A j) := heq
    _ = N * (A i * (∏ j ∈ s.erase i, A j)) := by
      rw [Finset.mul_prod_erase s A hi]

end CommRing

end Contribution.Erdos686TwentyFive

/- Original module: work/session7/HigherContactCertificate.lean -/

/-
Reusable algebraic core of the higher-contact certificates for Erdős 686.
This does not assert the prime-power normalization, any numerical certificate,
or the complete multiplier-25 bounty target.
-/

namespace Contribution.Erdos686TwentyFive

variable {A : Type*} [CommSemiring A]

/-- A monomial of total degree at least `order` is divisible by `q ^ order`
when both of its inputs are divisible by `q`. -/
theorem higherContact_monomial_dvd (q u v coefficient : A)
    (a b order : ℕ) (hu : q ∣ u) (hv : q ∣ v)
    (hdegree : order ≤ a + b) :
    q ^ order ∣ coefficient * u ^ a * v ^ b := by
  have hpowers : q ^ (a + b) ∣ u ^ a * v ^ b := by
    rw [pow_add]
    exact mul_dvd_mul (pow_dvd_pow_of_dvd hu a) (pow_dvd_pow_of_dvd hv b)
  have hmonomial : q ^ order ∣ u ^ a * v ^ b :=
    (pow_dvd_pow q hdegree).trans hpowers
  simpa only [mul_assoc] using dvd_mul_of_dvd_right hmonomial coefficient

/-- Every finite polynomial remainder whose monomials have total degree at
least `order` is divisible by `q ^ order` at inputs divisible by `q`. -/
theorem higherContact_remainder_dvd (s : Finset (ℕ × ℕ))
    (coefficient : ℕ × ℕ → A) (q u v : A) (order : ℕ)
    (hu : q ∣ u) (hv : q ∣ v)
    (hdegree : ∀ ab ∈ s, order ≤ ab.1 + ab.2) :
    q ^ order ∣ ∑ ab ∈ s, coefficient ab * u ^ ab.1 * v ^ ab.2 := by
  classical
  revert hdegree
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simp only [Finset.sum_empty]
      exact ⟨0, by rw [mul_zero]⟩
  | @insert ab s hab ih =>
      intro hdegree
      rw [Finset.sum_insert hab]
      obtain ⟨w, hw⟩ := higherContact_monomial_dvd q u v (coefficient ab)
        ab.1 ab.2 order hu hv (hdegree ab (Finset.mem_insert_self ab s))
      obtain ⟨z, hz⟩ := ih (fun cd hcd => hdegree cd (Finset.mem_insert_of_mem hcd))
      exact ⟨w + z, by rw [mul_add, ← hw, ← hz]⟩

/-- An exact identity `G = F * H + remainder` gives higher divisibility of `G`
on `F = 0`, when the remainder has the required total degree. -/
theorem higherContact_certificate_dvd (s : Finset (ℕ × ℕ))
    (coefficient : ℕ × ℕ → A) (q u v G F H : A) (order : ℕ)
    (hu : q ∣ u) (hv : q ∣ v)
    (hdegree : ∀ ab ∈ s, order ≤ ab.1 + ab.2)
    (hidentity : G = F * H + ∑ ab ∈ s, coefficient ab * u ^ ab.1 * v ^ ab.2)
    (hcurve : F = 0) : q ^ order ∣ G := by
  rw [hidentity, hcurve, zero_mul, zero_add]
  exact higherContact_remainder_dvd s coefficient q u v order hu hv hdegree

end Contribution.Erdos686TwentyFive

/- Original module: work/session9/QuotientBridge.lean -/

/-
Exact algebraic bridge for the length-five quotient used in session 9.
This file does NOT prove existence, nonexistence, or squareclass completeness.
-/

namespace Contribution.Erdos686TwentyFive

def centeredFive (t : ℚ) : ℚ := t ^ 5 - 5 * t ^ 3 + 4 * t

def quotientSextic (r : ℚ) : ℚ :=
  9 * r ^ 6 + 400 * r ^ 5 - 1250 * r ^ 3 + 400 * r + 5625

theorem centeredFive_product (a : ℚ) :
    centeredFive (a + 3) =
      (a + 1) * (a + 2) * (a + 3) * (a + 4) * (a + 5) := by
  unfold centeredFive
  ring

theorem quotient_discriminant (r X : ℚ)
    (h : (r ^ 5 - 25) * X ^ 2 - 5 * (r ^ 3 - 25) * X +
      4 * (r - 25) = 0) :
    (2 * (r ^ 5 - 25) * X - 5 * (r ^ 3 - 25)) ^ 2 =
      quotientSextic r := by
  unfold quotientSextic
  have hid :
      (2 * (r ^ 5 - 25) * X - 5 * (r ^ 3 - 25)) ^ 2 -
        (9 * r ^ 6 + 400 * r ^ 5 - 1250 * r ^ 3 + 400 * r + 5625) =
      4 * (r ^ 5 - 25) * ((r ^ 5 - 25) * X ^ 2 -
        5 * (r ^ 3 - 25) * X + 4 * (r - 25)) := by ring
  rw [h, mul_zero] at hid
  exact sub_eq_zero.mp hid

theorem centeredFive_to_quotient (x y : ℚ) (hx : x ≠ 0)
    (h : centeredFive y = 25 * centeredFive x) :
    (2 * ((y / x) ^ 5 - 25) * x ^ 2 -
      5 * ((y / x) ^ 3 - 25)) ^ 2 = quotientSextic (y / x) := by
  apply quotient_discriminant (y / x) (x ^ 2)
  have hxy : y / x * x = y := div_mul_cancel₀ y hx
  have hmul : x * (((y / x) ^ 5 - 25) * (x ^ 2) ^ 2 -
      5 * ((y / x) ^ 3 - 25) * x ^ 2 + 4 * (y / x - 25)) = 0 := by
    calc
      _ = centeredFive (y / x * x) - 25 * centeredFive x := by
        unfold centeredFive
        ring
      _ = 0 := by rw [hxy, h]; ring
  exact (mul_eq_zero.mp hmul).resolve_left hx


end Contribution.Erdos686TwentyFive

/- Original module: work/session13/NormRelationBridge.lean -/

/-
Abstract linear-algebra bridge for the session-13 norm relation.

This file proves only that a coefficient-five identity between linear maps
over F_2 gives an injection into a product and the corresponding dimension
bound.  It does not construct class groups or arithmetic correspondences,
instantiate the maps with number fields, certify any class-group bound, or
prove the k=5 case or the full Erdős 686 multiplier-25 problem.
-/

namespace Contribution.Erdos686TwentyFive.NormRelationBridge

variable {V A B C : Type*}
variable [AddCommGroup V] [Module (ZMod 2) V]
variable [AddCommGroup A] [Module (ZMod 2) A]
variable [AddCommGroup B] [Module (ZMod 2) B]
variable [AddCommGroup C] [Module (ZMod 2) C]

/-- Additive multiplication by five is the identity on an F_2-vector space. -/
theorem five_nsmul (x : V) : (5 : ℕ) • x = x := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod 2)]
  change (5 : ZMod 2) • x = x
  have h5 : (5 : ZMod 2) = 1 := by decide
  rw [h5, one_smul]

/-- The three forward maps jointly separate points if the reverse maps
recover additive multiplication by five. -/
theorem relation_injective
    (a : V →ₗ[ZMod 2] A) (b : V →ₗ[ZMod 2] B) (c : V →ₗ[ZMod 2] C)
    (u : A →ₗ[ZMod 2] V) (v : B →ₗ[ZMod 2] V) (w : C →ₗ[ZMod 2] V)
    (h : ∀ x : V, u (a x) + v (b x) + w (c x) = (5 : ℕ) • x) :
    Function.Injective (a.prod (b.prod c)) := by
  intro x y hxy
  have ha : a x = a y := congrArg Prod.fst hxy
  have hb : b x = b y := congrArg (fun t : A × B × C => t.2.1) hxy
  have hc : c x = c y := congrArg (fun t : A × B × C => t.2.2) hxy
  calc
    x = u (a x) + v (b x) + w (c x) := by
      simpa only [five_nsmul] using (h x).symm
    _ = u (a y) + v (b y) + w (c y) := by rw [ha, hb, hc]
    _ = y := by simpa only [five_nsmul] using h y

/-- Consequently the source dimension is at most the sum of the three
target dimensions. -/
theorem relation_finrank_le
    [Module.Finite (ZMod 2) V]
    [Module.Finite (ZMod 2) A]
    [Module.Finite (ZMod 2) B]
    [Module.Finite (ZMod 2) C]
    (a : V →ₗ[ZMod 2] A) (b : V →ₗ[ZMod 2] B) (c : V →ₗ[ZMod 2] C)
    (u : A →ₗ[ZMod 2] V) (v : B →ₗ[ZMod 2] V) (w : C →ₗ[ZMod 2] V)
    (h : ∀ x : V, u (a x) + v (b x) + w (c x) = (5 : ℕ) • x) :
    Module.finrank (ZMod 2) V ≤
      Module.finrank (ZMod 2) A + Module.finrank (ZMod 2) B +
        Module.finrank (ZMod 2) C := by
  have hi := LinearMap.finrank_le_finrank_of_injective
    (relation_injective a b c u v w h)
  simpa only [Module.finrank_prod, Nat.add_assoc] using hi


end Contribution.Erdos686TwentyFive.NormRelationBridge

/- Original module: work/publication686/K6RatioBridge.lean -/

/- Direct use of the fixed-length exclusion in the original rational-ratio form. -/
namespace Contribution.Erdos686TwentyFive

/-- The rational ratio occurring in the original question cannot equal 25
when the block length is six.  Its denominator is proved positive. -/
theorem k6_ratio_exclusion (n m : ℕ) (hmn : n + 6 ≤ m) :
    (25 : ℚ) ≠
      ((∏ i ∈ Finset.Icc 1 6, (m + i) : ℕ) : ℚ) /
        ((∏ i ∈ Finset.Icc 1 6, (n + i) : ℕ) : ℚ) := by
  intro h
  have hnpos : 0 < (∏ i ∈ Finset.Icc 1 6, (n + i) : ℕ) := by
    apply Finset.prod_pos
    intro i hi
    have hi1 := (Finset.mem_Icc.mp hi).1
    omega
  have hnzero : ((∏ i ∈ Finset.Icc 1 6, (n + i) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hnpos)
  have hq : ((∏ i ∈ Finset.Icc 1 6, (m + i) : ℕ) : ℚ) =
      25 * ((∏ i ∈ Finset.Icc 1 6, (n + i) : ℕ) : ℚ) :=
    ((eq_div_iff hnzero).mp h).symm
  have hn : (∏ i ∈ Finset.Icc 1 6, (m + i) : ℕ) =
      25 * (∏ i ∈ Finset.Icc 1 6, (n + i) : ℕ) := by
    exact_mod_cast hq
  exact k6_exclusion n m hmn hn

end Contribution.Erdos686TwentyFive
