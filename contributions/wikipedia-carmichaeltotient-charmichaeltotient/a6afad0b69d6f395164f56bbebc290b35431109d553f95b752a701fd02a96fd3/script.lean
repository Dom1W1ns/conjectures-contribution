import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Structural constraints for Carmichael's totient conjecture

A partial contribution for `wikipedia-carmichaeltotient-charmichaeltotient`.
The prime-square forcing argument is an elementary case of the classical
Carmichael--Klee method; see Kevin Ford, The distribution of totients,
Section 7.3, https://arxiv.org/abs/1104.3264.

All results below are proved directly from Mathlib. The global conjecture
and the historical large lower bounds are not assumed or proved here.
-/

namespace Contribution.CarmichaelTotient

/-- A positive integer whose totient has no other natural-number preimage. -/
def UniqueTotient (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, Nat.totient m = Nat.totient n → m = n

/-- Global uniqueness is the exact obstruction in Carmichael's conjecture. -/
theorem uniqueTotient_iff {n : ℕ} :
    UniqueTotient n ↔ 0 < n ∧ ¬ ∃ m : ℕ, m ≠ n ∧ Nat.totient m = Nat.totient n := by
  simp only [UniqueTotient]
  constructor
  · rintro ⟨hn, hu⟩
    exact ⟨hn, fun ⟨m, hmn, hφ⟩ => hmn (hu m hφ)⟩
  · rintro ⟨hn, hu⟩
    refine ⟨hn, fun m hφ => ?_⟩
    by_contra hmn
    exact hu ⟨m, hmn, hφ⟩

/-- A hypothetical unique preimage is divisible by four. -/
theorem four_dvd_of_unique {n : ℕ} (hn : 0 < n)
    (hu : ∀ m : ℕ, Nat.totient m = Nat.totient n → m = n) : 4 ∣ n := by
  have htwo : 2 ∣ n := by
    by_contra h
    have ho : Odd n := Nat.not_even_iff_odd.mp (fun he => h he.two_dvd)
    have he := hu (2 * n) (Nat.totient_two_mul_of_odd ho)
    omega
  obtain ⟨k, rfl⟩ := htwo
  have htwo : 2 ∣ k := by
    by_contra h
    have ho : Odd k := Nat.not_even_iff_odd.mp (fun he => h he.two_dvd)
    have he := hu k (Nat.totient_two_mul_of_odd ho).symm
    omega
  obtain ⟨j, rfl⟩ := htwo
  exact ⟨j, by omega⟩

/-- Every positive integer not divisible by four satisfies the conjecture. -/
theorem collision_of_not_four_dvd {n : ℕ} (hn : 0 < n) (hfour : ¬4 ∣ n) :
    ∃ m : ℕ, m ≠ n ∧ Nat.totient m = Nat.totient n := by
  by_contra h
  have hu : ∀ m : ℕ, Nat.totient m = Nat.totient n → m = n := by
    intro m hφ
    by_contra hmn
    exact h ⟨m, hmn, hφ⟩
  exact hfour (four_dvd_of_unique hn hu)

/-- Multiplying by a divisor introduces no new prime divisors. -/
theorem totient_mul_of_dvd {a k : ℕ} (hk : 0 < k) (hka : k ∣ a) :
    (k * a).totient = k * a.totient := by
  have h := Nat.totient_gcd_mul_totient_mul k a
  rw [Nat.gcd_eq_left hka] at h
  have ht : 0 < k.totient := Nat.totient_pos.mpr hk
  nlinarith

/-- Replacing a prime by its predecessor preserves the totient when the
predecessor already divides the remaining factor. -/
theorem totient_prime_mul_eq_pred_mul {p a : ℕ} (hp : p.Prime)
    (hpa : ¬ p ∣ a) (hpred : p - 1 ∣ a) :
    (p * a).totient = ((p - 1) * a).totient := by
  rw [Nat.totient_mul_of_prime_of_not_dvd hp hpa,
    totient_mul_of_dvd (by have := hp.two_le; omega) hpred]

/-- A prime dividing a global singleton totient fiber must occur at least twice
if its predecessor also divides the integer. -/
theorem prime_sq_dvd_of_prime_and_pred_dvd {n p : ℕ} (hn : 0 < n)
    (huniq : ∀ m : ℕ, m.totient = n.totient → m = n)
    (hp : p.Prime) (hpn : p ∣ n) (hpred : p - 1 ∣ n) : p ^ 2 ∣ n := by
  obtain ⟨a, rfl⟩ := hpn
  by_cases hpa : p ∣ a
  · simpa [pow_two] using Nat.mul_dvd_mul_left p hpa
  have hcop : (p - 1).Coprime p :=
    (Nat.coprime_self_sub_left (by have := hp.two_le; omega)).mpr (Nat.coprime_one_left p)
  have hpreda : p - 1 ∣ a := hcop.dvd_of_dvd_mul_left hpred
  have heq := huniq ((p - 1) * a) (totient_prime_mul_eq_pred_mul hp hpa hpreda).symm
  have hpadd : p - 1 + 1 = p := by have := hp.two_le; omega
  have ha : 0 < a := Nat.pos_of_mul_pos_left hn
  nlinarith

/-- If the square of a prime's predecessor divides a global singleton totient
fiber, then the square of that prime divides it as well. -/
theorem prime_sq_dvd_of_pred_sq_dvd {n p : ℕ} (hn : 0 < n)
    (huniq : ∀ m : ℕ, m.totient = n.totient → m = n)
    (hp : p.Prime) (hpred : (p - 1) ^ 2 ∣ n) : p ^ 2 ∣ n := by
  have hpredn : p - 1 ∣ n := Nat.dvd_of_pow_dvd (by decide) hpred
  apply prime_sq_dvd_of_prime_and_pred_dvd hn huniq hp _ hpredn
  by_contra hpn
  obtain ⟨a, rfl⟩ := hpredn
  have hpredpos : 0 < p - 1 := by have := hp.two_le; omega
  have hpreda : p - 1 ∣ a := by
    apply Nat.dvd_of_mul_dvd_mul_left hpredpos
    simpa [pow_two] using hpred
  have hpa : ¬ p ∣ a := fun h => hpn (dvd_mul_of_dvd_right h _)
  have heq := huniq (p * a) (totient_prime_mul_eq_pred_mul hp hpa hpreda)
  have hpadd : p - 1 + 1 = p := by have := hp.two_le; omega
  have ha : 0 < a := Nat.pos_of_mul_pos_left hn
  nlinarith

/-- The first forced prime squares in the predecessor-square descent. -/
theorem forced_prime_squares {n : ℕ} (hn : 0 < n)
    (huniq : ∀ m : ℕ, m.totient = n.totient → m = n) :
    4 ∣ n ∧ 9 ∣ n ∧ 49 ∣ n ∧ 1849 ∣ n := by
  have h4 : 4 ∣ n := by
    simpa using prime_sq_dvd_of_pred_sq_dvd hn huniq (by norm_num : Nat.Prime 2)
      (by norm_num : (2 - 1) ^ 2 ∣ n)
  have h9 : 9 ∣ n := by
    simpa using prime_sq_dvd_of_pred_sq_dvd hn huniq (by norm_num : Nat.Prime 3)
      (by simpa using h4)
  have h36 : 36 ∣ n := by
    simpa using (show Nat.Coprime 4 9 by norm_num).mul_dvd_of_dvd_of_dvd h4 h9
  have h49 : 49 ∣ n := by
    simpa using prime_sq_dvd_of_pred_sq_dvd hn huniq (by norm_num : Nat.Prime 7)
      (by simpa using h36)
  have h1764 : 1764 ∣ n := by
    simpa using (show Nat.Coprime 36 49 by norm_num).mul_dvd_of_dvd_of_dvd h36 h49
  have h1849 : 1849 ∣ n := by
    simpa using prime_sq_dvd_of_pred_sq_dvd hn huniq (by norm_num : Nat.Prime 43)
      (by simpa using h1764)
  exact ⟨h4, h9, h49, h1849⟩

/-- An elementary lower bound obtained solely from the four forced prime squares.
This does not claim Klee's substantially stronger historical bound. -/
theorem elementary_divisibility_bound {n : ℕ} (hn : 0 < n)
    (huniq : ∀ m : ℕ, m.totient = n.totient → m = n) :
    3261636 ∣ n ∧ 3261636 ≤ n := by
  obtain ⟨h4, h9, h49, h1849⟩ := forced_prime_squares hn huniq
  have h36 : 36 ∣ n := by
    simpa using (show Nat.Coprime 4 9 by norm_num).mul_dvd_of_dvd_of_dvd h4 h9
  have h1764 : 1764 ∣ n := by
    simpa using (show Nat.Coprime 36 49 by norm_num).mul_dvd_of_dvd_of_dvd h36 h49
  have h : 3261636 ∣ n := by
    simpa using (show Nat.Coprime 1764 1849 by norm_num).mul_dvd_of_dvd_of_dvd h1764 h1849
  exact ⟨h, Nat.le_of_dvd hn h⟩

/-- Every positive integer below the elementary bound has a different totient
preimage. This follows by contradiction from the structural divisibility bound. -/
theorem exists_companion_below_elementary_bound {n : ℕ} (hn : 0 < n)
    (hbound : n < 3261636) :
    ∃ m : ℕ, m ≠ n ∧ m.totient = n.totient := by
  by_contra h
  have huniq : ∀ m : ℕ, m.totient = n.totient → m = n := by
    intro m hm
    by_contra hne
    exact h ⟨m, hne, hm⟩
  have := (elementary_divisibility_bound hn huniq).2
  omega

/-- Equal totients persist on adjoining a factor coprime to both inputs. -/
theorem totient_collision_mul {a b c : ℕ}
    (ha : a.Coprime c) (hb : b.Coprime c)
    (hφ : Nat.totient a = Nat.totient b) :
    Nat.totient (a * c) = Nat.totient (b * c) := by
  rw [Nat.totient_mul ha, Nat.totient_mul hb, hφ]

/-- A nontrivial collision stays nontrivial after multiplication by a positive
common factor, provided both totients are multiplicative there. -/
theorem collision_mul {a b c : ℕ} (hc : 0 < c) (hab : a ≠ b)
    (ha : a.Coprime c) (hb : b.Coprime c)
    (hφ : Nat.totient a = Nat.totient b) :
    a * c ≠ b * c ∧ Nat.totient (a * c) = Nat.totient (b * c) := by
  constructor
  · exact fun h => hab (Nat.eq_of_mul_eq_mul_right hc h)
  · exact totient_collision_mul ha hb hφ

/-- Every collision of one factor of a hypothetical unique preimage must
introduce a common prime with the complementary factor. -/
theorem unique_factor_replacement {a b c : ℕ} (hc : 0 < c)
    (hac : a.Coprime c)
    (huniq : ∀ m : ℕ, Nat.totient m = Nat.totient (a * c) → m = a * c)
    (hφ : Nat.totient b = Nat.totient a) (hbc : b.Coprime c) : b = a := by
  apply Nat.eq_of_mul_eq_mul_right hc
  apply huniq
  exact totient_collision_mul hbc hac hφ

/-- Contrapositive form of the replacement-factor restriction. -/
theorem unique_factor_collision_not_coprime {a b c : ℕ} (hc : 0 < c)
    (hac : a.Coprime c)
    (huniq : ∀ m : ℕ, Nat.totient m = Nat.totient (a * c) → m = a * c)
    (hφ : Nat.totient b = Nat.totient a) (hba : b ≠ a) :
    ¬ b.Coprime c := by
  intro hbc
  exact hba (unique_factor_replacement hc hac huniq hφ hbc)

/-- The powers of two starting at four have the explicit partner
`3 * 2^(k+1)`. -/
theorem two_power_collision (k : ℕ) :
    3 * 2 ^ (k + 1) ≠ 2 ^ (k + 2) ∧
    Nat.totient (3 * 2 ^ (k + 1)) = Nat.totient (2 ^ (k + 2)) := by
  have hc : Nat.Coprime 3 (2 ^ (k + 1)) := by
    exact (show Nat.Coprime 3 2 by decide).pow_right _
  have hpos : 0 < 2 ^ (k + 1) := by positivity
  have hpow : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by
    rw [show k + 2 = (k + 1) + 1 by omega, pow_succ, Nat.mul_comm]
  constructor
  · rw [hpow]
    intro h
    have : 3 = 2 := Nat.eq_of_mul_eq_mul_right hpos h
    omega
  · rw [Nat.totient_mul hc, Nat.totient_prime (by decide : Nat.Prime 3),
      Nat.totient_prime_pow_succ Nat.prime_two,
      show k + 2 = (k + 1) + 1 by omega,
      Nat.totient_prime_pow_succ Nat.prime_two]
    simp [pow_succ, Nat.mul_comm]

/-- Every power of two has a second preimage under the totient function. -/
theorem two_power_has_collision (k : ℕ) :
    ∃ m : ℕ, m ≠ 2 ^ k ∧ Nat.totient m = Nat.totient (2 ^ k) := by
  rcases k with _ | k
  · exact ⟨2, by norm_num, by norm_num⟩
  rcases k with _ | k
  · exact ⟨1, by norm_num, by norm_num⟩
  · exact ⟨3 * 2 ^ (k + 1), two_power_collision k⟩

/-- An odd positive input always has its double as a second preimage. -/
theorem odd_has_collision {n : ℕ} (hn : 0 < n) (hodd : Odd n) :
    ∃ m : ℕ, m ≠ n ∧ Nat.totient m = Nat.totient n := by
  exact ⟨2 * n, by omega, Nat.totient_two_mul_of_odd hodd⟩

/-- No power of a prime can be a counterexample to Carmichael's conjecture. -/
theorem prime_power_has_collision {p : ℕ} (hp : Nat.Prime p) (k : ℕ) :
    ∃ m : ℕ, m ≠ p ^ k ∧ Nat.totient m = Nat.totient (p ^ k) := by
  by_cases hp2 : p = 2
  · subst p
    exact two_power_has_collision k
  · apply odd_has_collision (pow_pos hp.pos _)
    exact (hp.odd_of_ne_two hp2).pow

/-- A hypothetical unique preimage is unequal to every prime power. -/
theorem unique_ne_prime_power {n p : ℕ} (hp : Nat.Prime p) (k : ℕ)
    (huniq : ∀ m : ℕ, Nat.totient m = Nat.totient n → m = n) : n ≠ p ^ k := by
  intro hn
  rcases prime_power_has_collision hp k with ⟨m, hne, hφ⟩
  exact hne (by rw [← hn]; exact huniq m (by simpa [hn] using hφ))

section FiniteChecks

set_option maxRecDepth 4096

lemma totient_3261636 : Nat.totient 3261636 = 910224 := by
  rw [show 3261636 = (2 ^ 2 * 3 ^ 2) * (7 ^ 2 * 43 ^ 2) by norm_num]
  rw [Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 2 * 3 ^ 2) (7 ^ 2 * 43 ^ 2)),
    Nat.totient_mul (by norm_num : Nat.Coprime (2 ^ 2) (3 ^ 2)),
    Nat.totient_mul (by norm_num : Nat.Coprime (7 ^ 2) (43 ^ 2)),
    Nat.totient_prime_pow_succ (by norm_num : Nat.Prime 2) 1,
    Nat.totient_prime_pow_succ (by norm_num : Nat.Prime 3) 1,
    Nat.totient_prime_pow_succ (by norm_num : Nat.Prime 7) 1,
    Nat.totient_prime_pow_succ (by norm_num : Nat.Prime 43) 1]
  norm_num

lemma totient_6523272 : Nat.totient 6523272 = 1820448 := by
  change Nat.totient (2 * 3261636) = _
  rw [Nat.totient_mul_of_prime_of_dvd Nat.prime_two (by norm_num), totient_3261636]

lemma totient_9784908 : Nat.totient 9784908 = 2730672 := by
  change Nat.totient (3 * 3261636) = _
  rw [Nat.totient_mul_of_prime_of_dvd (by norm_num : Nat.Prime 3) (by norm_num),
    totient_3261636]

lemma totient_912139 : Nat.totient 912139 = 910224 := by
  change Nat.totient (883 * 1033) = _
  rw [Nat.totient_mul (by norm_num : Nat.Coprime 883 1033),
    Nat.totient_prime (by norm_num : Nat.Prime 883),
    Nat.totient_prime (by norm_num : Nat.Prime 1033)]

lemma totient_1820449 : Nat.totient 1820449 = 1820448 := by
  exact Nat.totient_prime (by norm_num : Nat.Prime 1820449)

lemma totient_2734351 : Nat.totient 2734351 = 2730672 := by
  change Nat.totient (1033 * 2647) = _
  rw [Nat.totient_mul (by norm_num : Nat.Coprime 1033 2647),
    Nat.totient_prime (by norm_num : Nat.Prime 1033),
    Nat.totient_prime (by norm_num : Nat.Prime 2647)]

/-- Three explicit collisions eliminate the first three multiples of the
structurally forced divisor. -/
theorem checked_divisibility_bound {n : ℕ} (hn : 0 < n)
    (huniq : ∀ m : ℕ, m.totient = n.totient → m = n) :
    13046544 ≤ n := by
  have hnot1 : n ≠ 3261636 := by
    intro heq
    subst n
    have := huniq 912139 (totient_912139.trans totient_3261636.symm)
    norm_num at this
  have hnot2 : n ≠ 6523272 := by
    intro heq
    subst n
    have := huniq 1820449 (totient_1820449.trans totient_6523272.symm)
    norm_num at this
  have hnot3 : n ≠ 9784908 := by
    intro heq
    subst n
    have := huniq 2734351 (totient_2734351.trans totient_9784908.symm)
    norm_num at this
  obtain ⟨k, hk⟩ := (elementary_divisibility_bound hn huniq).1
  omega

/-- Carmichael's conclusion is proved for every positive input below 13,046,544
using structural lemmas and three explicit arithmetically checked collisions. -/
theorem exists_companion_below_checked_bound {n : ℕ} (hn : 0 < n)
    (hbound : n < 13046544) :
    ∃ m : ℕ, m ≠ n ∧ m.totient = n.totient := by
  by_contra h
  have huniq : ∀ m : ℕ, m.totient = n.totient → m = n := by
    intro m hm
    by_contra hne
    exact h ⟨m, hne, hm⟩
  have := checked_divisibility_bound hn huniq
  omega

/-- The entire ten-million-input computational scan is subsumed by a Lean proof. -/
theorem exists_companion_through_ten_million {n : ℕ} (hn : 0 < n)
    (hbound : n ≤ 10000000) :
    ∃ m : ℕ, m ≠ n ∧ m.totient = n.totient :=
  exists_companion_below_checked_bound hn (by omega)

end FiniteChecks

end Contribution.CarmichaelTotient

namespace Contribution.CarmichaelTotient.GlobalStrongerForcing

/-- The totient scales linearly when a multiplier introduces no new primes. -/
theorem totient_mul_of_prime_support {a k : ℕ}
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ k → p ∣ a) :
    (k * a).totient = k * a.totient := by
  induction k using induction_on_primes with
  | zero => simp
  | one => simp
  | prime_mul p k hp ih =>
    have hpa : p ∣ a := hsupport p hp (dvd_mul_right p k)
    have hka : (k * a).totient = k * a.totient :=
      ih (fun q hq hqk => hsupport q hq (dvd_mul_of_dvd_right hqk p))
    rw [mul_assoc, Nat.totient_mul_of_prime_of_dvd hp (dvd_mul_of_dvd_right hpa k), hka]
    simp only [mul_assoc]

/-- Carmichael's stronger predecessor criterion: it suffices that the quotient
by the predecessor still contain every prime of the predecessor. -/
theorem prime_sq_dvd_of_pred_quotient_support {n p a : ℕ} (hn : 0 < n)
    (huniq : ∀ m : ℕ, m.totient = n.totient → m = n)
    (hp : p.Prime) (hdecomp : n = (p - 1) * a)
    (hsupport : ∀ q : ℕ, q.Prime → q ∣ p - 1 → q ∣ a) :
    p ^ 2 ∣ n := by
  have hpredn : p - 1 ∣ n := ⟨a, hdecomp⟩
  apply prime_sq_dvd_of_prime_and_pred_dvd hn huniq hp _ hpredn
  by_contra hpn
  have hpa : ¬ p ∣ a := by
    intro h
    apply hpn
    rw [hdecomp]
    exact dvd_mul_of_dvd_right h _
  have hφ : (p * a).totient = n.totient := by
    rw [hdecomp, Nat.totient_mul_of_prime_of_not_dvd hp hpa,
      totient_mul_of_prime_support hsupport]
  have heq := huniq (p * a) hφ
  have hpadd : p - 1 + 1 = p := by have := hp.two_le; omega
  have ha : 0 < a := by rw [hdecomp] at hn; exact Nat.pos_of_mul_pos_left hn
  rw [hdecomp] at heq
  nlinarith

/-- When the 3-adic valuation is exactly two, a factor replacement forces 13². -/
theorem thirteen_sq_dvd_of_not_twenty_seven_dvd {n : ℕ} (hn : 0 < n)
    (huniq : ∀ m : ℕ, m.totient = n.totient → m = n)
    (h27 : ¬ 27 ∣ n) : 13 ^ 2 ∣ n := by
  obtain ⟨h4, h9, -, -⟩ := forced_prime_squares hn huniq
  have h36 : 36 ∣ n := by
    simpa using (show Nat.Coprime 4 9 by norm_num).mul_dvd_of_dvd_of_dvd h4 h9
  have h12 : 13 - 1 ∣ n := dvd_trans (by norm_num : 12 ∣ 36) h36
  apply prime_sq_dvd_of_prime_and_pred_dvd hn huniq (by norm_num) _ h12
  by_contra h13
  obtain ⟨k, rfl⟩ := h36
  have h3k : ¬ 3 ∣ k := by
    intro h
    obtain ⟨j, rfl⟩ := h
    apply h27
    exact ⟨4 * j, by ring⟩
  have hcop : Nat.Coprime 9 (4 * k) := by
    have h3 : Nat.Coprime 3 k := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h3k
    exact (show Nat.Coprime 3 4 by norm_num).mul_right h3 |>.pow_left 2
  have h13k : ¬ 13 ∣ 2 * k := by
    intro h
    apply h13
    exact dvd_trans h ⟨18, by ring⟩
  have hphi : (13 * (2 * k)).totient = (36 * k).totient := by
    rw [Nat.totient_mul_of_prime_of_not_dvd (by norm_num : Nat.Prime 13) h13k]
    rw [show 36 * k = 9 * (4 * k) by ring, Nat.totient_mul hcop]
    rw [show 4 * k = 2 * (2 * k) by ring,
      Nat.totient_mul_of_prime_of_dvd Nat.prime_two (dvd_mul_right 2 k)]
    have hphi9 : Nat.totient 9 = 6 := by
      simpa using Nat.totient_prime_pow_succ (by norm_num : Nat.Prime 3) 1
    rw [hphi9]
    ring
  have heq := huniq (13 * (2 * k)) hphi
  omega

/-- When 27 divides a singleton preimage, the support form of Carmichael's
criterion forces 19²; the weaker predecessor-square rule does not suffice. -/
theorem nineteen_sq_dvd_of_twenty_seven_dvd {n : ℕ} (hn : 0 < n)
    (huniq : ∀ m : ℕ, m.totient = n.totient → m = n)
    (h27 : 27 ∣ n) : 19 ^ 2 ∣ n := by
  obtain ⟨h4, -, -, -⟩ := forced_prime_squares hn huniq
  have h108 : 108 ∣ n := by
    simpa using (show Nat.Coprime 4 27 by norm_num).mul_dvd_of_dvd_of_dvd h4 h27
  obtain ⟨k, rfl⟩ := h108
  apply prime_sq_dvd_of_pred_quotient_support hn huniq (by norm_num : Nat.Prime 19)
    (show 108 * k = (19 - 1) * (6 * k) by ring) _
  intro q hq hqd
  have hqdiv : q ∣ 2 * 3 ^ 2 := by simpa using hqd
  rcases hq.dvd_mul.mp hqdiv with h2 | h9
  · have hq2 : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2
    subst q
    exact dvd_trans (by norm_num : 2 ∣ 6) (dvd_mul_right 6 k)
  · have hq3 : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3)).mp
      (hq.dvd_of_dvd_pow h9)
    subst q
    exact dvd_trans (by norm_num : 3 ∣ 6) (dvd_mul_right 6 k)

/-- The first genuine branch beyond the finite 2,3,7,43 predecessor-square
closure. This is a divisibility restriction, not an infinitude theorem. -/
theorem thirteen_or_nineteen_sq_dvd {n : ℕ} (hn : 0 < n)
    (huniq : ∀ m : ℕ, m.totient = n.totient → m = n) :
    13 ^ 2 ∣ n ∨ 19 ^ 2 ∣ n := by
  by_cases h27 : 27 ∣ n
  · exact Or.inr (nineteen_sq_dvd_of_twenty_seven_dvd hn huniq h27)
  · exact Or.inl (thirteen_sq_dvd_of_not_twenty_seven_dvd hn huniq h27)

end Contribution.CarmichaelTotient.GlobalStrongerForcing

namespace Contribution.CarmichaelTotient

/-- Multiplying a positive equal-totient pair by a prime preserves its common
totient exactly when that prime divides both inputs or neither input. -/
theorem prime_scaling_totient_iff {a b p : ℕ} (ha : 0 < a)
    (hφ : a.totient = b.totient) (hp : p.Prime) :
    (p * a).totient = (p * b).totient ↔ (p ∣ a ↔ p ∣ b) := by
  have hφpos : 0 < a.totient := Nat.totient_pos.mpr ha
  have hpred : p - 1 + 1 = p := by have := hp.two_le; omega
  by_cases hpa : p ∣ a <;> by_cases hpb : p ∣ b
  · simp only [hpa, hpb, iff_true]
    rw [Nat.totient_mul_of_prime_of_dvd hp hpa,
      Nat.totient_mul_of_prime_of_dvd hp hpb, hφ]
  · simp only [hpa, hpb, iff_false, not_true_eq_false, iff_false]
    rw [Nat.totient_mul_of_prime_of_dvd hp hpa,
      Nat.totient_mul_of_prime_of_not_dvd hp hpb, ← hφ]
    nlinarith
  · simp only [hpa, hpb, iff_true, iff_false]
    rw [Nat.totient_mul_of_prime_of_not_dvd hp hpa,
      Nat.totient_mul_of_prime_of_dvd hp hpb, ← hφ]
    nlinarith
  · simp only [hpa, hpb, iff_true]
    rw [Nat.totient_mul_of_prime_of_not_dvd hp hpa,
      Nat.totient_mul_of_prime_of_not_dvd hp hpb, hφ]

/-- The prime-scaling criterion suffices for every exponent, without requiring
the complementary factor to be coprime to the collision pair. -/
theorem prime_power_scaling_totient {a b p : ℕ} (ha : 0 < a)
    (hφ : a.totient = b.totient) (hp : p.Prime)
    (hdiv : p ∣ a ↔ p ∣ b) (k : ℕ) :
    (p ^ k * a).totient = (p ^ k * b).totient := by
  induction k with
  | zero => simpa using hφ
  | succ k ih =>
    have hdiv' : p ∣ p ^ k * a ↔ p ∣ p ^ k * b := by
      simp only [hp.dvd_mul, hdiv]
    have hpos : 0 < p ^ k * a := Nat.mul_pos (pow_pos hp.pos k) ha
    have h := (prime_scaling_totient_iff hpos ih hp).mpr hdiv'
    simpa only [pow_succ', mul_assoc] using h

/-- A genuine collision generates a distinct equal-totient pair at every
prime-power scale satisfying the exact divisibility criterion. -/
theorem prime_power_scaling_collision {a b p : ℕ} (ha : 0 < a)
    (hab : a ≠ b) (hφ : a.totient = b.totient) (hp : p.Prime)
    (hdiv : p ∣ a ↔ p ∣ b) (k : ℕ) :
    p ^ k * a ≠ p ^ k * b ∧
    (p ^ k * a).totient = (p ^ k * b).totient := by
  constructor
  · intro h
    exact hab (Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos k) h)
  · exact prime_power_scaling_totient ha hφ hp hdiv k

end Contribution.CarmichaelTotient

namespace Contribution.CarmichaelTotient.ClosureAudit

theorem divisor_1806_cases {d : ℕ} (hd : d ∣ 1806) :
    d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 6 ∨ d = 7 ∨ d = 14 ∨
    d = 21 ∨ d = 42 ∨ d = 43 ∨ d = 86 ∨ d = 129 ∨ d = 258 ∨
    d = 301 ∨ d = 602 ∨ d = 903 ∨ d = 1806 := by
  have hfac : d ∣ 2 * (3 * (7 * 43)) := hd
  rcases Nat.dvd_mul.mp hfac with ⟨a, b, ha, hb, rfl⟩
  rcases Nat.dvd_mul.mp hb with ⟨c, e, hc, he, rfl⟩
  rcases Nat.dvd_mul.mp he with ⟨f, g, hf, hg, rfl⟩
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp ha with rfl | rfl <;>
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hc with rfl | rfl <;>
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hf with rfl | rfl <;>
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 43)).mp hg with rfl | rfl <;>
    norm_num

/-- Every prime eligible under the weak rule already belongs to the seed set. -/
theorem eligible_prime_cases {p : ℕ} (hp : Nat.Prime p)
    (hpred : (p - 1) ^ 2 ∣ 3261636) :
    p = 2 ∨ p = 3 ∨ p = 7 ∨ p = 43 := by
  have hd : p - 1 ∣ 1806 :=
    (Nat.pow_dvd_pow_iff (by decide : (2 : ℕ) ≠ 0)).mp hpred
  have hcases := divisor_1806_cases hd
  have hpos := hp.two_le
  have hpval : p = (p - 1) + 1 := by omega
  rcases hcases with h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h <;>
    rw [h] at hpval <;> norm_num at hpval <;> subst p <;>
    norm_num at hp <;> norm_num

/-- Iterating this rule cannot add a prime square to this positive seed. -/
theorem predecessor_square_fixed_point :
    0 < (3261636 : ℕ) ∧
      ∀ p : ℕ, p.Prime → (p - 1) ^ 2 ∣ 3261636 → p ^ 2 ∣ 3261636 := by
  refine ⟨by norm_num, ?_⟩
  intro p hp hpred
  rcases eligible_prime_cases hp hpred with rfl | rfl | rfl | rfl <;> norm_num

/-- In particular, the weak rule alone cannot require more than these four primes. -/
theorem no_new_prime_from_seed :
    ¬ ∃ p : ℕ, p.Prime ∧ (p - 1) ^ 2 ∣ 3261636 ∧ ¬ p ∣ 3261636 := by
  rintro ⟨p, hp, hpred, hnot⟩
  exact hnot (Nat.dvd_of_pow_dvd (by decide)
    (predecessor_square_fixed_point.2 p hp hpred))

end Contribution.CarmichaelTotient.ClosureAudit

namespace Contribution.CarmichaelTotient.Klee

open GlobalStrongerForcing

/-- A prime already present in a singleton preimage has exponent at least two
when every prime factor of its predecessor is also present. -/
theorem prime_sq_dvd_of_prime_and_pred_support {n p : ℕ} (hn : 0 < n)
    (huniq : ∀ m : ℕ, m.totient = n.totient → m = n)
    (hp : p.Prime) (hpn : p ∣ n)
    (hsupport : ∀ q : ℕ, q.Prime → q ∣ p - 1 → q ∣ n) : p ^ 2 ∣ n := by
  obtain ⟨a, rfl⟩ := hpn
  by_cases hpa : p ∣ a
  · simpa [pow_two] using Nat.mul_dvd_mul_left p hpa
  have hpredpos : 0 < p - 1 := by have := hp.two_le; omega
  have hsupporta : ∀ q : ℕ, q.Prime → q ∣ p - 1 → q ∣ a := by
    intro q hq hqd
    have hqp : ¬ q ∣ p := by
      intro h
      have heq : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp h
      subst q
      have := Nat.le_of_dvd hpredpos hqd
      omega
    exact (hq.dvd_mul.mp (hsupport q hq hqd)).resolve_left hqp
  have hphi : ((p - 1) * a).totient = (p * a).totient := by
    rw [totient_mul_of_prime_support hsupporta,
      Nat.totient_mul_of_prime_of_not_dvd hp hpa]
  have heq := huniq ((p - 1) * a) hphi
  have ha : 0 < a := Nat.pos_of_mul_pos_left hn
  have hpadd : p - 1 + 1 = p := by have := hp.two_le; omega
  nlinarith

/-- Carmichael--Klee forcing in a factorized prime-support form. Writing
`n = d * (e * a)` expresses the quotient in Ford's lemma without natural
division. The multiplier `e` introduces no new primes into `a`.

This is an unbounded implication; it does not assert that infinitely many
primes satisfy its hypotheses. -/
theorem carmichael_klee_support {n d e a p : ℕ} (hn : 0 < n)
    (huniq : ∀ m : ℕ, m.totient = n.totient → m = n)
    (hdecomp : n = d * (e * a)) (hcop : d.Coprime (e * a))
    (hsupporte : ∀ q : ℕ, q.Prime → q ∣ e → q ∣ a)
    (hsupportphi : ∀ q : ℕ, q.Prime → q ∣ d.totient → q ∣ n)
    (hp : p.Prime) (hprime : p = 1 + e * d.totient) : p ^ 2 ∣ n := by
  have hpred : p - 1 = e * d.totient := by omega
  have hen : e ∣ n := by
    rw [hdecomp]
    exact dvd_mul_of_dvd_right (dvd_mul_right e a) d
  have hpredsupport : ∀ q : ℕ, q.Prime → q ∣ p - 1 → q ∣ n := by
    intro q hq hqd
    rw [hpred] at hqd
    rcases hq.dvd_mul.mp hqd with hqe | hqphi
    · exact dvd_trans hqe hen
    · exact hsupportphi q hq hqphi
  apply prime_sq_dvd_of_prime_and_pred_support hn huniq hp _ hpredsupport
  by_contra hpn
  have han : a ∣ n := by
    rw [hdecomp]
    exact dvd_mul_of_dvd_right (dvd_mul_left a e) d
  have hpa : ¬ p ∣ a := fun h => hpn (dvd_trans h han)
  have hphi : (p * a).totient = n.totient := by
    rw [Nat.totient_mul_of_prime_of_not_dvd hp hpa, hpred, hdecomp,
      Nat.totient_mul hcop, totient_mul_of_prime_support hsupporte]
    ring
  have heq := huniq (p * a) hphi
  exact hpn (heq ▸ dvd_mul_right p a)

open scoped BigOperators

/-- The quotient and squarefree-kernel formulation of Carmichael--Klee,
matching the hypotheses of Ford, The distribution of totients, Lemma 7.2. -/
theorem carmichael_klee {n d e p : ℕ} (hn : 0 < n)
    (huniq : ∀ m : ℕ, m.totient = n.totient → m = n)
    (hd : d ∣ n) (hcop : d.Coprime (n / d))
    (hphi : (∏ q ∈ d.totient.primeFactors, q) ∣ n)
    (he : e ∣ (n / d) / (∏ q ∈ (n / d).primeFactors, q))
    (hp : p.Prime) (hprime : p = 1 + e * d.totient) : p ^ 2 ∣ n := by
  let y := n / d
  let r := ∏ q ∈ y.primeFactors, q
  have hr : r ∣ y := Nat.prod_primeFactors_dvd y
  have hnprod : d * y = n := Nat.mul_div_cancel' hd
  have hypos : 0 < y := Nat.pos_of_mul_pos_left (hnprod ▸ hn)
  have hdpos : 0 < d := Nat.pos_of_mul_pos_right (hnprod ▸ hn)
  obtain ⟨a, ha⟩ := he
  have hy : y = e * (r * a) := by
    calc
      y = r * (y / r) := (Nat.mul_div_cancel' hr).symm
      _ = r * (e * a) := by rw [show y / r = e * a from ha]
      _ = e * (r * a) := by ring
  have hnrepr : n = d * (e * (r * a)) := by rw [← hnprod, hy]
  have hsupporte : ∀ q : ℕ, q.Prime → q ∣ e → q ∣ r * a := by
    intro q hq hqe
    have hqy : q ∣ y := by rw [hy]; exact dvd_mul_of_dvd_left hqe _
    have hmem : q ∈ y.primeFactors := hq.mem_primeFactors hqy hypos.ne'
    have hqr : q ∣ r := Finset.dvd_prod_of_mem (fun q => q) hmem
    exact dvd_mul_of_dvd_left hqr a
  have hsupportphi : ∀ q : ℕ, q.Prime → q ∣ d.totient → q ∣ n := by
    intro q hq hqd
    have hmem : q ∈ d.totient.primeFactors :=
      hq.mem_primeFactors hqd (Nat.totient_pos.mpr hdpos).ne'
    exact dvd_trans (Finset.dvd_prod_of_mem (fun q => q) hmem) hphi
  apply carmichael_klee_support hn huniq hnrepr _ hsupporte hsupportphi hp hprime
  simpa only [← hy] using hcop

end Contribution.CarmichaelTotient.Klee

namespace Contribution.CarmichaelTotient.PomeranceSupport

/-- Euler's product has positive predecessor factors because all its factors are prime. -/
theorem predecessor_product_pos (n : ℕ) :
    0 < ∏ p ∈ n.primeFactors, (p - 1) := by
  apply Finset.prod_pos
  intro p hp
  have := (Nat.prime_of_mem_primeFactors hp).two_le
  omega

/-- Equal totients determine the input once the set of prime divisors is fixed. -/
theorem eq_of_totient_eq_of_primeFactors_eq {a b : ℕ}
    (hφ : a.totient = b.totient) (hprimes : a.primeFactors = b.primeFactors) :
    a = b := by
  have ha := Nat.totient_mul_prod_primeFactors a
  have hb := Nat.totient_mul_prod_primeFactors b
  rw [hφ, hprimes] at ha
  apply Nat.eq_of_mul_eq_mul_right (predecessor_product_pos b)
  exact ha.symm.trans hb

/-- Cancelling common prime factors in Euler's product isolates exactly the
prime divisors present in `n` but missing from `m`. -/
theorem missing_prime_product_identity {m n : ℕ}
    (hφ : m.totient = n.totient) (hsubset : m.primeFactors ⊆ n.primeFactors) :
    n * (∏ p ∈ n.primeFactors \ m.primeFactors, (p - 1)) =
      m * (∏ p ∈ n.primeFactors \ m.primeFactors, p) := by
  have hm := Nat.totient_mul_prod_primeFactors m
  have hn := Nat.totient_mul_prod_primeFactors n
  have hrad : (∏ p ∈ n.primeFactors \ m.primeFactors, p) *
      (∏ p ∈ m.primeFactors, p) = ∏ p ∈ n.primeFactors, p :=
    Finset.prod_sdiff hsubset
  have hpred : (∏ p ∈ n.primeFactors \ m.primeFactors, (p - 1)) *
      (∏ p ∈ m.primeFactors, (p - 1)) = ∏ p ∈ n.primeFactors, (p - 1) :=
    Finset.prod_sdiff hsubset
  rw [← hφ, ← hrad, ← hpred] at hn
  apply Nat.eq_of_mul_eq_mul_right (predecessor_product_pos m)
  nlinarith [congrArg (fun t => t * (∏ p ∈ n.primeFactors \ m.primeFactors, p)) hm]

end Contribution.CarmichaelTotient.PomeranceSupport


namespace Contribution.CarmichaelTotient.PomeranceCriterion

open Finset

lemma prime_dvd_prod_exists {s : Finset ℕ} {p : ℕ} (hp : Nat.Prime p)
    (hd : p ∣ ∏ q ∈ s, q) : ∃ q ∈ s, p ∣ q := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty] at hd
    exact (hp.not_dvd_one hd).elim
  | @insert q s hqs ih =>
    rw [Finset.prod_insert hqs] at hd
    rcases hp.dvd_mul.mp hd with hq | hs
    · exact ⟨q, Finset.mem_insert_self q s, hq⟩
    · obtain ⟨r, hrs, hpr⟩ := ih hs
      exact ⟨r, Finset.mem_insert_of_mem hrs, hpr⟩

/-- A product of distinct primes is divisible by no prime square. -/
lemma prime_sq_not_dvd_prime_prod {s : Finset ℕ}
    (hs : ∀ q ∈ s, Nat.Prime q) {p : ℕ} (hp : Nat.Prime p) :
    ¬ p ^ 2 ∣ ∏ q ∈ s, q := by
  intro hsq
  have hd : p ∣ ∏ q ∈ s, q := Nat.dvd_of_pow_dvd (by decide) hsq
  obtain ⟨q, hqs, hpq⟩ := prime_dvd_prod_exists hp hd
  have hpqeq : p = q := (Nat.prime_dvd_prime_iff_eq hp (hs q hqs)).mp hpq
  have hps : p ∈ s := hpqeq ▸ hqs
  have hprod : (∏ q ∈ s, q) = p * ∏ q ∈ s.erase p, q := by
    exact (Finset.mul_prod_erase s (fun q : ℕ => q) hps).symm
  rw [hprod, pow_two] at hsq
  have hd' : p ∣ ∏ q ∈ s.erase p, q := Nat.dvd_of_mul_dvd_mul_left hp.pos hsq
  obtain ⟨q, hqs, hpq⟩ := prime_dvd_prod_exists hp hd'
  have heq : p = q :=
    (Nat.prime_dvd_prime_iff_eq hp (hs q (Finset.mem_of_mem_erase hqs))).mp hpq
  exact (Finset.ne_of_mem_erase hqs) heq.symm

/-- No new square of a prime can appear by multiplying a number coprime to
that prime by a product of distinct primes. -/
lemma prime_sq_not_dvd_mul_prime_prod {s : Finset ℕ}
    (hs : ∀ q ∈ s, Nat.Prime q) {p m : ℕ} (hp : Nat.Prime p) (hpm : ¬ p ∣ m) :
    ¬ p ^ 2 ∣ m * ∏ q ∈ s, q := by
  intro hsq
  have hcop : Nat.Coprime (p ^ 2) m := (hp.coprime_iff_not_dvd.mpr hpm).pow_left 2
  exact prime_sq_not_dvd_prime_prod hs hp (hcop.dvd_of_dvd_mul_left hsq)

/-- Pomerance's finite divisibility criterion is sufficient for global
uniqueness of a positive totient preimage. Its hypothesis is substantially
stronger than predecessor-square closure. -/
theorem singleton_of_prime_predecessor_criterion {n : ℕ} (hn : 0 < n)
    (hcriterion : ∀ p : ℕ, Nat.Prime p → p - 1 ∣ n.totient → p ^ 2 ∣ n) :
    ∀ m : ℕ, m.totient = n.totient → m = n := by
  intro m hφ
  have hm : 0 < m := Nat.totient_pos.mp (by rw [hφ]; exact Nat.totient_pos.mpr hn)
  have hpred {a p : ℕ} (hp : Nat.Prime p) (hpa : p ∣ a) : p - 1 ∣ a.totient := by
    simpa only [Nat.totient_prime hp] using Nat.totient_dvd_of_dvd hpa
  have hsub : m.primeFactors ⊆ n.primeFactors := by
    intro p hpm
    have hp := Nat.prime_of_mem_primeFactors hpm
    have hpφ : p - 1 ∣ n.totient := by
      rw [← hφ]
      exact hpred hp (Nat.dvd_of_mem_primeFactors hpm)
    exact Nat.mem_primeFactors.mpr ⟨hp,
      Nat.dvd_of_pow_dvd (by decide) (hcriterion p hp hpφ), hn.ne'⟩
  have hidentity := PomeranceSupport.missing_prime_product_identity hφ hsub
  have hrev : n.primeFactors ⊆ m.primeFactors := by
    intro p hpn
    by_contra hpm
    have hp := Nat.prime_of_mem_primeFactors hpn
    have hpnot : ¬ p ∣ m := by
      intro hdiv
      exact hpm (Nat.mem_primeFactors.mpr ⟨hp, hdiv, hm.ne'⟩)
    have hpsq : p ^ 2 ∣ n :=
      hcriterion p hp (hpred hp (Nat.dvd_of_mem_primeFactors hpn))
    have hdiv : p ^ 2 ∣ m * ∏ q ∈ n.primeFactors \ m.primeFactors, q := by
      rw [← hidentity]
      exact dvd_mul_of_dvd_left hpsq _
    exact prime_sq_not_dvd_mul_prime_prod
      (fun q hq => Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hq).1) hp hpnot hdiv
  exact PomeranceSupport.eq_of_totient_eq_of_primeFactors_eq hφ (Finset.Subset.antisymm hsub hrev)

/-- The criterion can be checked on the finite divisor set of `φ(n)`.
No search cutoff occurs in the resulting uniqueness conclusion. -/
theorem singleton_of_divisor_certificate {n : ℕ} (hn : 0 < n)
    (hcertificate : ∀ d ∈ n.totient.divisors,
      Nat.Prime (d + 1) → (d + 1) ^ 2 ∣ n) :
    ∀ m : ℕ, m.totient = n.totient → m = n := by
  apply singleton_of_prime_predecessor_criterion hn
  intro p hp hpred
  have hpadd : p - 1 + 1 = p := by have := hp.two_le; omega
  have hd : p - 1 ∈ n.totient.divisors :=
    Nat.mem_divisors.mpr ⟨hpred, (Nat.totient_pos.mpr hn).ne'⟩
  simpa only [hpadd] using hcertificate (p - 1) hd (by simpa only [hpadd] using hp)

/-- A positive integer satisfying the finite certificate would globally
refute Carmichael's conjecture. This theorem does not assert that such an
integer exists. -/
theorem refutes_carmichael_of_divisor_certificate {n : ℕ} (hn : 0 < n)
    (hcertificate : ∀ d ∈ n.totient.divisors,
      Nat.Prime (d + 1) → (d + 1) ^ 2 ∣ n) :
    ¬ (∀ a : ℕ, 0 < a → ∃ b : ℕ, b ≠ a ∧ b.totient = a.totient) := by
  intro hall
  obtain ⟨m, hmn, hφ⟩ := hall n hn
  exact hmn (singleton_of_divisor_certificate hn hcertificate m hφ)

end Contribution.CarmichaelTotient.PomeranceCriterion

namespace Contribution.CarmichaelTotient.SquareKernelCriterion

/-- Pomerance's sufficient criterion for a singleton totient fiber. -/
def Criterion (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p - 1 ∣ n.totient → p ^ 2 ∣ n

/-- The square of the product of the distinct prime divisors. -/
def squareKernel (n : ℕ) : ℕ := (∏ p ∈ n.primeFactors, p) ^ 2

/-- Every prime divisor of a witness to the criterion occurs at least twice. -/
theorem prime_sq_dvd_of_criterion {n p : ℕ} (h : Criterion n)
    (hp : p.Prime) (hpn : p ∣ n) : p ^ 2 ∣ n := by
  apply h p hp
  rw [← Nat.totient_prime hp]
  exact Nat.totient_dvd_of_dvd hpn

/-- The square-kernel of a positive witness to the criterion divides it. -/
theorem squareKernel_dvd {n : ℕ} (hn : 0 < n) (h : Criterion n) :
    squareKernel n ∣ n := by
  unfold squareKernel
  rw [← Finset.prod_pow]
  conv_rhs => rw [Nat.prod_primeFactors_pow_factorization hn.ne']
  apply Finset.prod_dvd_prod_of_dvd
  intro p hpn
  have hp := Nat.prime_of_mem_primeFactors hpn
  apply Nat.pow_dvd_pow
  exact (hp.pow_dvd_iff_le_factorization hn.ne').mp
    (prime_sq_dvd_of_criterion h hp (Nat.dvd_of_mem_primeFactors hpn))

/-- A product of primes, including the empty product, is positive. -/
theorem squareKernel_pos (n : ℕ) : 0 < squareKernel n := by
  unfold squareKernel
  apply pow_pos
  exact Finset.prod_pos (fun p hp => Nat.pos_of_mem_primeFactors hp)

/-- Passing to the square-kernel preserves Pomerance's sufficient criterion. -/
theorem criterion_squareKernel {n : ℕ} (hn : 0 < n) (h : Criterion n) :
    Criterion (squareKernel n) := by
  intro p hp hpred
  have hp2n : p ^ 2 ∣ n :=
    h p hp (dvd_trans hpred (Nat.totient_dvd_of_dvd (squareKernel_dvd hn h)))
  have hpn : p ∣ n := Nat.dvd_of_pow_dvd (by decide) hp2n
  have hmem : p ∈ n.primeFactors := hp.mem_primeFactors hpn hn.ne'
  have hprad : p ∣ ∏ q ∈ n.primeFactors, q :=
    Finset.dvd_prod_of_mem (fun q : ℕ => q) hmem
  exact pow_dvd_pow_of_dvd hprad 2

/-- Existence of a positive criterion witness reduces exactly to witnesses
that are squares of products of distinct primes. No infinitude or existence
assumption is hidden in this equivalence. -/
theorem exists_criterion_iff_squareKernel :
    (∃ n : ℕ, 0 < n ∧ Criterion n) ↔
      ∃ n : ℕ, 0 < n ∧ Criterion (squareKernel n) := by
  constructor
  · rintro ⟨n, hn, h⟩
    exact ⟨n, hn, criterion_squareKernel hn h⟩
  · rintro ⟨n, _, h⟩
    exact ⟨squareKernel n, squareKernel_pos n, h⟩

end Contribution.CarmichaelTotient.SquareKernelCriterion
