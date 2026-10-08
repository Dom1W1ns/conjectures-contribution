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
