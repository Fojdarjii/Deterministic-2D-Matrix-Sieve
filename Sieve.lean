import Mathlib.Data.Nat.Prime
import Mathlib.Tactic.IntervalCases

-- 1. क्षैतिज अक्ष (Horizontal Coordinate Space)
def CoordinateCandidates (X : ℕ) : Set ℕ :=
  { n | n ≤ X ∧ (n % 6 = 1 ∨ n % 6 = 5) }

-- 2. ऊर्ध्वाधर अक्ष (Vertical Multiplier Space)
def BoundMultipliers (X : ℕ) : Set ℕ :=
  { p | Nat.Prime p ∧ p * p ≤ X ∧ p > 3 }

-- 3. ग्रिड इंटरसेक्शन (The Intersection Matrix)
def PureCompositeMatrix (X : ℕ) : Set ℕ :=
  { c | c ≤ X ∧ ∃ p ∈ BoundMultipliers X, p ∣ c ∧ p < c }

-- लेम्मा: 3 से बड़े प्राइम्स अनिवार्य रूप से 6k ± 1 होते हैं
lemma mod6_structural_limit {n : ℕ} (hn_gt3 : n > 3) (hn_p : Nat.Prime n) :
    n % 6 = 1 ∨ n % 6 = 5 := by
  have h_lt : n % 6 < 6 := Nat.mod_lt n (by norm_num)
  have h_eq : n = 6 * (n / 6) + (n % 6) := (Nat.div_add_mod n 6).symm
  have h0 : n % 6 ≠ 0 := by
    rintro h
    have hd : 6 ∣ n := Nat.dvd_of_mod_eq_zero h
    have h2 : 2 ∣ n := dvd_trans (by norm_num) hd
    have : n = 2 := hn_p.eq_one_or_self_of_dvd 2 h2 |>.resolve_left (by omega)
    omega
  have h2 : n % 6 ≠ 2 := by
    rintro h
    have hd : 2 ∣ (n % 6) := by rw [h]; exact dvd_rfl
    have h_dvd_6 : 2 ∣ 6 * (n / 6) := by use 3 * (n / 6); ring
    have : 2 ∣ n := by rw [h_eq]; exact dvd_add h_dvd_6 hd
    have : n = 2 := hn_p.eq_one_or_self_of_dvd 2 this |>.resolve_left (by omega)
    omega
  have h3 : n % 6 ≠ 3 := by
    rintro h
    have hd : 3 ∣ (n % 6) := by rw [h]; exact dvd_rfl
    have h_dvd_6 : 3 ∣ 6 * (n / 6) := by use 2 * (n / 6); ring
    have : 3 ∣ n := by rw [h_eq]; exact dvd_add h_dvd_6 hd
    have : n = 3 := hn_p.eq_one_or_self_of_dvd 3 this |>.resolve_left (by omega)
    omega
  have h4 : n % 6 ≠ 4 := by
    rintro h
    have hd : 2 ∣ (n % 6) := by rw [h]; use 2
    have h_dvd_6 : 2 ∣ 6 * (n / 6) := by use 3 * (n / 6); ring
    have : 2 ∣ n := by rw [h_eq]; exact dvd_add h_dvd_6 hd
    have : n = 2 := hn_p.eq_one_or_self_of_dvd 2 this |>.resolve_left (by omega)
    omega
  generalize hmod : n % 6 = r at *
  interval_cases r <;> omega

-- मुख्य सार्वभौमिक थ्योरम (The Universal 2D Sieve Equation)
theorem perfect_sieve_proof (X : ℕ) :
    { n | n ≤ X ∧ Nat.Prime n ∧ n > 3 } = CoordinateCandidates X \ PureCompositeMatrix X := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_diff]
  constructor
  · rintro ⟨hX, hn_prime, hn_gt3⟩
    constructor
    · exact ⟨hX, mod6_structural_limit hn_gt3 hn_prime⟩
    · rintro ⟨-, p, ⟨hp_prime, _, _⟩, hp_dvd, hp_lt⟩
      have hp_eq : p = 1 ∨ p = n := hn_prime.eq_one_or_self_of_dvd p hp_dvd
      rcases hp_eq with rfl | rfl
      · exact hp_prime.ne_one rfl
      · omega
  · rintro ⟨⟨hX, h_mod⟩, hn_not_comp⟩
    refine ⟨hX, ?_, ?_⟩
    · rw [Nat.prime_def_le_sqrt]
      refine ⟨?_, ?_⟩
      · rcases h_mod with h | h <;> omega
      · intro p hp_prime hp_dvd hp_sq
        have hp_gt3 : p > 3 := by
          by_contra h_le3
          have hp_cases : p = 2 ∨ p = 3 := by
            have : p ≠ 0 := hp_prime.ne_zero
            have : p ≠ 1 := hp_prime.ne_one
            omega
          have h_eq : n = 6 * (n / 6) + (n % 6) := (Nat.div_add_mod n 6).symm
          rcases hp_cases with rfl | rfl
          · have hd : 2 ∣ n := hp_dvd
            have h_dvd_6 : 2 ∣ 6 * (n / 6) := by use 3 * (n / 6); ring
            have h_rem : 2 ∣ (n % 6) := by
              have h_sub : n % 6 = n - 6 * (n / 6) := by omega
              rw [h_sub]
              exact Nat.dvd_sub (Nat.div_mul_le n 6) hd h_dvd_6
            rcases h_mod with h | h <;> (rw [h] at h_rem; revert h_rem; norm_num)
          · have hd : 3 ∣ n := hp_dvd
            have h_dvd_6 : 3 ∣ 6 * (n / 6) := by use 2 * (n / 6); ring
            have h_rem : 3 ∣ (n % 6) := by
              have h_sub : n % 6 = n - 6 * (n / 6) := by omega
              rw [h_sub]
              exact Nat.dvd_sub (Nat.div_mul_le n 6) hd h_dvd_6
            rcases h_mod with h | h <;> (rw [h] at h_rem; revert h_rem; norm_num)
        have hp_sq_le : p * p ≤ X := by
          have : p * p ≤ n := hp_sq
          omega
        have hp_lt : p < n := by
          have h_neq : p ≠ n := by
            rintro rfl
            have h_sq_n : n * n ≤ n := hp_sq
            have : n ≤ 1 := by
              rcases n with _ | _
              · omega
              · rcases n with _ | _
                · omega
                · nlinarith
            omega
          have hp_le : p ≤ n := by
            have : p * p ≤ n := hp_sq
            have : p ≥ 5 := by omega
            nlinarith
          omega
        have h_matrix_trap : n ∈ PureCompositeMatrix X := ⟨hX, p, ⟨hp_prime, hp_sq_le, hp_gt3⟩, hp_dvd, hp_lt⟩
        exact hn_not_comp h_matrix_trap
    · rcases h_mod with h | h <;> omega
