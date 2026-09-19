import Mathlib.Data.Nat.Prime
import Mathlib.Tactic.IntervalCases

def CoordinateCandidates (X : ℕ) : Set ℕ :=
  { n | n ≤ X ∧ (n % 6 = 1 ∨ n % 6 = 5) }

def DynamicMultipliers (X : ℕ) : Set ℕ :=
  { m | m ∈ CoordinateCandidates X ∧ m * m ≤ X }

def TwoWayCompositeMatrix (X : ℕ) : Set ℕ :=
  { c | c ≤ X ∧ ∃ m1 ∈ DynamicMultipliers X, ∃ m2 ∈ CoordinateCandidates X, c = m1 * m2 }

theorem perfect_two_way_sieve_equality (X : ℕ) :
  { n | n ≤ X ∧ Nat.Prime n ∧ n > 3 } = CoordinateCandidates X \ TwoWayCompositeMatrix X := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_diff]
  constructor
  · rintro ⟨hX, hn_prime, hn_gt3⟩
    constructor
    · refine ⟨hX, ?_⟩
      have h_mod6 : n % 6 ≠ 0 ∧ n % 6 ≠ 2 ∧ n % 6 ≠ 3 ∧ n % 6 ≠ 4 := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · rintro (h0 : n % 6 = 0)
          have : 6 ∣ n := Nat.dvd_of_mod_eq_zero h0
          have : 2 ∣ n := dvd_trans (by norm_num) this
          have : n = 2 := hn_prime.eq_one_or_self_of_dvd 2 this |>.resolve_left (by omega)
          omega
        · rintro (h2 : n % 6 = 2)
          have : 2 ∣ (n % 6) := by omega
          have : 2 ∣ n := (Nat.dvd_add_iff_left (by norm_num : 2 ∣ (n - n % 6))).mp (by sorry)
          have : n = 2 := hn_prime.eq_one_or_self_of_dvd 2 this |>.resolve_left (by omega)
          omega
        · rintro (h3 : n % 6 = 3)
          have : 3 ∣ n := (Nat.dvd_add_iff_left (by norm_num : 3 ∣ (n - n % 6))).mp (by sorry)
          have : n = 3 := hn_prime.eq_one_or_self_of_dvd 3 this |>.resolve_left (by omega)
          omega
        · rintro (h4 : n % 6 = 4)
          have : 2 ∣ n := (Nat.dvd_add_iff_left (by norm_num : 2 ∣ (n - n % 6))).mp (by sorry)
          have : n = 2 := hn_prime.eq_one_or_self_of_dvd 2 this |>.resolve_left (by omega)
          omega
      have h_bound : n % 6 < 6 := Nat.mod_lt n (by norm_num)
      omega
    · rintro ⟨-, m1, ⟨⟨hm1_cand_bound, hm1_mod⟩, hm1_sq⟩, m2, ⟨hm2_cand_bound, hm2_mod⟩, rfl⟩
      have hm1_gt1 : m1 > 1 := by
        rcases hm1_mod with h | h <;> {
          have : m1 ≠ 0 := by rintro rfl; norm_num at h
          have : m1 ≠ 1 := by rintro rfl; norm_num at h
          omega
        }
      have hm2_gt1 : m2 > 1 := by
        rcases hm2_mod with h | h <;> {
          have : m2 ≠ 0 := by rintro rfl; norm_num at h
          have : m2 ≠ 1 := by rintro rfl; norm_num at h
          omega
        }
      exact Nat.not_prime_mul hm1_gt1 hm2_gt1 hn_prime
  · rintro ⟨⟨hX, h_mod⟩, hn_not_matrix⟩
    refine ⟨hX, ?_, ?_⟩
    · by_contra hc
      obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd hc
      have hp_gt3 : p > 3 := by
        by_contra h_le3
        have hp_cases : p = 2 ∨ p = 3 := by 
          have : p ≠ 0 := hp_prime.ne_zero
          have : p ≠ 1 := hp_prime.ne_one
          omega
        rcases hp_cases with rfl | rfl
        · have : 2 ∣ n := hp_dvd
          rcases h_mod with h | h
          · have : 2 ∣ (n % 6) := by sorry
            omega
          · have : 2 ∣ (n % 6) := by sorry
            omega
        · have : 3 ∣ n := hp_dvd
          rcases h_mod with h | h
          · have : 3 ∣ (n % 6) := by sorry
            omega
          · have : 3 ∣ (n % 6) := by sorry
            omega
      have h_p_cand : p % 6 = 1 ∨ p % 6 = 5 := by
        have h_mod6 := Nat.mod_lt p (by norm_num)
        have h_not_zero : p % 6 ≠ 0 := by rintro h0; have : 6 ∣ p := Nat.dvd_of_mod_eq_zero h0; have : 2 ∣ p := dvd_trans (by norm_num) this; have : p = 2 := hp_prime.eq_one_or_self_of_dvd 2 this |>.resolve_left (by norm_num); omega
        have h_not_two : p % 6 ≠ 2 := by rintro h2; have : 2 ∣ p := by sorry; have : p = 2 := hp_prime.eq_one_or_self_of_dvd 2 this |>.resolve_left (by norm_num); omega
        have h_not_three : p % 6 ≠ 3 := by rintro h3; have : 3 ∣ p := by sorry; have : p = 3 := hp_prime.eq_one_or_self_of_dvd 3 this |>.resolve_left (by norm_num); omega
        have h_not_four : p % 6 ≠ 4 := by rintro h4; have : 2 ∣ p := by sorry; have : p = 2 := hp_prime.eq_one_or_self_of_dvd 2 this |>.resolve_left (by norm_num); omega
        omega
      obtain ⟨k, rfl⟩ := hp_dvd
      have hk_cand : k % 6 = 1 ∨ k % 6 = 5 := by
        rcases h_mod with h | h
        · have : (p * k) % 6 = 1 := h
          sorry
        · have : (p * k) % 6 = 5 := h
          sorry
      have hk_le_X : k ≤ X := by
        have : p ≥ 5 := by omega
        nlinarith
      have hp_le_X : p ≤ X := by
        have : k ≥ 1 := by 
          have : p * k ≠ 0 := by rintro h0; have : p * k ≤ X := by exact hX; omega
          omega
        nlinarith
      have h_matrix_leak : p * k ∈ TwoWayCompositeMatrix X := by
        refine ⟨hX, p, ⟨⟨hp_le_X, h_p_cand⟩, ?_⟩, k, ⟨hk_le_X, hk_cand⟩, rfl⟩
        by_contra h_sq_gt
        have : k < p := by sorry
        sorry
      exact hn_not_matrix h_matrix_leak
    · rcases h_mod with h | h
      · have : n ≠ 1 := by rintro rfl; norm_num at h
        omega
      · omega
