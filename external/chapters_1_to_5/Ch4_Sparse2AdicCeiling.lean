/-!
# Chapter 4: Exact 2-Adic Valuation Ceilings for Sparse Decimals (`M(2) = 6`, `M(3) = 13`) & Unconditional `∀ m ≥ 14, w(2^m) ≥ 5` (Lean 4)

Self-contained pure Lean 4.16.0 core (zero Mathlib, zero `sorry`, zero `native_decide`,
only standard axioms `[propext, Quot.sound]`).

## Driving Question from Chapter 3
Chapter 3 proved that almost all residue classes `r mod 2^(13k)` force `s(N) > 14k` at length `4k`.
Moving from typical residues to the SPECIFIC residue `r = 0` (multiples of `2^k` with `5 ∤ B`),
how high can `v_2(B)` actually get when `B` has only `w(B) ≤ 2` or `w(B) ≤ 3` non-zero decimal digits?
Naive peeling gave `M(2) ≤ 13` and `M(3) ≤ 46`. We compute and prove the **EXACT sharp ceilings**!

## Main Results
1. **Exact 2-Digit Ceiling `M(2) = 6` (`not_pow2_7_dvd_of_weight_le_2`, tight at `64 = 2^6`)**:
   For EVERY `B ≥ 1` with `5 ∤ B` and `hammingWeight B ≤ 2`, **`¬ (2 ^ 7 ∣ B)`**!
2. **Exact 3-Digit Ceiling `M(3) = 13` (`not_pow2_14_dvd_of_weight_le_3`, tight at `9003008 = 2^13 * 1099`)**:
   For EVERY `B ≥ 1` with `5 ∤ B` and `hammingWeight B ≤ 3`, **`¬ (2 ^ 14 ∣ B)`**!
   (Collapses the `w(2^m) ≤ 4` bound from `m ≤ 156` all the way down to `m ≤ 46`!)
3. **Complete Unconditional Theorem (`pow2_weight_ge_5_of_ge_14`, tight at `2^13 = 8192`)**:
   **`∀ m ≥ 14, hammingWeight (2^m) ≥ 5`** — NO power of 2 beyond `2^13 = 8192` EVER has
   4 or fewer non-zero decimal digits!
-/

namespace Ch4Sparse2AdicCeiling

def hammingWeight (n : Nat) : Nat :=
  if h : n = 0 then 0
  else (if n % 10 ≠ 0 then 1 else 0) + hammingWeight (n / 10)
termination_by n
decreasing_by omega

def hwFuel : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n = 0 then 0 else (if n % 10 ≠ 0 then 1 else 0) + hwFuel fuel (n / 10)

theorem nat_strong_ind {P : Nat → Prop} (h : ∀ n, (∀ k < n, P k) → P n) : ∀ n, P n :=
  fun n => Nat.strongRecOn n h

theorem hammingWeight_zero : hammingWeight 0 = 0 := by unfold hammingWeight; simp

theorem hammingWeight_eq (n : Nat) :
    hammingWeight n = if n = 0 then 0 else (if n % 10 ≠ 0 then 1 else 0) + hammingWeight (n / 10) := by
  by_cases h : n = 0
  · subst h; unfold hammingWeight; simp
  · rw [if_neg h]; conv => lhs; unfold hammingWeight; simp only [h, dite_false]

theorem hwFuel_le_hammingWeight : ∀ fuel n : Nat, hwFuel fuel n ≤ hammingWeight n := by
  intro fuel; induction fuel with
  | zero => intro n; simp [hwFuel]
  | succ fuel ih =>
    intro n; simp only [hwFuel]
    by_cases h0 : n = 0
    · subst h0; simp [hammingWeight_zero]
    · rw [if_neg h0, hammingWeight_eq n, if_neg h0]; have := ih (n / 10); omega

theorem hammingWeight_pos_of_pos {n : Nat} (hn : n > 0) : hammingWeight n ≥ 1 := by
  refine nat_strong_ind (P := fun n => n > 0 → hammingWeight n ≥ 1) ?_ n hn
  intro n ih hn
  rw [hammingWeight_eq n, if_neg (by omega)]
  by_cases hm : n % 10 ≠ 0
  · rw [if_pos hm]; omega
  · have := ih (n / 10) (by omega) (by omega); omega

theorem pow_pos {b : Nat} (hb : b ≥ 1) (n : Nat) : b ^ n ≥ 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.pow_succ]; exact Nat.mul_le_mul ih hb

theorem pow10_split (k : Nat) : 10 ^ k = 2 ^ k * 5 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, ih]
    have h10 : (10 : Nat) = 2 * 5 := by decide
    rw [h10, ← Nat.mul_assoc, Nat.mul_assoc (2 ^ k) (5 ^ k) 2, Nat.mul_comm (5 ^ k) 2,
        ← Nat.mul_assoc, Nat.mul_assoc]

theorem dvd_of_dvd_add_left {d a b : Nat} (ha : d ∣ a) (hab : d ∣ a + b) : d ∣ b := by
  have h1 : a % d = 0 := Nat.mod_eq_zero_of_dvd ha
  have h2 : (a + b) % d = 0 := Nat.mod_eq_zero_of_dvd hab
  rw [Nat.add_mod, h1, Nat.zero_add, Nat.mod_mod] at h2
  exact Nat.dvd_of_mod_eq_zero h2

theorem not_five_dvd_pow2 (m : Nat) : ¬ (5 ∣ 2 ^ m) := by
  induction m with
  | zero => decide
  | succ m ih =>
    intro h
    have hm : (2 ^ (m + 1)) % 5 = 0 := Nat.mod_eq_zero_of_dvd h
    rw [Nat.pow_succ, Nat.mul_mod] at hm
    exact ih (Nat.dvd_of_mod_eq_zero (by omega))

theorem hammingWeight_split_pow10 :
    ∀ k n : Nat, hammingWeight n = hammingWeight (n / 10 ^ k) + hammingWeight (n % 10 ^ k) := by
  intro k; induction k with
  | zero => intro n; simp [Nat.mod_one, hammingWeight_zero]
  | succ k ih =>
    intro n
    have h10k : 10 ^ k > 0 := pow_pos (by decide : 10 ≥ 1) k
    by_cases hn0 : n = 0
    · subst hn0; simp [hammingWeight_zero]
    · rw [hammingWeight_eq n, if_neg hn0]
      have hrec := ih (n / 10)
      have hdiv : n / 10 ^ (k + 1) = (n / 10) / 10 ^ k := by
        rw [Nat.pow_succ, Nat.mul_comm (10 ^ k) 10, Nat.div_div_eq_div_mul]
      have hmod : n % 10 ^ (k + 1) = n % 10 + 10 * ((n / 10) % 10 ^ k) := by
        have h1 : n = 10 * (n / 10) + n % 10 := by omega
        have h2 : n / 10 = 10 ^ k * ((n / 10) / 10 ^ k) + (n / 10) % 10 ^ k :=
          (Nat.div_add_mod (n / 10) (10 ^ k)).symm
        have h3 : n = 10 ^ (k + 1) * ((n / 10) / 10 ^ k) + (n % 10 + 10 * ((n / 10) % 10 ^ k)) := by
          rw [Nat.pow_succ, Nat.mul_comm (10 ^ k) 10]
          calc n = 10 * (10 ^ k * ((n / 10) / 10 ^ k) + (n / 10) % 10 ^ k) + n % 10 := by rw [← h2]; exact h1
            _ = 10 * 10 ^ k * ((n / 10) / 10 ^ k) + (n % 10 + 10 * ((n / 10) % 10 ^ k)) := by
                rw [Nat.mul_add, Nat.mul_assoc]; omega
        have hlt : n % 10 + 10 * ((n / 10) % 10 ^ k) < 10 ^ (k + 1) := by
          have hlt1 : (n / 10) % 10 ^ k < 10 ^ k := Nat.mod_lt _ h10k
          have hlt2 : n % 10 < 10 := Nat.mod_lt _ (by decide)
          rw [Nat.pow_succ]; omega
        conv => lhs; rw [h3, Nat.mul_add_mod]
        exact Nat.mod_eq_of_lt hlt
      have hw_mod : hammingWeight (n % 10 ^ (k + 1)) =
          (if n % 10 ≠ 0 then 1 else 0) + hammingWeight ((n / 10) % 10 ^ k) := by
        rw [hmod]
        by_cases hrem0 : n % 10 + 10 * ((n / 10) % 10 ^ k) = 0
        · have hd0 : n % 10 = 0 := by omega
          have hq0 : (n / 10) % 10 ^ k = 0 := by omega
          rw [hrem0, hq0, hammingWeight_zero, if_neg (by omega)]
        · rw [hammingWeight_eq, if_neg hrem0]
          have hlt2 : n % 10 < 10 := Nat.mod_lt _ (by decide)
          have hm1 : (n % 10 + 10 * ((n / 10) % 10 ^ k)) % 10 = n % 10 := by omega
          have hd1 : (n % 10 + 10 * ((n / 10) % 10 ^ k)) / 10 = (n / 10) % 10 ^ k := by omega
          rw [hm1, hd1]
      rw [hdiv, hw_mod, hrec]; omega

theorem mod_pow10_dvd_of_dvd {B k : Nat} (hdvd : 2 ^ k ∣ B) : 2 ^ k ∣ B % 10 ^ k := by
  have hdm : B = 10 ^ k * (B / 10 ^ k) + B % 10 ^ k := (Nat.div_add_mod B (10 ^ k)).symm
  have h2k_q : 2 ^ k ∣ 10 ^ k * (B / 10 ^ k) :=
    Nat.dvd_trans (by rw [pow10_split k]; exact Nat.dvd_mul_right _ _) (Nat.dvd_mul_right _ _)
  rw [hdm] at hdvd
  exact dvd_of_dvd_add_left h2k_q hdvd

theorem not_five_dvd_mod_pow10 {B k : Nat} (hk : k ≥ 1) (h5 : ¬ (5 ∣ B)) : ¬ (5 ∣ B % 10 ^ k) := by
  intro h5m
  have h5_10k : 5 ∣ 10 ^ k := by
    cases k with | zero => omega | succ k' => rw [Nat.pow_succ]; exact Nat.dvd_trans (by decide : 5 ∣ 10) (Nat.dvd_mul_left 10 _)
  have hdm : B = 10 ^ k * (B / 10 ^ k) + B % 10 ^ k := (Nat.div_add_mod B (10 ^ k)).symm
  apply h5
  rw [hdm]
  exact Nat.dvd_add (Nat.dvd_trans h5_10k (Nat.dvd_mul_right _ _)) h5m

/-- Every `n` with `w(n) = 1` has the form `d * 10^e` with `1 ≤ d ≤ 9`. -/
theorem ten_mul_digit_pow10 (d e : Nat) : 10 * (d * 10 ^ e) = d * 10 ^ (e + 1) := by
  rw [Nat.pow_succ, Nat.mul_comm 10 (d * 10 ^ e), Nat.mul_assoc]

theorem eq_digit_mul_pow10_of_weight_1 :
    ∀ n : Nat, hammingWeight n = 1 → ∃ d e : Nat, 1 ≤ d ∧ d ≤ 9 ∧ n = d * 10 ^ e := by
  refine nat_strong_ind (P := fun n => hammingWeight n = 1 → ∃ d e : Nat, 1 ≤ d ∧ d ≤ 9 ∧ n = d * 10 ^ e) ?_
  intro n ih hw
  by_cases h0 : n = 0
  · subst h0; rw [hammingWeight_zero] at hw; omega
  · rw [hammingWeight_eq n, if_neg h0] at hw
    by_cases hm : n % 10 ≠ 0
    · rw [if_pos hm] at hw
      have hdiv0 : n / 10 = 0 := by
        by_cases hd : n / 10 = 0
        · exact hd
        · exfalso; have := hammingWeight_pos_of_pos (Nat.pos_of_ne_zero hd); omega
      exact ⟨n % 10, 0, by omega, by omega, by simp; omega⟩
    · rw [if_neg hm, Nat.zero_add] at hw
      obtain ⟨d, e, h1, h9, hq⟩ := ih (n / 10) (by omega) hw
      refine ⟨d, e + 1, h1, h9, ?_⟩
      rw [Nat.pow_succ, ← Nat.mul_assoc, ← hq]; omega

/-! ### Part 1: Exact 2-Digit Ceiling `M(2) = 6` (`¬ 2^7 ∣ B` for `w(B) ≤ 2, 5 ∤ B`) -/

/-- Exact 1-digit ceiling `M(1) = 3`: if `5 ∤ B` and `w(B) ≤ 1`, then `¬ (2^4 ∣ B)`. -/
theorem not_pow2_4_dvd_of_weight_le_1 {B : Nat} (h5 : ¬ (5 ∣ B)) (hw : hammingWeight B ≤ 1) :
    ¬ (2 ^ 4 ∣ B) := by
  have hB_pos : B > 0 := by
    by_cases h0 : B = 0
    · subst h0; exfalso; exact h5 (Nat.dvd_zero 5)
    · omega
  have hw1 : hammingWeight B = 1 := by have := hammingWeight_pos_of_pos hB_pos; omega
  obtain ⟨d, e, h1, h9, hB⟩ := eq_digit_mul_pow10_of_weight_1 B hw1
  have he0 : e = 0 := by
    cases e with
    | zero => rfl
    | succ e' =>
      exfalso; apply h5; rw [hB, Nat.pow_succ]
      exact Nat.dvd_trans (by decide : 5 ∣ 10) (Nat.dvd_trans (Nat.dvd_mul_left 10 _) (Nat.dvd_mul_left _ d))
  subst he0; simp at hB
  intro h16
  have hle := Nat.le_of_dvd (by omega) h16
  have : 2 ^ 4 = 16 := by decide
  omega

/-- Kernel check of all `216` 2-digit numbers `d0 + d1 * 10^e` (`e ∈ {1,2,3}`, `5 ∤ d0`):
    NONE is divisible by `128 = 2^7`! -/
def checkM2 : Bool :=
  ([1, 2, 3, 4, 6, 7, 8, 9] : List Nat).all fun d0 =>
    ([1, 2, 3] : List Nat).all fun e =>
      ([1, 2, 3, 4, 5, 6, 7, 8, 9] : List Nat).all fun d1 =>
        decide ((d0 + d1 * 10 ^ e) % 128 ≠ 0)

theorem checkM2_ok : checkM2 = true := by decide

theorem mem_nonfive_digits {d : Nat} (h1 : 1 ≤ d) (h9 : d ≤ 9) (h5 : d ≠ 5) :
    d ∈ ([1, 2, 3, 4, 6, 7, 8, 9] : List Nat) := by
  have : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem mem_nonzero_digits {d : Nat} (h1 : 1 ≤ d) (h9 : d ≤ 9) :
    d ∈ ([1, 2, 3, 4, 5, 6, 7, 8, 9] : List Nat) := by
  have : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- **HEADLINE 1 — Exact 2-Digit Ceiling `M(2) = 6`**:
    NO integer `B` with `5 ∤ B` and `hammingWeight B ≤ 2` is divisible by `2^7 = 128`! (Tight at `64 = 2^6`.) -/
theorem not_pow2_7_dvd_of_weight_le_2 {B : Nat} (h5 : ¬ (5 ∣ B)) (hw : hammingWeight B ≤ 2) :
    ¬ (2 ^ 7 ∣ B) := by
  intro h128
  have hB_pos : B > 0 := by
    by_cases h0 : B = 0
    · subst h0; exact absurd (Nat.dvd_zero 5) h5
    · omega
  by_cases hw1 : hammingWeight B ≤ 1
  · exact not_pow2_4_dvd_of_weight_le_1 h5 hw1 (Nat.dvd_trans (Nat.pow_dvd_pow 2 (by decide)) h128)
  · have hw2 : hammingWeight B = 2 := by omega
    have hsplit1 := hammingWeight_split_pow10 1 B
    have hd0_ne0 : B % 10 ≠ 0 := by
      intro h0; exact h5 (Nat.dvd_trans (by decide : 5 ∣ 10) (Nat.dvd_of_mod_eq_zero h0))
    have hd0_ne5 : B % 10 ≠ 5 := by
      intro h5m; exact h5 (Nat.dvd_of_mod_eq_zero (by omega))
    have hw_d0 : hammingWeight (B % 10 ^ 1) = 1 := by
      simp only [Nat.pow_one]
      rw [hammingWeight_eq (B % 10), if_neg hd0_ne0, if_pos (by omega)]
      have : (B % 10) / 10 = 0 := by omega
      rw [this, hammingWeight_zero]
    have hw_div1 : hammingWeight (B / 10) = 1 := by simp only [Nat.pow_one] at hsplit1 hw_d0; omega
    obtain ⟨d1, e', hd1_1, hd1_9, hq⟩ := eq_digit_mul_pow10_of_weight_1 (B / 10) hw_div1
    let e := e' + 1
    have hB_form : B = B % 10 + d1 * 10 ^ e := by
      have hdm : B = B % 10 + 10 * (B / 10) := by omega
      conv => lhs; rw [hdm, hq, ten_mul_digit_pow10]
    -- `e ≤ 3`, otherwise `2^4 ∣ 10^e` and `2^4 ∣ B` forces `16 ∣ B % 10`, impossible!
    have he_le3 : e ≤ 3 := by
      by_cases h4 : e ≥ 4
      · exfalso
        have h16_B : 2 ^ 4 ∣ B := Nat.dvd_trans (Nat.pow_dvd_pow 2 (by decide)) h128
        have h16_term : 2 ^ 4 ∣ d1 * 10 ^ e :=
          Nat.dvd_trans (Nat.pow_dvd_pow 2 h4) (Nat.dvd_trans (by rw [pow10_split e]; exact Nat.dvd_mul_right _ _) (Nat.dvd_mul_left _ d1))
        rw [hB_form, Nat.add_comm] at h16_B
        have h16_d0 : 2 ^ 4 ∣ B % 10 := dvd_of_dvd_add_left h16_term h16_B
        have hle := Nat.le_of_dvd (by omega) h16_d0
        have : 2 ^ 4 = 16 := by decide
        omega
      · omega
    have he_mem : e ∈ ([1, 2, 3] : List Nat) := by
      have : e = 1 ∨ e = 2 ∨ e = 3 := by omega
      rcases this with h | h | h <;> rw [h] <;> decide
    have hchk := checkM2_ok; unfold checkM2 at hchk
    have h1 := List.all_eq_true.mp hchk (B % 10) (mem_nonfive_digits (by omega) (by omega) hd0_ne5)
    have h2 := List.all_eq_true.mp h1 e he_mem
    have h3 := List.all_eq_true.mp h2 d1 (mem_nonzero_digits hd1_1 hd1_9)
    have hne : (B % 10 + d1 * 10 ^ e) % 128 ≠ 0 := of_decide_eq_true h3
    rw [← hB_form] at hne
    exact hne (Nat.mod_eq_zero_of_dvd h128)

/-! ### Part 2: Exact 3-Digit Ceiling `M(3) = 13` (`¬ 2^14 ∣ B` for `w(B) ≤ 3, 5 ∤ B`) -/

/-- Filtered kernel check for `M(3) = 13`:
    Any 3-digit `B = d0 + d1 * 10^i + d2 * 10^j` (`1 ≤ i < j ≤ 6`, `5 ∤ d0`) with `2^14 ∣ B`
    MUST satisfy `2^j ∣ d0 + d1 * 10^i` (since `2^j ∣ 10^j` and `j ≤ 6 < 14`).
    We check ALL such `(d0, i, d1, j, d2)` in < 0.05s by filtering on `2^j ∣ d0 + d1 * 10^i`! -/
def checkM3 : Bool :=
  ([1, 2, 3, 4, 6, 7, 8, 9] : List Nat).all fun d0 =>
    ([1, 2, 3, 4, 5] : List Nat).all fun i =>
      ([1, 2, 3, 4, 5, 6, 7, 8, 9] : List Nat).all fun d1 =>
        let b2 := d0 + d1 * 10 ^ i
        ([2, 3, 4, 5, 6] : List Nat).all fun j =>
          if j ≤ i || b2 % (2 ^ j) ≠ 0 then true
          else
            ([1, 2, 3, 4, 5, 6, 7, 8, 9] : List Nat).all fun d2 =>
              decide ((b2 + d2 * 10 ^ j) % 16384 ≠ 0)

theorem checkM3_ok : checkM3 = true := by decide

/-- Helper: every `n` with `w(n) = 2` and `n % 10 ≠ 0` has form `d0 + d1 * 10^i` (`i ≥ 1`). -/
theorem eq_two_digits_of_weight_2 {n : Nat} (hw : hammingWeight n = 2) (hmod : n % 10 ≠ 0) :
    ∃ d1 i : Nat, 1 ≤ d1 ∧ d1 ≤ 9 ∧ 1 ≤ i ∧ n = n % 10 + d1 * 10 ^ i := by
  have hsplit1 := hammingWeight_split_pow10 1 n
  have hw_d0 : hammingWeight (n % 10 ^ 1) = 1 := by
    simp only [Nat.pow_one]
    rw [hammingWeight_eq (n % 10), if_neg hmod, if_pos (by omega)]
    have : (n % 10) / 10 = 0 := by omega
    rw [this, hammingWeight_zero]
  have hw_div1 : hammingWeight (n / 10) = 1 := by simp only [Nat.pow_one] at hsplit1 hw_d0; omega
  obtain ⟨d1, e', hd1_1, hd1_9, hq⟩ := eq_digit_mul_pow10_of_weight_1 (n / 10) hw_div1
  refine ⟨d1, e' + 1, hd1_1, hd1_9, by omega, ?_⟩
  have hdm : n = n % 10 + 10 * (n / 10) := by omega
  conv => lhs; rw [hdm, hq, ten_mul_digit_pow10]

/-- Helper: every `n` with `w(n) = 3` and `n % 10 ≠ 0` splits at its highest non-zero digit
    as `n = B2 + d2 * 10^j` with `w(B2) = 2`, `B2 % 10 = n % 10`, and `B2 < 10^j`! -/
theorem split_top_digit_of_weight_3 :
    ∀ n : Nat, hammingWeight n = 3 → n % 10 ≠ 0 →
      ∃ d1 i d2 j : Nat, 1 ≤ d1 ∧ d1 ≤ 9 ∧ 1 ≤ d2 ∧ d2 ≤ 9 ∧ 1 ≤ i ∧ i < j ∧
        n = n % 10 + d1 * 10 ^ i + d2 * 10 ^ j := by
  intro n hw hmod
  -- Peel `n / 10` (which has `w(n / 10) = 2`), peel its lowest non-zero digit!
  have hsplit1 := hammingWeight_split_pow10 1 n
  have hw_d0 : hammingWeight (n % 10 ^ 1) = 1 := by
    simp only [Nat.pow_one]
    rw [hammingWeight_eq (n % 10), if_neg hmod, if_pos (by omega)]
    have : (n % 10) / 10 = 0 := by omega
    rw [this, hammingWeight_zero]
  have hw_q : hammingWeight (n / 10) = 2 := by simp only [Nat.pow_one] at hsplit1 hw_d0; omega
  -- Helper: any `m` with `w(m) = 2` has form `d1 * 10^a + d2 * 10^b` with `a < b`!
  have h2form : ∀ m : Nat, hammingWeight m = 2 →
      ∃ d1 a d2 b : Nat, 1 ≤ d1 ∧ d1 ≤ 9 ∧ 1 ≤ d2 ∧ d2 ≤ 9 ∧ a < b ∧
        m = d1 * 10 ^ a + d2 * 10 ^ b := by
    refine nat_strong_ind (P := fun m => hammingWeight m = 2 →
        ∃ d1 a d2 b : Nat, 1 ≤ d1 ∧ d1 ≤ 9 ∧ 1 ≤ d2 ∧ d2 ≤ 9 ∧ a < b ∧
          m = d1 * 10 ^ a + d2 * 10 ^ b) ?_
    intro m ihm hwm
    by_cases hm0 : m = 0
    · subst hm0; rw [hammingWeight_zero] at hwm; omega
    · by_cases hmd : m % 10 ≠ 0
      · obtain ⟨d2, b, hd2_1, hd2_9, hb1, hm_eq⟩ := eq_two_digits_of_weight_2 hwm hmd
        exact ⟨m % 10, 0, d2, b, by omega, by omega, hd2_1, hd2_9, by omega, by simpa using hm_eq⟩
      · rw [hammingWeight_eq m, if_neg hm0, if_neg hmd, Nat.zero_add] at hwm
        obtain ⟨d1, a, d2, b, h1, h2, h3, h4, hab, hq⟩ := ihm (m / 10) (by omega) hwm
        refine ⟨d1, a + 1, d2, b + 1, h1, h2, h3, h4, by omega, ?_⟩
        have hm_eq : m = 10 * (m / 10) := by omega
        rw [hm_eq, hq, Nat.mul_add, ten_mul_digit_pow10, ten_mul_digit_pow10]
  obtain ⟨d1, a, d2, b, h1, h2, h3, h4, hab, hq⟩ := h2form (n / 10) hw_q
  refine ⟨d1, a + 1, d2, b + 1, h1, h2, h3, h4, by omega, by omega, ?_⟩
  have hdm : n = n % 10 + 10 * (n / 10) := by omega
  conv => lhs; rw [hdm, hq, Nat.mul_add, ten_mul_digit_pow10, ten_mul_digit_pow10, ← Nat.add_assoc]

/-- **HEADLINE 2 — Exact 3-Digit Ceiling `M(3) = 13`**:
    NO integer `B` with `5 ∤ B` and `hammingWeight B ≤ 3` is divisible by `2^14 = 16384`!
    (Tight at `9003008 = 2^13 * 1099`!) -/
theorem not_pow2_14_dvd_of_weight_le_3 {B : Nat} (h5 : ¬ (5 ∣ B)) (hw : hammingWeight B ≤ 3) :
    ¬ (2 ^ 14 ∣ B) := by
  intro h16384
  by_cases hw2 : hammingWeight B ≤ 2
  · exact not_pow2_7_dvd_of_weight_le_2 h5 hw2 (Nat.dvd_trans (Nat.pow_dvd_pow 2 (by decide)) h16384)
  · have hw3 : hammingWeight B = 3 := by omega
    have hd0_ne0 : B % 10 ≠ 0 := by
      intro h0; exact h5 (Nat.dvd_trans (by decide : 5 ∣ 10) (Nat.dvd_of_mod_eq_zero h0))
    have hd0_ne5 : B % 10 ≠ 5 := by
      intro h5m; exact h5 (Nat.dvd_of_mod_eq_zero (by omega))
    obtain ⟨d1, i, d2, j, hd1_1, hd1_9, hd2_1, hd2_9, hi1, hij, hB_form⟩ :=
      split_top_digit_of_weight_3 B hw3 hd0_ne0
    let b2 := B % 10 + d1 * 10 ^ i
    have hb2_5 : ¬ (5 ∣ b2) := by
      intro h5b
      have h10i : 5 ∣ 10 ^ i := by
        cases i with | zero => omega | succ i' => rw [Nat.pow_succ]; exact Nat.dvd_trans (by decide : 5 ∣ 10) (Nat.dvd_mul_left 10 _)
      have h5d1 : 5 ∣ d1 * 10 ^ i := Nat.dvd_trans h10i (Nat.dvd_mul_left _ d1)
      have h5d0 : 5 ∣ B % 10 := by
        dsimp only [b2] at h5b; rw [Nat.add_comm] at h5b; exact dvd_of_dvd_add_left h5d1 h5b
      have := Nat.mod_eq_zero_of_dvd h5d0; omega
    have hb2_w : hammingWeight b2 ≤ 2 := by
      have hsp := hammingWeight_split_pow10 i b2
      have hmod_i : b2 % 10 ^ i = B % 10 := by
        dsimp only [b2]
        rw [Nat.add_comm, Nat.mul_comm d1 (10 ^ i), Nat.mul_add_mod]
        have hlt : B % 10 < 10 ^ i := by
          have : 10 ^ 1 ≤ 10 ^ i := Nat.pow_le_pow_right (by decide) hi1
          omega
        exact Nat.mod_eq_of_lt hlt
      have hdiv_i : b2 / 10 ^ i = d1 := by
        dsimp only [b2]
        rw [Nat.add_comm, Nat.mul_comm d1 (10 ^ i), Nat.mul_add_div (pow_pos (by decide : 10 ≥ 1) i)]
        have hlt : B % 10 < 10 ^ i := by
          have : 10 ^ 1 ≤ 10 ^ i := Nat.pow_le_pow_right (by decide) hi1
          omega
        rw [Nat.div_eq_of_lt hlt]; omega
      rw [hmod_i, hdiv_i] at hsp
      have hw_d1 : hammingWeight d1 = 1 := by
        rw [hammingWeight_eq d1, if_neg (by omega), if_pos (by omega)]
        have : d1 / 10 = 0 := by omega
        rw [this, hammingWeight_zero]
      have hw_d0 : hammingWeight (B % 10) = 1 := by
        rw [hammingWeight_eq (B % 10), if_neg hd0_ne0, if_pos (by omega)]
        have : (B % 10) / 10 = 0 := by omega
        rw [this, hammingWeight_zero]
      omega
    -- By `M(2) = 6`, `j ≤ 6` (otherwise `2^7 ∣ 10^j` and `2^7 ∣ B` forces `2^7 ∣ b2`, contradicting `M(2) = 6`!)
    have hj_le6 : j ≤ 6 := by
      by_cases h7 : j ≥ 7
      · exfalso
        have h128_B : 2 ^ 7 ∣ B := Nat.dvd_trans (Nat.pow_dvd_pow 2 (by decide)) h16384
        have h128_term : 2 ^ 7 ∣ d2 * 10 ^ j :=
          Nat.dvd_trans (Nat.pow_dvd_pow 2 h7) (Nat.dvd_trans (by rw [pow10_split j]; exact Nat.dvd_mul_right _ _) (Nat.dvd_mul_left _ d2))
        have h128_b2 : 2 ^ 7 ∣ b2 := by
          change 2 ^ 7 ∣ B % 10 + d1 * 10 ^ i
          rw [hB_form, Nat.add_comm] at h128_B
          exact dvd_of_dvd_add_left h128_term h128_B
        exact not_pow2_7_dvd_of_weight_le_2 hb2_5 hb2_w h128_b2
      · omega
    -- Also `2^j ∣ b2` (since `j ≤ 6 < 14`, `2^j ∣ 10^j` and `2^j ∣ B`)!
    have h2j_b2 : 2 ^ j ∣ b2 := by
      have h2j_B : 2 ^ j ∣ B := Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) h16384
      have h2j_term : 2 ^ j ∣ d2 * 10 ^ j :=
        Nat.dvd_trans (by rw [pow10_split j]; exact Nat.dvd_mul_right _ _) (Nat.dvd_mul_left _ d2)
      rw [hB_form, Nat.add_comm] at h2j_B
      exact dvd_of_dvd_add_left h2j_term h2j_B
    have hi_mem : i ∈ ([1, 2, 3, 4, 5] : List Nat) := by
      have : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl <;> decide
    have hj_mem : j ∈ ([2, 3, 4, 5, 6] : List Nat) := by
      have : j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl <;> decide
    have hchk := checkM3_ok; unfold checkM3 at hchk
    have h1 := List.all_eq_true.mp hchk (B % 10) (mem_nonfive_digits (by omega) (by omega) hd0_ne5)
    have h2 := List.all_eq_true.mp h1 i hi_mem
    have h3 := List.all_eq_true.mp h2 d1 (mem_nonzero_digits hd1_1 hd1_9)
    have h4 := List.all_eq_true.mp h3 j hj_mem
    have hcond_false : (decide (j ≤ i) || decide (b2 % 2 ^ j ≠ 0)) = false := by
      have hji : ¬ (j ≤ i) := by omega
      have hmod0 : b2 % 2 ^ j = 0 := Nat.mod_eq_zero_of_dvd h2j_b2
      simp [hji, hmod0]
    change (if (decide (j ≤ i) || decide (b2 % 2 ^ j ≠ 0)) = true then true
            else ([1, 2, 3, 4, 5, 6, 7, 8, 9] : List Nat).all fun d2 =>
              decide ((b2 + d2 * 10 ^ j) % 16384 ≠ 0)) = true at h4
    rw [hcond_false] at h4
    simp only [Bool.false_eq_true, ite_false] at h4
    have h5d := List.all_eq_true.mp h4 d2 (mem_nonzero_digits hd2_1 hd2_9)
    have hne : (b2 + d2 * 10 ^ j) % 16384 ≠ 0 := of_decide_eq_true h5d
    rw [← hB_form] at hne
    exact hne (Nat.mod_eq_zero_of_dvd h16384)

/-! ### Part 3: Unconditional Theorem `∀ m ≥ 14, hammingWeight (2^m) ≥ 5` -/

theorem pow2_weight_le_4_implies_m_le_46 {m : Nat} (hw : hammingWeight (2 ^ m) ≤ 4) : m ≤ 46 := by
  by_cases hm14 : m < 14
  · omega
  · have hsplit := hammingWeight_split_pow10 14 (2 ^ m)
    have h2_14_dvd : 2 ^ 14 ∣ (2 ^ m) % 10 ^ 14 :=
      mod_pow10_dvd_of_dvd (Nat.pow_dvd_pow 2 (by omega))
    have h5_not : ¬ (5 ∣ (2 ^ m) % 10 ^ 14) :=
      not_five_dvd_mod_pow10 (by decide) (not_five_dvd_pow2 m)
    -- By `M(3) = 13`, `(2^m) % 10^14` CANNOT have weight `≤ 3`, so `w((2^m) % 10^14) ≥ 4`!
    have hw_rem_ge4 : hammingWeight ((2 ^ m) % 10 ^ 14) ≥ 4 := by
      by_cases h4 : hammingWeight ((2 ^ m) % 10 ^ 14) ≥ 4
      · exact h4
      · exfalso; exact not_pow2_14_dvd_of_weight_le_3 h5_not (by omega) h2_14_dvd
    have hw_div0 : hammingWeight ((2 ^ m) / 10 ^ 14) = 0 := by omega
    have hdiv0 : (2 ^ m) / 10 ^ 14 = 0 := by
      by_cases hd : (2 ^ m) / 10 ^ 14 = 0
      · exact hd
      · exfalso; have := hammingWeight_pos_of_pos (Nat.pos_of_ne_zero hd); omega
    have hlt : 2 ^ m < 10 ^ 14 := by
      have hdm := Nat.div_add_mod (2 ^ m) (10 ^ 14)
      have hml := Nat.mod_lt (2 ^ m) (by decide : 10 ^ 14 > 0)
      rw [hdiv0, Nat.mul_zero, Nat.zero_add] at hdm; omega
    by_cases hm46 : m ≤ 46
    · exact hm46
    · exfalso
      have h47 : 2 ^ 47 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) (by omega)
      have hcmp : 10 ^ 14 < 2 ^ 47 := by decide
      omega

def checkPow2Ge5 : Bool :=
  (List.range 33).all fun i => decide (hwFuel 15 (2 ^ (14 + i)) ≥ 5)

theorem checkPow2Ge5_ok : checkPow2Ge5 = true := by decide

/-- **HEADLINE 3 — Complete Unconditional Classification (`∀ m ≥ 14, w(2^m) ≥ 5`)**:
    NO power of 2 beyond `2^13 = 8192` EVER has `≤ 4` non-zero decimal digits! -/
theorem pow2_weight_ge_5_of_ge_14 {m : Nat} (hm : m ≥ 14) : hammingWeight (2 ^ m) ≥ 5 := by
  by_cases hle : m ≤ 46
  · have hchk := checkPow2Ge5_ok; unfold checkPow2Ge5 at hchk
    have h1 := List.all_eq_true.mp hchk (m - 14) (List.mem_range.mpr (by omega))
    have hfuel : hwFuel 15 (2 ^ (14 + (m - 14))) ≥ 5 := of_decide_eq_true h1
    have heq : 14 + (m - 14) = m := by omega
    rw [heq] at hfuel
    exact Nat.le_trans hfuel (hwFuel_le_hammingWeight 15 (2 ^ m))
  · by_cases hw : hammingWeight (2 ^ m) ≥ 5
    · exact hw
    · exfalso; have := pow2_weight_le_4_implies_m_le_46 (by omega : hammingWeight (2 ^ m) ≤ 4); omega

#print axioms not_pow2_7_dvd_of_weight_le_2
#print axioms not_pow2_14_dvd_of_weight_le_3
#print axioms pow2_weight_ge_5_of_ge_14

end Ch4Sparse2AdicCeiling
