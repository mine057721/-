/-!
# Chapter 1: Generalized Bidirectional, Reverse & Per-Digit Doubling-Window Transducer Spectrum (Lean 4)

Self-contained pure Lean 4.16.0 core (zero Mathlib, zero `sorry`, zero `native_decide`,
only standard axioms `[propext, Quot.sound]`).

## Main Results
1. **Generalized Linear-Objective Transducer Certificate (`gen_cert_sound`)**:
   Unifies forward (`s(n)`), reverse (`s(2^(K-1) n)`), bidirectional (`s(n) + s(2^(K-1) n)`),
   and Hamming-weight (`w(n)`) lower bounds in ONE `2^(K-1)`-state potential-certificate framework
   with automatic carry-flush telescoping and ZERO additive error!
2. **Universal No-Deep-Valley Theorem (`no_deep_valley_K7`, tight at `n = 75`)**:
   `∀ n : Nat, s(2n) + s(4n) + s(8n) + s(16n) + s(32n) ≥ s(n) + s(64n)`.
   The 5 interior steps of ANY 7-step doubling orbit can NEVER dip below the sum of its two endpoints!
3. **Reverse Phase-Transition Spectrum (`rev_K5`, `rev_K6`, `rev_K7`)**:
   - `K = 5`: `2 * windowSum 5 n ≥ 5 * s(16n)` (tight at `n = 3`)
   - `K = 6`: `windowSum 6 n ≥ 3 * s(32n)` (tight at `n = 3`)
   - `K = 7`: `23 * windowSum 7 n ≥ 77 * s(64n)` (tight at `n = 14`)
4. **Per-Nonzero-Digit Spectrum (`wt_K2`, `wt_K4`, `wt_K6`, `wt_K7`)**:
   - `K = 2`: `s(n) + s(2n) ≥ 3 * w(n)` (tight at `n = 1`)
   - `K = 4`: `windowSum 4 n ≥ 7 * w(n)` (tight at `n = 125`)
   - `K = 6`: `windowSum 6 n ≥ 9 * w(n)` (tight at `n = 125`)
   - `K = 7`: `3 * windowSum 7 n ≥ 35 * w(n)` (tight at `n = 125`)
-/

namespace Ch1BidirectionalTransducer

def digitSum (n : Nat) : Nat :=
  if h : n < 10 then n
  else n % 10 + digitSum (n / 10)
termination_by n
decreasing_by omega

def hammingWeight (n : Nat) : Nat :=
  if h : n = 0 then 0
  else (if n % 10 ≠ 0 then 1 else 0) + hammingWeight (n / 10)
termination_by n
decreasing_by omega

def sumRange (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => sumRange f k + f k

def windowSum (K n : Nat) : Nat :=
  sumRange (fun j => digitSum (2 ^ j * n)) K

def shiftedWindowSum (K c n : Nat) : Nat :=
  sumRange (fun j => digitSum (2 ^ j * n + c / 2 ^ (K - 1 - j))) K

def stepWeight (K c d : Nat) : Nat :=
  sumRange (fun j => (2 ^ j * d + c / 2 ^ (K - 1 - j)) % 10) K

def nextCarry (K c d : Nat) : Nat :=
  (c + d * 2 ^ (K - 1)) / 10

def targetStep (K α β γ c d : Nat) : Nat :=
  α * d + β * ((2 ^ (K - 1) * d + c) % 10) + γ * (if d = 0 then 0 else 1)

def targetShifted (K α β γ c n : Nat) : Nat :=
  α * digitSum n + β * digitSum (2 ^ (K - 1) * n + c) + γ * hammingWeight n

theorem nat_strong_ind {P : Nat → Prop} (h : ∀ n, (∀ k < n, P k) → P n) : ∀ n, P n :=
  fun n => Nat.strongRecOn n h

theorem digitSum_zero : digitSum 0 = 0 := by unfold digitSum; simp
theorem digitSum_lt_ten {n : Nat} (h : n < 10) : digitSum n = n := by unfold digitSum; simp [h]

theorem digitSum_eq (n : Nat) : digitSum n = n % 10 + digitSum (n / 10) := by
  by_cases h : n < 10
  · rw [digitSum_lt_ten h, Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h, digitSum_zero]; omega
  · conv => lhs; unfold digitSum; simp [h]

theorem hammingWeight_zero : hammingWeight 0 = 0 := by unfold hammingWeight; simp

theorem hammingWeight_eq (n : Nat) :
    hammingWeight n = if n = 0 then 0 else (if n % 10 ≠ 0 then 1 else 0) + hammingWeight (n / 10) := by
  by_cases h : n = 0
  · subst h; unfold hammingWeight; simp
  · rw [if_neg h]; conv => lhs; unfold hammingWeight; simp only [h, dite_false]

theorem pow2_pos (k : Nat) : 2 ^ k ≥ 1 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.pow_succ]; omega

theorem sumRange_pointwise_add (f g : Nat → Nat) (N : Nat) :
    sumRange (fun i => f i + g i) N = sumRange f N + sumRange g N := by
  induction N with
  | zero => simp [sumRange]
  | succ N ih => simp only [sumRange]; omega

theorem sumRange_congr {f g : Nat → Nat} {N : Nat} (h : ∀ i, i < N → f i = g i) :
    sumRange f N = sumRange g N := by
  induction N with
  | zero => simp [sumRange]
  | succ N ih =>
    simp only [sumRange]
    rw [ih (fun i hi => h i (by omega)), h N (by omega)]

theorem sumRange_zero_fn (N : Nat) : sumRange (fun _ => 0) N = 0 := by
  induction N with
  | zero => simp [sumRange]
  | succ N ih => simp only [sumRange, ih]

theorem nextCarry_div_pow2 {K j c d : Nat} (hj : j < K) :
    nextCarry K c d / 2 ^ (K - 1 - j) = (2 ^ j * d + c / 2 ^ (K - 1 - j)) / 10 := by
  unfold nextCarry
  have hsplit : 2 ^ (K - 1) = 2 ^ j * 2 ^ (K - 1 - j) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hrpos : 2 ^ (K - 1 - j) > 0 := pow2_pos (K - 1 - j)
  calc ((c + d * 2 ^ (K - 1)) / 10) / 2 ^ (K - 1 - j)
      = (c + d * 2 ^ (K - 1)) / (10 * 2 ^ (K - 1 - j)) := Nat.div_div_eq_div_mul _ _ _
    _ = (c + d * 2 ^ (K - 1)) / (2 ^ (K - 1 - j) * 10) := by rw [Nat.mul_comm 10 (2 ^ (K - 1 - j))]
    _ = ((c + d * 2 ^ (K - 1)) / 2 ^ (K - 1 - j)) / 10 := (Nat.div_div_eq_div_mul _ _ _).symm
    _ = (c / 2 ^ (K - 1 - j) + d * 2 ^ j) / 10 := by
        rw [hsplit, ← Nat.mul_assoc, Nat.add_mul_div_right c (d * 2 ^ j) hrpos]
    _ = (2 ^ j * d + c / 2 ^ (K - 1 - j)) / 10 := by
        rw [Nat.add_comm, Nat.mul_comm d (2 ^ j)]

theorem shiftedWindowSum_step (K c n : Nat) :
    shiftedWindowSum K c n =
      stepWeight K c (n % 10) + shiftedWindowSum K (nextCarry K c (n % 10)) (n / 10) := by
  unfold shiftedWindowSum stepWeight
  rw [← sumRange_pointwise_add]
  refine sumRange_congr (fun j hj => ?_)
  rw [digitSum_eq (2 ^ j * n + c / 2 ^ (K - 1 - j))]
  have hn : n = 10 * (n / 10) + n % 10 := (Nat.div_add_mod n 10).symm
  have hdecomp : 2 ^ j * n + c / 2 ^ (K - 1 - j) =
      10 * (2 ^ j * (n / 10)) + (2 ^ j * (n % 10) + c / 2 ^ (K - 1 - j)) := by
    conv => lhs; rw [hn, Nat.mul_add, Nat.mul_left_comm (2 ^ j) 10 (n / 10)]
    omega
  have hmod : (2 ^ j * n + c / 2 ^ (K - 1 - j)) % 10 =
      (2 ^ j * (n % 10) + c / 2 ^ (K - 1 - j)) % 10 := by
    rw [hdecomp, Nat.mul_add_mod]
  have hdiv : (2 ^ j * n + c / 2 ^ (K - 1 - j)) / 10 =
      2 ^ j * (n / 10) + nextCarry K c (n % 10) / 2 ^ (K - 1 - j) := by
    rw [hdecomp, Nat.mul_add_div (by decide : 10 > 0), nextCarry_div_pow2 hj]
  rw [hmod, hdiv]

/-- Exact 1-digit recurrence for `targetShifted` (works for BOTH `n > 0` and flush `n = 0`!). -/
theorem targetShifted_step (K α β γ c n : Nat) :
    targetShifted K α β γ c n =
      targetStep K α β γ c (n % 10) + targetShifted K α β γ (nextCarry K c (n % 10)) (n / 10) := by
  unfold targetShifted targetStep
  have hds := digitSum_eq n
  have hhw : hammingWeight n = (if n % 10 = 0 then 0 else 1) + hammingWeight (n / 10) := by
    by_cases h0 : n = 0
    · subst h0; simp [hammingWeight_zero]
    · rw [hammingWeight_eq n, if_neg h0]
      by_cases hm : n % 10 = 0
      · rw [if_pos hm, if_neg (by omega)]
      · rw [if_neg hm, if_pos hm]
  have hend : digitSum (2 ^ (K - 1) * n + c) =
      (2 ^ (K - 1) * (n % 10) + c) % 10 + digitSum (2 ^ (K - 1) * (n / 10) + nextCarry K c (n % 10)) := by
    rw [digitSum_eq (2 ^ (K - 1) * n + c)]
    have hn : n = 10 * (n / 10) + n % 10 := (Nat.div_add_mod n 10).symm
    have hdecomp : 2 ^ (K - 1) * n + c =
        10 * (2 ^ (K - 1) * (n / 10)) + (2 ^ (K - 1) * (n % 10) + c) := by
      conv => lhs; rw [hn, Nat.mul_add, Nat.mul_left_comm (2 ^ (K - 1)) 10 (n / 10)]
      omega
    have hmod : (2 ^ (K - 1) * n + c) % 10 = (2 ^ (K - 1) * (n % 10) + c) % 10 := by
      rw [hdecomp, Nat.mul_add_mod]
    have hdiv : (2 ^ (K - 1) * n + c) / 10 = 2 ^ (K - 1) * (n / 10) + nextCarry K c (n % 10) := by
      rw [hdecomp, Nat.mul_add_div (by decide : 10 > 0)]
      unfold nextCarry; rw [Nat.mul_comm (2 ^ (K - 1)) (n % 10), Nat.add_comm (n % 10 * 2 ^ (K - 1)) c]
    rw [hmod, hdiv]
  rw [hds, hhw, hend, Nat.mul_add, Nat.mul_add, Nat.mul_add]
  omega

theorem shiftedWindowSum_zero_carry (K n : Nat) :
    shiftedWindowSum K 0 n = windowSum K n := by
  unfold shiftedWindowSum windowSum
  exact sumRange_congr (fun j _ => by simp)

theorem shiftedWindowSum_zero_zero (K : Nat) :
    shiftedWindowSum K 0 0 = 0 := by
  rw [shiftedWindowSum_zero_carry]
  unfold windowSum
  rw [sumRange_congr (g := fun _ => 0) (fun j _ => by simp [digitSum_zero])]
  exact sumRange_zero_fn K

theorem nextCarry_lt {K c d : Nat} (hc : c < 2 ^ (K - 1)) (hd : d < 10) :
    nextCarry K c d < 2 ^ (K - 1) := by
  unfold nextCarry
  have hle : d * 2 ^ (K - 1) ≤ 9 * 2 ^ (K - 1) := Nat.mul_le_mul_right _ (by omega)
  omega

theorem flush_gen_bound {K p q α β γ : Nat} {φ : Nat → Nat}
    (hcert : ∀ c, c < 2 ^ (K - 1) → ∀ d, d < 10 →
      q * stepWeight K c d + φ (nextCarry K c d) ≥ p * targetStep K α β γ c d + φ c) :
    ∀ c : Nat, c < 2 ^ (K - 1) →
      q * shiftedWindowSum K c 0 + φ 0 ≥ p * targetShifted K α β γ c 0 + φ c := by
  refine nat_strong_ind (P := fun c => c < 2 ^ (K - 1) →
      q * shiftedWindowSum K c 0 + φ 0 ≥ p * targetShifted K α β γ c 0 + φ c) ?_
  intro c ih hc
  by_cases hc0 : c = 0
  · subst hc0
    rw [shiftedWindowSum_zero_zero]
    unfold targetShifted; simp [digitSum_zero, hammingWeight_zero]
  · have hstep := shiftedWindowSum_step K c 0
    have htstep := targetShifted_step K α β γ c 0
    simp only [Nat.zero_mod, Nat.zero_div] at hstep htstep
    have hnc : nextCarry K c 0 = c / 10 := by unfold nextCarry; simp
    rw [hnc] at hstep htstep
    have hih := ih (c / 10) (by omega) (by omega)
    have hedge := hcert c hc 0 (by decide)
    rw [hnc] at hedge
    rw [hstep, htstep, Nat.mul_add, Nat.mul_add]
    omega

theorem shifted_gen_bound {K p q α β γ : Nat} {φ : Nat → Nat}
    (hcert : ∀ c, c < 2 ^ (K - 1) → ∀ d, d < 10 →
      q * stepWeight K c d + φ (nextCarry K c d) ≥ p * targetStep K α β γ c d + φ c) :
    ∀ n c : Nat, c < 2 ^ (K - 1) →
      q * shiftedWindowSum K c n + φ 0 ≥ p * targetShifted K α β γ c n + φ c := by
  refine nat_strong_ind (P := fun n => ∀ c, c < 2 ^ (K - 1) →
      q * shiftedWindowSum K c n + φ 0 ≥ p * targetShifted K α β γ c n + φ c) ?_
  intro n ih c hc
  by_cases hn0 : n = 0
  · subst hn0; exact flush_gen_bound hcert c hc
  · have hstep := shiftedWindowSum_step K c n
    have htstep := targetShifted_step K α β γ c n
    have hd : n % 10 < 10 := Nat.mod_lt n (by decide)
    have hnc_lt : nextCarry K c (n % 10) < 2 ^ (K - 1) := nextCarry_lt hc hd
    have hih := ih (n / 10) (by omega) (nextCarry K c (n % 10)) hnc_lt
    have hedge := hcert c hc (n % 10) hd
    rw [hstep, htstep, Nat.mul_add, Nat.mul_add]
    omega

/-- **Universal Generalized Transducer Certificate Theorem** (ZERO additive error!). -/
theorem gen_potential_cert_sound {K p q α β γ : Nat} {φ : Nat → Nat}
    (hcert : ∀ c, c < 2 ^ (K - 1) → ∀ d, d < 10 →
      q * stepWeight K c d + φ (nextCarry K c d) ≥ p * targetStep K α β γ c d + φ c) :
    ∀ n : Nat,
      q * windowSum K n ≥ p * (α * digitSum n + β * digitSum (2 ^ (K - 1) * n) + γ * hammingWeight n) := by
  intro n
  have hmain := shifted_gen_bound hcert n 0 (pow2_pos (K - 1))
  rw [shiftedWindowSum_zero_carry] at hmain
  unfold targetShifted at hmain
  simp only [Nat.add_zero] at hmain
  omega

inductive BTree
  | leaf (v : Nat)
  | node (l r : BTree)

def BTree.get : Nat → BTree → Nat → Nat
  | 0, BTree.leaf v, _ => v
  | d + 1, BTree.node l r, idx =>
    if idx < 2 ^ d then BTree.get d l idx
    else BTree.get d r (idx - 2 ^ d)
  | _, _, _ => 0

def checkGenCert (K p q α β γ : Nat) (t : BTree) : Bool :=
  (List.range (2 ^ (K - 1))).all fun c =>
    (List.range 10).all fun d =>
      decide (q * stepWeight K c d + BTree.get (K - 1) t (nextCarry K c d) ≥
              p * targetStep K α β γ c d + BTree.get (K - 1) t c)

theorem checkGenCert_sound {K p q α β γ : Nat} {t : BTree}
    (h : checkGenCert K p q α β γ t = true) :
    ∀ n : Nat,
      q * windowSum K n ≥ p * (α * digitSum n + β * digitSum (2 ^ (K - 1) * n) + γ * hammingWeight n) := by
  refine gen_potential_cert_sound (φ := BTree.get (K - 1) t) ?_
  intro c hc d hd
  unfold checkGenCert at h
  have h1 := List.all_eq_true.mp h c (List.mem_range.mpr hc)
  have h2 := List.all_eq_true.mp h1 d (List.mem_range.mpr hd)
  exact of_decide_eq_true h2

def potBidir7 : BTree :=
  BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 3) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0))) (BTree.node (BTree.node (BTree.leaf 2) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 0) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0))) (BTree.node (BTree.node (BTree.leaf 0) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 5) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0))) (BTree.node (BTree.node (BTree.leaf 0) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 1) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0))) (BTree.node (BTree.node (BTree.leaf 0) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0)))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 8) (BTree.leaf 1)) (BTree.node (BTree.leaf 0) (BTree.leaf 0))) (BTree.node (BTree.node (BTree.leaf 7) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 4) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0))) (BTree.node (BTree.node (BTree.leaf 0) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 10) (BTree.leaf 3)) (BTree.node (BTree.leaf 0) (BTree.leaf 0))) (BTree.node (BTree.node (BTree.leaf 0) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 6) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0))) (BTree.node (BTree.node (BTree.leaf 0) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0))))))

def potRev5 : BTree :=
  BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 13) (BTree.leaf 1)) (BTree.node (BTree.leaf 0) (BTree.leaf 0))) (BTree.node (BTree.node (BTree.leaf 7) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 3) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0))) (BTree.node (BTree.node (BTree.leaf 0) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0))))

def potRev6 : BTree :=
  BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 13) (BTree.leaf 5)) (BTree.node (BTree.leaf 3) (BTree.leaf 0))) (BTree.node (BTree.node (BTree.leaf 8) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 4) (BTree.leaf 2)) (BTree.node (BTree.leaf 0) (BTree.leaf 0))) (BTree.node (BTree.node (BTree.leaf 5) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 8) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0))) (BTree.node (BTree.node (BTree.leaf 3) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 0) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0))) (BTree.node (BTree.node (BTree.leaf 0) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0)))))

def potRev7 : BTree :=
  BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 412) (BTree.leaf 143)) (BTree.node (BTree.leaf 141) (BTree.leaf 0))) (BTree.node (BTree.node (BTree.leaf 118) (BTree.leaf 0)) (BTree.node (BTree.leaf 99) (BTree.leaf 0)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 141) (BTree.leaf 69)) (BTree.node (BTree.leaf 11) (BTree.leaf 0))) (BTree.node (BTree.node (BTree.leaf 246) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 164) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0))) (BTree.node (BTree.node (BTree.leaf 44) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 0) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0))) (BTree.node (BTree.node (BTree.leaf 0) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0)))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 297) (BTree.leaf 28)) (BTree.node (BTree.leaf 26) (BTree.leaf 0))) (BTree.node (BTree.node (BTree.leaf 3) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 26) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0))) (BTree.node (BTree.node (BTree.leaf 131) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 49) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0))) (BTree.node (BTree.node (BTree.leaf 0) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 0) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0))) (BTree.node (BTree.node (BTree.leaf 0) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0))))))

def potWt2 : BTree :=
  BTree.node (BTree.leaf 0) (BTree.leaf 0)

def potWt4 : BTree :=
  BTree.node (BTree.node (BTree.node (BTree.leaf 0) (BTree.leaf 1)) (BTree.node (BTree.leaf 2) (BTree.leaf 0))) (BTree.node (BTree.node (BTree.leaf 2) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0)))

def potWt6 : BTree :=
  BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 0) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0))) (BTree.node (BTree.node (BTree.leaf 7) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 6) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0))) (BTree.node (BTree.node (BTree.leaf 0) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 4) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0))) (BTree.node (BTree.node (BTree.leaf 2) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 1) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0))) (BTree.node (BTree.node (BTree.leaf 0) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0)))))

def potWt7 : BTree :=
  BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 0) (BTree.leaf 0)) (BTree.node (BTree.leaf 8) (BTree.leaf 0))) (BTree.node (BTree.node (BTree.leaf 6) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 45) (BTree.leaf 0)) (BTree.node (BTree.leaf 10) (BTree.leaf 0))) (BTree.node (BTree.node (BTree.leaf 0) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 34) (BTree.leaf 0)) (BTree.node (BTree.leaf 7) (BTree.leaf 0))) (BTree.node (BTree.node (BTree.leaf 32) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 9) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0))) (BTree.node (BTree.node (BTree.leaf 0) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0)))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 20) (BTree.leaf 6)) (BTree.node (BTree.leaf 28) (BTree.leaf 0))) (BTree.node (BTree.node (BTree.leaf 26) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 30) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0))) (BTree.node (BTree.node (BTree.leaf 0) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 19) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0))) (BTree.node (BTree.node (BTree.leaf 17) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 0) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0))) (BTree.node (BTree.node (BTree.leaf 0) (BTree.leaf 0)) (BTree.node (BTree.leaf 0) (BTree.leaf 0))))))

theorem certBidir7_ok : checkGenCert 7 2 1 1 1 0 potBidir7 = true := by decide
theorem certRev5_ok   : checkGenCert 5 5 2 0 1 0 potRev5 = true := by decide
theorem certRev6_ok   : checkGenCert 6 3 1 0 1 0 potRev6 = true := by decide
theorem certRev7_ok   : checkGenCert 7 77 23 0 1 0 potRev7 = true := by decide
theorem certWt2_ok    : checkGenCert 2 3 1 0 0 1 potWt2 = true := by decide
theorem certWt4_ok    : checkGenCert 4 7 1 0 0 1 potWt4 = true := by decide
theorem certWt6_ok    : checkGenCert 6 9 1 0 0 1 potWt6 = true := by decide
theorem certWt7_ok    : checkGenCert 7 35 3 0 0 1 potWt7 = true := by decide

/-- **HEADLINE 1 — Universal No-Deep-Valley Theorem (`K = 7`, tight at `n = 75`)**:
    For EVERY `n : Nat`, `s(2n) + s(4n) + s(8n) + s(16n) + s(32n) ≥ s(n) + s(64n)`! -/
theorem no_deep_valley_K7 (n : Nat) :
    digitSum (2 * n) + digitSum (4 * n) + digitSum (8 * n) +
    digitSum (16 * n) + digitSum (32 * n) ≥ digitSum n + digitSum (64 * n) := by
  have h := checkGenCert_sound certBidir7_ok n
  have hpow : 2 ^ 0 = 1 ∧ 2 ^ 1 = 2 ∧ 2 ^ 2 = 4 ∧ 2 ^ 3 = 8 ∧ 2 ^ 4 = 16 ∧ 2 ^ 5 = 32 ∧ 2 ^ 6 = 64 := by decide
  simp only [windowSum, sumRange, hpow.1, hpow.2.1, hpow.2.2.1, hpow.2.2.2.1, hpow.2.2.2.2.1, hpow.2.2.2.2.2.1, hpow.2.2.2.2.2.2,
             Nat.one_mul, Nat.zero_mul, Nat.add_zero, Nat.zero_add] at h
  omega

/-- **HEADLINE 2 — Reverse Phase-Transition Spectrum (`K = 5, 6, 7`)**: -/
theorem rev_K5 (n : Nat) : 2 * windowSum 5 n ≥ 5 * digitSum (16 * n) := by
  simpa using checkGenCert_sound certRev5_ok n

theorem rev_K6 (n : Nat) : windowSum 6 n ≥ 3 * digitSum (32 * n) := by
  simpa using checkGenCert_sound certRev6_ok n

theorem rev_K7 (n : Nat) : 23 * windowSum 7 n ≥ 77 * digitSum (64 * n) := by
  simpa using checkGenCert_sound certRev7_ok n

/-- **HEADLINE 3 — Per-Nonzero-Digit Growth Spectrum (`K = 2, 4, 6, 7`)**: -/
theorem wt_K2 (n : Nat) : digitSum n + digitSum (2 * n) ≥ 3 * hammingWeight n := by
  have h := checkGenCert_sound certWt2_ok n
  have hpow : 2 ^ 0 = 1 ∧ 2 ^ 1 = 2 := by decide
  simp only [windowSum, sumRange, hpow.1, hpow.2, Nat.one_mul, Nat.zero_mul, Nat.add_zero, Nat.zero_add] at h
  exact h

theorem wt_K4 (n : Nat) : windowSum 4 n ≥ 7 * hammingWeight n := by
  simpa using checkGenCert_sound certWt4_ok n

theorem wt_K6 (n : Nat) : windowSum 6 n ≥ 9 * hammingWeight n := by
  simpa using checkGenCert_sound certWt6_ok n

theorem wt_K7 (n : Nat) : 3 * windowSum 7 n ≥ 35 * hammingWeight n := by
  simpa using checkGenCert_sound certWt7_ok n

#print axioms gen_potential_cert_sound
#print axioms no_deep_valley_K7
#print axioms rev_K5
#print axioms rev_K6
#print axioms rev_K7
#print axioms wt_K2
#print axioms wt_K4
#print axioms wt_K6
#print axioms wt_K7

end Ch1BidirectionalTransducer
