/-!
# Chapter 3: The Length-Sparsity Phase Transition — Jumping Past Slope `1.0` via Exact Digit-Length Constraints (Lean 4)

Self-contained pure Lean 4.16.0 core (zero Mathlib, zero `sorry`, zero `native_decide`,
only standard axioms `[propext, Quot.sound]`).

## Driving Question from Chapter 2
Chapter 2 proved that WITHOUT a digit-length constraint (`N < 10^t`), NO local modular divisibility
(`M * 2^t ∣ N, 5 ∤ N`, even for `M = 27` or any odd `M` coprime to 10) can force `s(N) > 0.7 t`.
What happens the moment we impose the **exact digit-length constraint** of `2^t` itself
(`N < 10^(4k)` for `t = 13k`, matching `2^(13k) < 10^(4k)`)?

## Main Results
1. **Pure-`Nat` Capped-Digit Chernoff Moment Bound (`capped_chernoff_bound`)**:
   For ANY `D, M, p, q` with `1 ≤ p ≤ q` and `M ≤ 9 * D`:
     `countLow D M * p^M * q^(9*D - M) ≤ (mgf10 p q)^D`,
   where `mgf10 p q = ∑_{d=0}^9 p^d * q^(9 - d)`.
2. **Exact Phase-Transition Exponential Decay at `(D, t) = (4k, 13k)` (`length_sparsity_exp_decay`)**:
   At `(p, q) = (15, 17)`, `mgf10 15 17 = 719671754912` satisfies
     `(mgf10 15 17)^4 < 2^13 * 15^14 * 17^22` (ratio `≈ 0.95498 < 1`),
   proving `countLow (4 * k) (14 * k) < 2 ^ (13 * k)` for EVERY `k ≥ 1`, with exponential
   decay `countLow (4 * k) (14 * k) / 2^(13*k) ≤ 0.955^k → 0`!
3. **Hard-Residue Existence Strictly Above Slope `1.0` (`exists_hard_residue_slope_14_13`)**:
   By pure-`Nat` pigeonhole over `ℤ / 2^(13k) ℤ`, for EVERY `k ≥ 1`, there exists `r < 2^(13k)`
   such that EVERY `4k`-digit integer `N < 10^(4k)` with `N ≡ r (mod 2^(13k))` satisfies:
     **`digitSum N > 14 * k`** (slope `14/13 ≈ 1.0769 > 1.0`, a 3.77x jump over the
     unconstrained-length covering lower bound `2/7 ≈ 0.2857`!).
-/

namespace Ch3LengthPhaseTransition

def digitSum (n : Nat) : Nat :=
  if h : n < 10 then n
  else n % 10 + digitSum (n / 10)
termination_by n
decreasing_by omega

def sumRange (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumRange f n + f n

/-- Number of `D`-digit integers `n < 10^D` with `digitSum n ≤ M`. -/
def countLow (D M : Nat) : Nat :=
  sumRange (fun n => if digitSum n ≤ M then 1 else 0) (10 ^ D)

/-- Integer moment-generating sum for one decimal digit at `z = p / q`: `∑_{d<10} p^d * q^(9-d)`. -/
def mgf10 (p q : Nat) : Nat :=
  sumRange (fun d => p ^ d * q ^ (9 - d)) 10

/-- Full `D`-digit moment sum `∑_{n < 10^D} p^(s(n)) * q^(9*D - s(n))`. -/
def totalMgf (D p q : Nat) : Nat :=
  sumRange (fun n => p ^ digitSum n * q ^ (9 * D - digitSum n)) (10 ^ D)

theorem nat_strong_ind {P : Nat → Prop} (h : ∀ n, (∀ k < n, P k) → P n) : ∀ n, P n :=
  fun n => Nat.strongRecOn n h

theorem digitSum_zero : digitSum 0 = 0 := by unfold digitSum; simp
theorem digitSum_lt_ten {n : Nat} (h : n < 10) : digitSum n = n := by unfold digitSum; simp [h]

theorem digitSum_eq (n : Nat) : digitSum n = n % 10 + digitSum (n / 10) := by
  by_cases h : n < 10
  · rw [digitSum_lt_ten h, Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h, digitSum_zero]; omega
  · conv => lhs; unfold digitSum; simp [h]

theorem digitSum_10_mul_add {x d : Nat} (hd : d < 10) : digitSum (10 * x + d) = d + digitSum x := by
  rw [digitSum_eq (10 * x + d)]
  have hm : (10 * x + d) % 10 = d := by omega
  have hdiv : (10 * x + d) / 10 = x := by omega
  rw [hm, hdiv]

theorem digitSum_le_9D : ∀ D n : Nat, n < 10 ^ D → digitSum n ≤ 9 * D := by
  intro D; induction D with
  | zero => intro n hn; simp at hn; subst hn; simp [digitSum_zero]
  | succ D ih =>
    intro n hn; rw [digitSum_eq n]
    have hdiv : n / 10 < 10 ^ D := by rw [Nat.pow_succ] at hn; omega
    have := ih (n / 10) hdiv; omega

theorem sumRange_add (f : Nat → Nat) (a b : Nat) :
    sumRange f (a + b) = sumRange f a + sumRange (fun i => f (a + i)) b := by
  induction b with
  | zero => simp [sumRange]
  | succ b ih =>
    have h : a + (b + 1) = (a + b) + 1 := by omega
    rw [h, sumRange, sumRange, ih]; omega

theorem sumRange_mul_ten (f : Nat → Nat) (N : Nat) :
    sumRange f (10 * N) = sumRange (fun x => sumRange (fun d => f (10 * x + d)) 10) N := by
  induction N with
  | zero => simp [sumRange]
  | succ N ih =>
    have h : 10 * (N + 1) = 10 * N + 10 := by omega
    rw [h, sumRange_add, ih]; rfl

theorem sumRange_mul_const (c : Nat) (f : Nat → Nat) (N : Nat) :
    sumRange (fun i => c * f i) N = c * sumRange f N := by
  induction N with
  | zero => simp [sumRange]
  | succ N ih => simp only [sumRange, ih, Nat.mul_add]

theorem sumRange_mul_right_const (f : Nat → Nat) (c : Nat) (N : Nat) :
    sumRange (fun i => f i * c) N = sumRange f N * c := by
  induction N with
  | zero => simp [sumRange]
  | succ N ih => simp only [sumRange, ih, Nat.add_mul]

theorem sumRange_congr {f g : Nat → Nat} {N : Nat} (h : ∀ i, i < N → f i = g i) :
    sumRange f N = sumRange g N := by
  induction N with
  | zero => simp [sumRange]
  | succ N ih => simp only [sumRange]; rw [ih (fun i hi => h i (by omega)), h N (by omega)]

theorem sumRange_le {f g : Nat → Nat} {N : Nat} (h : ∀ i, i < N → f i ≤ g i) :
    sumRange f N ≤ sumRange g N := by
  induction N with
  | zero => simp [sumRange]
  | succ N ih =>
    simp only [sumRange]
    have h1 := ih (fun i hi => h i (by omega))
    have h2 := h N (by omega); omega

/-! ### Part 1: Exact Factorization of `totalMgf D p q = (mgf10 p q)^D` -/

theorem totalMgf_eq_pow (D p q : Nat) : totalMgf D p q = (mgf10 p q) ^ D := by
  induction D with
  | zero => unfold totalMgf; simp [sumRange, digitSum_zero]
  | succ D ih =>
    unfold totalMgf
    have hpow : 10 ^ (D + 1) = 10 * 10 ^ D := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow, sumRange_mul_ten]
    have hinner : ∀ x, x < 10 ^ D →
        sumRange (fun d => p ^ digitSum (10 * x + d) * q ^ (9 * (D + 1) - digitSum (10 * x + d))) 10 =
        (p ^ digitSum x * q ^ (9 * D - digitSum x)) * mgf10 p q := by
      intro x hx
      have hle9D := digitSum_le_9D D x hx
      have hterm : ∀ d, d < 10 →
          p ^ digitSum (10 * x + d) * q ^ (9 * (D + 1) - digitSum (10 * x + d)) =
          (p ^ digitSum x * q ^ (9 * D - digitSum x)) * (p ^ d * q ^ (9 - d)) := by
        intro d hd
        rw [digitSum_10_mul_add hd, Nat.pow_add]
        have hsub : 9 * (D + 1) - (d + digitSum x) = (9 * D - digitSum x) + (9 - d) := by omega
        rw [hsub, Nat.pow_add]
        rw [Nat.mul_comm (p ^ d) (p ^ digitSum x),
            Nat.mul_assoc (p ^ digitSum x) (p ^ d),
            Nat.mul_left_comm (p ^ d) (q ^ (9 * D - digitSum x)) (q ^ (9 - d)),
            ← Nat.mul_assoc (p ^ digitSum x) (q ^ (9 * D - digitSum x))]
      rw [sumRange_congr hterm, sumRange_mul_const]
      rfl
    rw [sumRange_congr hinner, sumRange_mul_right_const]
    change totalMgf D p q * mgf10 p q = mgf10 p q ^ (D + 1)
    rw [ih, Nat.pow_succ]

theorem mono_pow_ratio {p q a b T : Nat} (hpq : p ≤ q) (hab : a ≤ b) (hbT : b ≤ T) :
    p ^ b * q ^ (T - b) ≤ p ^ a * q ^ (T - a) := by
  have h1 : p ^ b = p ^ a * p ^ (b - a) := by rw [← Nat.pow_add]; congr 1; omega
  have h2 : q ^ (T - a) = q ^ (b - a) * q ^ (T - b) := by rw [← Nat.pow_add]; congr 1; omega
  rw [h1, h2]
  have hpq_pow : p ^ (b - a) ≤ q ^ (b - a) := Nat.pow_le_pow_left hpq (b - a)
  calc p ^ a * p ^ (b - a) * q ^ (T - b)
      ≤ p ^ a * q ^ (b - a) * q ^ (T - b) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hpq_pow)
    _ = p ^ a * (q ^ (b - a) * q ^ (T - b)) := Nat.mul_assoc _ _ _

/-- **1. Pure-`Nat` Capped-Digit Chernoff Bound**:
    For `p ≤ q` and `M ≤ 9 * D`: `countLow D M * p^M * q^(9*D - M) ≤ (mgf10 p q)^D`. -/
theorem capped_chernoff_bound {D M p q : Nat} (hpq : p ≤ q) (hMD : M ≤ 9 * D) :
    countLow D M * (p ^ M * q ^ (9 * D - M)) ≤ (mgf10 p q) ^ D := by
  rw [← totalMgf_eq_pow]
  unfold countLow totalMgf
  rw [← sumRange_mul_right_const]
  refine sumRange_le (fun n hn => ?_)
  by_cases h : digitSum n ≤ M
  · rw [if_pos h, Nat.one_mul]
    exact mono_pow_ratio hpq h hMD
  · rw [if_neg h, Nat.zero_mul]
    exact Nat.zero_le _

/-! ### Part 2: Exact Phase Transition at `(D, t) = (4k, 13k)` (Slope `14/13 ≈ 1.0769 > 1.0`) -/

theorem mgf10_15_17_val : mgf10 15 17 = 719671754912 := by decide

theorem decay_step_14_13 : (719671754912 : Nat) ^ 4 < 2 ^ 13 * (15 ^ 14 * 17 ^ 22) := by decide

theorem pow_lt_pow_of_lt {a b : Nat} (hab : a < b) : ∀ k : Nat, k ≥ 1 → a ^ k < b ^ k := by
  intro k hk
  cases k with
  | zero => omega
  | succ k' =>
    induction k' with
    | zero => simpa using hab
    | succ m ih =>
      have hm := ih (by omega)
      rw [Nat.pow_succ, Nat.pow_succ]
      calc a ^ (m + 1) * a ≤ a ^ (m + 1) * b := Nat.mul_le_mul_left _ (by omega)
        _ < b ^ (m + 1) * b := Nat.mul_lt_mul_of_pos_right hm (by omega)

/-- **2. Exact Length-Sparsity Exponential Decay (`countLow (4k) (14k) < 2^(13k)`)**:
    At the exact length scale of `2^(13k) < 10^(4k)`, the number of `4k`-digit integers with
    `s(N) ≤ 14k` (slope `14/13 ≈ 1.0769 > 1.0`) is STRICTLY smaller than `2^(13k)` (decay `0.955^k → 0`)! -/
theorem length_sparsity_lt_pow2 {k : Nat} (hk : k ≥ 1) :
    countLow (4 * k) (14 * k) < 2 ^ (13 * k) := by
  have hch := capped_chernoff_bound (D := 4 * k) (M := 14 * k) (p := 15) (q := 17) (by decide) (by omega)
  rw [mgf10_15_17_val] at hch
  have hsub : 9 * (4 * k) - 14 * k = 22 * k := by omega
  rw [hsub] at hch
  have hweight : 15 ^ (14 * k) * 17 ^ (22 * k) = (15 ^ 14 * 17 ^ 22) ^ k := by
    rw [Nat.mul_pow, Nat.pow_mul, Nat.pow_mul]
  have hmgf : (719671754912 : Nat) ^ (4 * k) = ((719671754912 : Nat) ^ 4) ^ k := by
    rw [Nat.pow_mul]
  rw [hweight, hmgf] at hch
  have hstrict : ((719671754912 : Nat) ^ 4) ^ k < (2 ^ 13 * (15 ^ 14 * 17 ^ 22)) ^ k :=
    pow_lt_pow_of_lt decay_step_14_13 k hk
  rw [Nat.mul_pow, ← Nat.pow_mul 2 13 k] at hstrict
  have hlt : countLow (4 * k) (14 * k) * (15 ^ 14 * 17 ^ 22) ^ k <
             2 ^ (13 * k) * (15 ^ 14 * 17 ^ 22) ^ k :=
    Nat.lt_of_le_of_lt hch hstrict
  exact Nat.lt_of_mul_lt_mul_right hlt

/-! ### Part 3: Pure-`Nat` Pigeonhole → Hard Residue Classes Strictly Above Slope `1.0` -/

theorem sumRange_indicator_lt_implies_zero {P : Nat → Bool} {N : Nat}
    (hlt : sumRange (fun r => if P r then 1 else 0) N < N) :
    ∃ r, r < N ∧ P r = false := by
  induction N with
  | zero => simp [sumRange] at hlt
  | succ N ih =>
    simp only [sumRange] at hlt
    by_cases hN : P N = false
    · exact ⟨N, by omega, hN⟩
    · have hNt : P N = true := by cases h : P N <;> simp_all
      rw [hNt] at hlt; simp at hlt
      obtain ⟨r, hr, hPr⟩ := ih (by omega)
      exact ⟨r, by omega, hPr⟩

/-- Every residue `r < R` hit by some `n < L` with `s(n) ≤ M` contributes at most `1` to `hitCount`,
    and `hitCount ≤ countLow D M`! -/
def isHit (D M R r : Nat) : Bool :=
  (List.range (10 ^ D)).any (fun n => decide (n % R = r ∧ digitSum n ≤ M))

-- Better: avoid `List.range (10^D)` (just use `∃ n < 10^D` via pure `Nat` double-sum bound!).
theorem count_hit_residues_le (D M R : Nat) (hR : R ≥ 1) :
    ∀ f : Nat → Bool,
      (∀ r, r < R → f r = true → ∃ n, n < 10 ^ D ∧ n % R = r ∧ digitSum n ≤ M) →
      sumRange (fun r => if f r then 1 else 0) R ≤ countLow D M := by
  -- Prove by induction on `K ≤ R`: the sum of `1`s over `r < K` is bounded by
  -- `∑_{n < 10^D} (if n % R < K ∧ digitSum n ≤ M then 1 else 0)`!
  intro f hf
  have hgen : ∀ K, K ≤ R →
      sumRange (fun r => if f r then 1 else 0) K ≤
      sumRange (fun n => if n % R < K ∧ digitSum n ≤ M then 1 else 0) (10 ^ D) := by
    intro K; induction K with
    | zero => intro _; simp [sumRange]
    | succ K ih =>
      intro hKR
      simp only [sumRange]
      have hprev := ih (by omega)
      by_cases hfK : f K = true
      · rw [if_pos hfK]
        obtain ⟨n0, hn0_lt, hn0_mod, hn0_ds⟩ := hf K (by omega) hfK
        -- Split `sumRange ... (10^D)` at `n0`: every `n` with `n % R < K` still counts,
        -- AND `n0` has `n0 % R = K` (not `< K`) so it adds `+1` strictly!
        have hstep : ∀ N, n0 < N →
            sumRange (fun n => if n % R < K ∧ digitSum n ≤ M then 1 else 0) N + 1 ≤
            sumRange (fun n => if n % R < K + 1 ∧ digitSum n ≤ M then 1 else 0) N := by
          intro N; induction N with
          | zero => intro h; omega
          | succ N ihN =>
            intro hltN
            simp only [sumRange]
            by_cases heq : n0 = N
            · subst heq
              have hle_rest :
                  sumRange (fun n => if n % R < K ∧ digitSum n ≤ M then 1 else 0) n0 ≤
                  sumRange (fun n => if n % R < K + 1 ∧ digitSum n ≤ M then 1 else 0) n0 :=
                sumRange_le (fun n _ => by
                  by_cases h1 : n % R < K ∧ digitSum n ≤ M
                  · rw [if_pos h1, if_pos ⟨by omega, h1.2⟩]; exact Nat.le_refl _
                  · rw [if_neg h1]; split <;> omega)
              have hnotK : ¬ (n0 % R < K ∧ digitSum n0 ≤ M) := by omega
              have hisK1 : n0 % R < K + 1 ∧ digitSum n0 ≤ M := ⟨by omega, hn0_ds⟩
              rw [if_neg hnotK, if_pos hisK1]; omega
            · have hrec := ihN (by omega)
              have hN_le : (if N % R < K ∧ digitSum N ≤ M then 1 else 0) ≤
                           (if N % R < K + 1 ∧ digitSum N ≤ M then 1 else 0) := by
                by_cases h1 : N % R < K ∧ digitSum N ≤ M
                · rw [if_pos h1, if_pos ⟨by omega, h1.2⟩]; exact Nat.le_refl _
                · rw [if_neg h1]; split <;> omega
              omega
        have := hstep (10 ^ D) hn0_lt
        omega
      · have hff : f K = false := by cases h : f K <;> simp_all
        rw [if_neg (by rw [hff]; decide)]
        have hle :
            sumRange (fun n => if n % R < K ∧ digitSum n ≤ M then 1 else 0) (10 ^ D) ≤
            sumRange (fun n => if n % R < K + 1 ∧ digitSum n ≤ M then 1 else 0) (10 ^ D) :=
          sumRange_le (fun n _ => by
            by_cases h1 : n % R < K ∧ digitSum n ≤ M
            · rw [if_pos h1, if_pos ⟨by omega, h1.2⟩]; exact Nat.le_refl _
            · rw [if_neg h1]; split <;> omega)
        omega
  have hfull := hgen R (Nat.le_refl R)
  have hle_total : sumRange (fun n => if n % R < R ∧ digitSum n ≤ M then 1 else 0) (10 ^ D) ≤
                   countLow D M := by
    unfold countLow
    refine sumRange_le (fun n _ => ?_)
    by_cases h : digitSum n ≤ M
    · rw [if_pos h, if_pos ⟨Nat.mod_lt n (by omega), h⟩]; exact Nat.le_refl _
    · rw [if_neg h, if_neg (fun hc => h hc.2)]; exact Nat.le_refl _
  exact Nat.le_trans hfull hle_total

/-- Decidable check whether residue `r` is hit by some `n < L` with `digitSum n ≤ M`. -/
def existsHit (L M R r : Nat) : Bool :=
  match L with
  | 0 => false
  | L' + 1 => decide (L' % R = r ∧ digitSum L' ≤ M) || existsHit L' M R r

theorem existsHit_iff (L M R r : Nat) :
    existsHit L M R r = true ↔ ∃ n, n < L ∧ n % R = r ∧ digitSum n ≤ M := by
  induction L with
  | zero => simp [existsHit]
  | succ L ih =>
    simp only [existsHit, Bool.or_eq_true, decide_eq_true_eq, ih]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨n, hn, h1, h2⟩)
      · exact ⟨L, by omega, h1, h2⟩
      · exact ⟨n, by omega, h1, h2⟩
    · rintro ⟨n, hn, h1, h2⟩
      by_cases hEq : n = L
      · subst hEq; left; exact ⟨h1, h2⟩
      · right; exact ⟨n, by omega, h1, h2⟩

/-- **3. HEADLINE — Hard-Residue Existence Strictly Above Slope `1.0` (`14/13 ≈ 1.0769`)**:
    For EVERY `k ≥ 1`, there exists a residue `r < 2^(13k)` such that EVERY `4k`-digit integer
    `N < 10^(4k)` with `N ≡ r (mod 2^(13k))` satisfies **`digitSum N > 14 * k`**! -/
theorem exists_hard_residue_slope_14_13 {k : Nat} (hk : k ≥ 1) :
    ∃ r : Nat, r < 2 ^ (13 * k) ∧
      ∀ N : Nat, N < 10 ^ (4 * k) → N % 2 ^ (13 * k) = r → digitSum N > 14 * k := by
  let R := 2 ^ (13 * k)
  have hR_pos : R ≥ 1 := by
    have hp : ∀ n, 2 ^ n ≥ 1 := by
      intro n; induction n with | zero => simp | succ m ih => rw [Nat.pow_succ]; omega
    exact hp (13 * k)
  let f := existsHit (10 ^ (4 * k)) (14 * k) R
  have hcount : sumRange (fun r => if f r then 1 else 0) R ≤ countLow (4 * k) (14 * k) := by
    refine count_hit_residues_le (4 * k) (14 * k) R hR_pos f ?_
    intro r _ hfr
    exact (existsHit_iff _ _ _ _).mp hfr
  have hlt : sumRange (fun r => if f r then 1 else 0) R < R :=
    Nat.lt_of_le_of_lt hcount (length_sparsity_lt_pow2 hk)
  obtain ⟨r, hr_lt, hfr_false⟩ := sumRange_indicator_lt_implies_zero hlt
  refine ⟨r, hr_lt, ?_⟩
  intro N hN_lt hN_mod
  by_cases hgt : digitSum N > 14 * k
  · exact hgt
  · exfalso
    have htrue : f r = true := (existsHit_iff _ _ _ _).mpr ⟨N, hN_lt, hN_mod, by omega⟩
    rw [hfr_false] at htrue
    exact absurd htrue (by decide)

#print axioms capped_chernoff_bound
#print axioms length_sparsity_lt_pow2
#print axioms exists_hard_residue_slope_14_13

end Ch3LengthPhaseTransition
