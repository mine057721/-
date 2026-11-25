/-!
# Chapter 2: Universal Multi-Modulus Local No-Go Theorem (`M * 2^t ∣ N`, `5 ∤ N`, `s(N) ≤ 0.7t + O(M)`) (Lean 4)

Self-contained pure Lean 4.16.0 core (zero Mathlib, zero `sorry`, zero `native_decide`,
only standard axioms `[propext, Quot.sound]`).

## Driving Question from Chapter 1
Pure 2-adic divisibility (`2^t ∣ N`, `5 ∤ N`) allows `s(N) ≤ 0.7t + 1.9`, so it cannot prove `s(N) ≥ t`.
What if we ALSO impose `27 ∣ N` (as in `TrapCond 27 9 0`, forcing `9 ∣ s(N)`), or ANY finite
collection of prime-power divisibility constraints `M ∣ N` with `gcd(M, 10) = 1`?

## Main Results
1. **Constructive Pure-Core Extended Euclidean / Modular Inverse (`exists_mul_mod_eq`)**:
   For ANY `M ≥ 1`, ANY `a` with `Nat.gcd a M = 1`, and ANY `r < M`, constructively produces
   `c < M` with `(c * a) % M = r` (via `egcd` over `Int`, zero `Classical.choice`!).
2. **Universal Multi-Modulus Local No-Go Theorem (`universal_local_modular_nogo`)**:
   For EVERY modulus `M ≥ 1` with `Nat.gcd M 10 = 1` and EVERY `t ≥ 1`:
     `∃ N ≥ 1, M * 2^t ∣ N ∧ ¬ (5 ∣ N) ∧ 10 * digitSum N ≤ 7 * t + 10 * M + 83`.
   Adding ANY finite set of non-2, non-5 prime-power divisibility constraints (`27`, `243`,
   `3 * 7 * 11 * 13 * 17`, ...) adds at most a constant `O(M)` offset and **ZERO slope**!
3. **Sharp `M = 27` Instantiation (`trap27_local_2adic_3adic_nogo`)**:
   Since `∀ c < 27, s(c) ≤ 10`, for EVERY `t ≥ 1`:
     `∃ N ≥ 1, 27 * 2^t ∣ N ∧ ¬ (5 ∣ N) ∧ 10 * digitSum N ≤ 7 * t + 183`.
   Hence for ALL `t ≥ 62`, even simultaneous 2-adic + 3-adic (`27 * 2^t ∣ N, 5 ∤ N`)
   divisibility is PROVABLY INSUFFICIENT to force `s(N) ≥ t`!
-/

namespace Ch2UniversalLocalNoGo

def digitSum (n : Nat) : Nat :=
  if h : n < 10 then n
  else n % 10 + digitSum (n / 10)
termination_by n
decreasing_by omega

def digitSumFuel : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n = 0 then 0 else n % 10 + digitSumFuel fuel (n / 10)

theorem nat_strong_ind {P : Nat → Prop} (h : ∀ n, (∀ k < n, P k) → P n) : ∀ n, P n :=
  fun n => Nat.strongRecOn n h

theorem digitSum_zero : digitSum 0 = 0 := by unfold digitSum; simp
theorem digitSum_lt_ten {n : Nat} (h : n < 10) : digitSum n = n := by unfold digitSum; simp [h]

theorem digitSum_eq (n : Nat) : digitSum n = n % 10 + digitSum (n / 10) := by
  by_cases h : n < 10
  · rw [digitSum_lt_ten h, Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h, digitSum_zero]; omega
  · conv => lhs; unfold digitSum; simp [h]

theorem digitSum_mul_ten (n : Nat) : digitSum (10 * n) = digitSum n := by
  rw [digitSum_eq (10 * n)]
  have h1 : (10 * n) % 10 = 0 := by omega
  have h2 : (10 * n) / 10 = n := by omega
  rw [h1, h2]; omega

theorem digitSum_mul_pow10 (k n : Nat) : digitSum (n * 10 ^ k) = digitSum n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (n * 10 ^ k) 10, digitSum_mul_ten, ih]

theorem digitSum_add_le : ∀ x y : Nat, digitSum (x + y) ≤ digitSum x + digitSum y := by
  intro x
  refine nat_strong_ind (P := fun x => ∀ y, digitSum (x + y) ≤ digitSum x + digitSum y) ?_ x
  intro x ih y
  by_cases hx : x = 0
  · subst hx; simp [digitSum_zero]
  · rw [digitSum_eq (x + y), digitSum_eq x, digitSum_eq y]
    by_cases hc : x % 10 + y % 10 < 10
    · have hm : (x + y) % 10 = x % 10 + y % 10 := by omega
      have hd : (x + y) / 10 = x / 10 + y / 10 := by omega
      rw [hm, hd]; have := ih (x / 10) (by omega) (y / 10); omega
    · have hm : (x + y) % 10 = x % 10 + y % 10 - 10 := by omega
      have hd : (x + y) / 10 = x / 10 + (y / 10 + 1) := by omega
      rw [hm, hd]
      have hrec1 := ih (x / 10) (by omega) (y / 10 + 1)
      have hsucc : ∀ z, digitSum (z + 1) ≤ digitSum z + 1 := by
        refine nat_strong_ind (P := fun z => digitSum (z + 1) ≤ digitSum z + 1) ?_
        intro z ihz; rw [digitSum_eq (z + 1), digitSum_eq z]
        by_cases hz : z % 10 < 9
        · have hm1 : (z + 1) % 10 = z % 10 + 1 := by omega
          have hd1 : (z + 1) / 10 = z / 10 := by omega
          rw [hm1, hd1]; omega
        · have hm1 : (z + 1) % 10 = 0 := by omega
          have hd1 : (z + 1) / 10 = z / 10 + 1 := by omega
          rw [hm1, hd1]; have := ihz (z / 10) (by omega); omega
      have := hsucc (y / 10); omega

theorem digitSum_le_self : ∀ n : Nat, digitSum n ≤ n := by
  refine nat_strong_ind (P := fun n => digitSum n ≤ n) ?_
  intro n ih
  by_cases h : n < 10
  · rw [digitSum_lt_ten h]; omega
  · rw [digitSum_eq n]; have := ih (n / 10) (by omega); omega

theorem digitSumFuel_eq_of_lt : ∀ fuel n : Nat, n < 10 ^ fuel → digitSumFuel fuel n = digitSum n := by
  intro fuel; induction fuel with
  | zero => intro n hn; simp at hn; subst hn; simp [digitSumFuel, digitSum_zero]
  | succ fuel ih =>
    intro n hn; simp only [digitSumFuel]
    by_cases h0 : n = 0
    · subst h0; simp [digitSum_zero]
    · rw [if_neg h0, digitSum_eq n]
      exact congrArg (n % 10 + ·) (ih (n / 10) (by rw [Nat.pow_succ] at hn; omega))

/-! ### Part 1: Constructive Extended Euclidean Algorithm & Modular Inverse -/

def egcd (a b : Nat) : Int × Int :=
  if hb : b = 0 then (1, 0)
  else
    let (x, y) := egcd b (a % b)
    (y, x - (a / b : Nat) * y)
termination_by b
decreasing_by exact Nat.mod_lt a (Nat.pos_of_ne_zero hb)

theorem egcd_spec :
    ∀ b a : Nat, (egcd a b).1 * (a : Int) + (egcd a b).2 * (b : Int) = (Nat.gcd a b : Int) := by
  refine nat_strong_ind (P := fun b => ∀ a, (egcd a b).1 * (a : Int) + (egcd a b).2 * (b : Int) = (Nat.gcd a b : Int)) ?_
  intro b ih a
  by_cases hb : b = 0
  · subst hb; unfold egcd; simp
  · conv => lhs; unfold egcd; simp only [hb, dite_false]
    have hlt : a % b < b := Nat.mod_lt a (Nat.pos_of_ne_zero hb)
    have hrec := ih (a % b) hlt b
    have hgcd : Nat.gcd a b = Nat.gcd b (a % b) := by
      rw [Nat.gcd_comm, Nat.gcd_rec, Nat.gcd_comm]
    rw [hgcd]
    have hdiv : (a : Int) = (b : Int) * ((a / b : Nat) : Int) + ((a % b : Nat) : Int) := by
      have h := (Nat.div_add_mod a b).symm
      omega
    -- Algebraic identity: `y * a + (x - q * y) * b = x * b + y * (a - q * b) = x * b + y * (a % b)`!
    let p := egcd b (a % b)
    change p.2 * (a : Int) + (p.1 - ((a / b : Nat) : Int) * p.2) * (b : Int) = (Nat.gcd b (a % b) : Int)
    have hrec' : p.1 * (b : Int) + p.2 * ((a % b : Nat) : Int) = (Nat.gcd b (a % b) : Int) := hrec
    have halg : p.2 * (a : Int) + (p.1 - ((a / b : Nat) : Int) * p.2) * (b : Int) =
                p.1 * (b : Int) + p.2 * ((a % b : Nat) : Int) := by
      rw [hdiv, Int.mul_add, Int.sub_mul]
      have hcomm : p.2 * ((b : Int) * ((a / b : Nat) : Int)) = ((a / b : Nat) : Int) * p.2 * (b : Int) := by
        rw [Int.mul_comm p.2, Int.mul_assoc, Int.mul_comm (b : Int)]
      omega
    rw [halg, hrec']

/-- Constructive modular surjectivity: if `M ≥ 1` and `Nat.gcd a M = 1`, then for every `r < M`
    there exists `c < M` with `(c * a) % M = r`. -/
theorem exists_mul_mod_eq {M a r : Nat} (hM : M ≥ 1) (hcop : Nat.gcd a M = 1) (hr : r < M) :
    ∃ c : Nat, c < M ∧ (c * a) % M = r := by
  have hbez := egcd_spec M a
  rw [hcop] at hbez
  let u : Int := (egcd a M).1
  let v : Int := (egcd a M).2
  let t : Int := ((r : Int) * u) % (M : Int)
  have hMpos : (M : Int) > 0 := by omega
  have ht_nonneg : 0 ≤ t := Int.emod_nonneg _ (by omega)
  have ht_lt : t < (M : Int) := Int.emod_lt_of_pos _ hMpos
  let c : Nat := t.toNat
  have hc_int : (c : Int) = t := Int.toNat_of_nonneg ht_nonneg
  have hc_lt : c < M := by omega
  refine ⟨c, hc_lt, ?_⟩
  -- Prove `((c * a : Nat) : Int) % (M : Int) = (r : Int)`!
  have hmod_int : (((c * a : Nat) : Int) % (M : Int)) = (r : Int) := by
    have h1 : ((c * a : Nat) : Int) = t * (a : Int) := by rw [← hc_int]; rfl
    rw [h1]
    have h2 : (t * (a : Int)) % (M : Int) = (((r : Int) * u) * (a : Int)) % (M : Int) := by
      dsimp only [t]
      rw [Int.mul_emod, Int.emod_emod, ← Int.mul_emod]
    rw [h2, Int.mul_assoc]
    have hua : u * (a : Int) = 1 - v * (M : Int) := by
      change u * (a : Int) + v * (M : Int) = 1 at hbez; omega
    rw [hua, Int.mul_sub, Int.mul_one, ← Int.mul_assoc]
    have hsub : ((r : Int) - (r : Int) * v * (M : Int)) % (M : Int) = (r : Int) % (M : Int) := by
      have : (r : Int) - (r : Int) * v * (M : Int) = (r : Int) + (-((r : Int) * v)) * (M : Int) := by
        rw [Int.neg_mul]; omega
      rw [this, Int.add_mul_emod_self_right]  -- Lean 4.37: renamed from Int.add_mul_emod_self
    rw [hsub, Int.emod_eq_of_lt (by omega) (by omega)]
  have hcast : (((c * a) % M : Nat) : Int) = ((c * a : Nat) : Int) % (M : Int) := rfl
  omega

theorem gcd_mul_right_eq_one {a b M : Nat} (ha : Nat.gcd a M = 1) (hb : Nat.gcd b M = 1) :
    Nat.gcd (a * b) M = 1 := by
  have hbez1 := egcd_spec M a; rw [ha] at hbez1
  have hbez2 := egcd_spec M b; rw [hb] at hbez2
  let d := Nat.gcd (a * b) M
  have hd_ab : (d : Int) ∣ ((a * b : Nat) : Int) := Int.ofNat_dvd.mpr (Nat.gcd_dvd_left _ _)
  have hd_M : (d : Int) ∣ (M : Int) := Int.ofNat_dvd.mpr (Nat.gcd_dvd_right _ _)
  -- Multiply `(x1*a + y1*M) * (x2*b + y2*M) = 1`, expand: `d ∣ 1`!
  let x1 := (egcd a M).1; let y1 := (egcd a M).2
  let x2 := (egcd b M).1; let y2 := (egcd b M).2
  have hprod : (x1 * (a : Int) + y1 * (M : Int)) * (x2 * (b : Int) + y2 * (M : Int)) = 1 := by
    rw [hbez1, hbez2]; rfl
  have hexp : (x1 * (a : Int) + y1 * (M : Int)) * (x2 * (b : Int) + y2 * (M : Int)) =
      (x1 * x2) * ((a * b : Nat) : Int) + (x1 * (a : Int) * y2 + y1 * (x2 * (b : Int) + y2 * (M : Int))) * (M : Int) := by
    rw [Int.add_mul, Int.mul_add]
    have h1 : x1 * (a : Int) * (x2 * (b : Int)) = x1 * x2 * ((a * b : Nat) : Int) := by
      have : ((a * b : Nat) : Int) = (a : Int) * (b : Int) := rfl
      rw [this, Int.mul_assoc x1 (a : Int), Int.mul_left_comm (a : Int) x2 (b : Int), ← Int.mul_assoc]
    have h2 : x1 * (a : Int) * (y2 * (M : Int)) = x1 * (a : Int) * y2 * (M : Int) := by
      rw [← Int.mul_assoc]
    have h3 : y1 * (M : Int) * (x2 * (b : Int) + y2 * (M : Int)) =
              y1 * (x2 * (b : Int) + y2 * (M : Int)) * (M : Int) := by
      rw [Int.mul_assoc, Int.mul_comm (M : Int), ← Int.mul_assoc]
    rw [h1, h2, h3, Int.add_assoc, ← Int.add_mul]
  rw [hexp] at hprod
  have hd_one : (d : Int) ∣ 1 := by
    rw [← hprod]
    exact Int.dvd_add (Int.dvd_trans hd_ab (Int.dvd_mul_left _ _)) (Int.dvd_trans hd_M (Int.dvd_mul_left _ _))
  have hd_nat : d ∣ 1 := Int.ofNat_dvd.mp hd_one
  exact Nat.le_antisymm (Nat.le_of_dvd (by decide) hd_nat)
    (Nat.pos_of_ne_zero fun h0 => by change (a * b).gcd M ∣ 1 at hd_nat; rw [h0] at hd_nat; exact absurd (Nat.eq_zero_of_zero_dvd hd_nat) (by decide))

theorem gcd_pow_eq_one {a M : Nat} (ha : Nat.gcd a M = 1) (k : Nat) :
    Nat.gcd (a ^ k) M = 1 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.pow_succ]; exact gcd_mul_right_eq_one ih ha

theorem mul_dvd_of_gcd_one {M A N : Nat} (hcop : Nat.gcd A M = 1) (hM : M ∣ N) (hA : A ∣ N) :
    M * A ∣ N := by
  obtain ⟨q, hq⟩ := hA
  have hbez := egcd_spec M A; rw [hcop] at hbez
  -- `q = q * 1 = q * (x * A + y * M) = x * N + y * q * M`, so `M ∣ q`!
  have hM_q : (M : Int) ∣ (q : Int) := by
    have hq_eq : (q : Int) = (egcd A M).1 * (N : Int) + ((egcd A M).2 * (q : Int)) * (M : Int) := by
      have hN : (N : Int) = (A : Int) * (q : Int) := by rw [hq]; rfl
      have hbez' : (egcd A M).1 * (A : Int) + (egcd A M).2 * (M : Int) = 1 := hbez
      have h1 : (q : Int) = (q : Int) * ((egcd A M).1 * (A : Int) + (egcd A M).2 * (M : Int)) := by
        rw [hbez', Int.mul_one]
      conv => lhs; rw [h1, Int.mul_add]
      rw [hN]
      have ha : (q : Int) * ((egcd A M).1 * (A : Int)) = (egcd A M).1 * ((A : Int) * (q : Int)) := by
        rw [Int.mul_left_comm, Int.mul_comm (q : Int) (A : Int)]
      have hb : (q : Int) * ((egcd A M).2 * (M : Int)) = (egcd A M).2 * (q : Int) * (M : Int) := by
        rw [← Int.mul_assoc, Int.mul_comm (q : Int) ((egcd A M).2)]
      rw [ha, hb]
    rw [hq_eq]
    exact Int.dvd_add (Int.dvd_trans (Int.ofNat_dvd.mpr hM) (Int.dvd_mul_left _ _)) (Int.dvd_mul_left _ _)
  obtain ⟨r, hr⟩ := Int.ofNat_dvd.mp hM_q
  refine ⟨r, ?_⟩
  rw [hq, hr, Nat.mul_left_comm, Nat.mul_assoc]

/-! ### Part 2: 1024-Residue Depth-10 BTree Covering (`10 * s(N) ≤ 7 * t + 83`) -/

inductive BTree
  | leaf (v : Nat)
  | node (l r : BTree)

def BTree.get : Nat → BTree → Nat → Nat
  | 0, BTree.leaf v, _ => v
  | d + 1, BTree.node l r, idx =>
    if idx < 2 ^ d then BTree.get d l idx
    else BTree.get d r (idx - 2 ^ d)
  | _, _, _ => 0

def coverTree1024 : BTree :=
  BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 0) (BTree.leaf 1)) (BTree.node (BTree.leaf 2) (BTree.leaf 3))) (BTree.node (BTree.node (BTree.leaf 100100100) (BTree.leaf 100100101)) (BTree.node (BTree.leaf 1030) (BTree.leaf 1031)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 101000200) (BTree.leaf 101000201)) (BTree.node (BTree.leaf 10) (BTree.leaf 11))) (BTree.node (BTree.node (BTree.leaf 12) (BTree.leaf 13)) (BTree.node (BTree.leaf 100100110) (BTree.leaf 100100111))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 100010000) (BTree.leaf 100010001)) (BTree.node (BTree.leaf 100010002) (BTree.leaf 100010003))) (BTree.node (BTree.node (BTree.leaf 20) (BTree.leaf 21)) (BTree.node (BTree.leaf 22) (BTree.leaf 23)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 10111000) (BTree.leaf 10111001)) (BTree.node (BTree.leaf 100010010) (BTree.leaf 100010011))) (BTree.node (BTree.node (BTree.leaf 3100) (BTree.leaf 3101)) (BTree.node (BTree.leaf 30) (BTree.leaf 31)))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 1000020000) (BTree.leaf 1000020001)) (BTree.node (BTree.leaf 10111010) (BTree.leaf 10111011))) (BTree.node (BTree.node (BTree.leaf 10200100) (BTree.leaf 10200101)) (BTree.node (BTree.leaf 3110) (BTree.leaf 3111)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 1001001000) (BTree.leaf 1001001001)) (BTree.node (BTree.leaf 1000020010) (BTree.leaf 1000020011))) (BTree.node (BTree.node (BTree.leaf 301100) (BTree.leaf 301101)) (BTree.node (BTree.leaf 10200110) (BTree.leaf 10200111))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 10110000) (BTree.leaf 10110001)) (BTree.node (BTree.leaf 1001001010) (BTree.leaf 1001001011))) (BTree.node (BTree.node (BTree.leaf 2100) (BTree.leaf 2101)) (BTree.node (BTree.leaf 2102) (BTree.leaf 2103)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 211000) (BTree.leaf 211001)) (BTree.node (BTree.leaf 10110010) (BTree.leaf 10110011))) (BTree.node (BTree.node (BTree.leaf 10300) (BTree.leaf 10301)) (BTree.node (BTree.leaf 2110) (BTree.leaf 2111))))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 1001000000) (BTree.leaf 1001000001)) (BTree.node (BTree.leaf 1001000002) (BTree.leaf 1001000003))) (BTree.node (BTree.node (BTree.leaf 300100) (BTree.leaf 300101)) (BTree.node (BTree.leaf 10310) (BTree.leaf 10311)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 1021000) (BTree.leaf 1021001)) (BTree.node (BTree.leaf 1001000010) (BTree.leaf 1001000011))) (BTree.node (BTree.node (BTree.leaf 1100) (BTree.leaf 1101)) (BTree.node (BTree.leaf 1102) (BTree.leaf 1103))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 210000) (BTree.leaf 210001)) (BTree.node (BTree.leaf 210002) (BTree.leaf 210003))) (BTree.node (BTree.node (BTree.leaf 1110100) (BTree.leaf 1110101)) (BTree.node (BTree.leaf 1110) (BTree.leaf 1111)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 1112) (BTree.leaf 1113)) (BTree.node (BTree.leaf 210010) (BTree.leaf 210011))) (BTree.node (BTree.node (BTree.leaf 100011100) (BTree.leaf 100011101)) (BTree.node (BTree.leaf 1110110) (BTree.leaf 1110111)))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 1020000) (BTree.leaf 1020001)) (BTree.node (BTree.leaf 1020002) (BTree.leaf 1020003))) (BTree.node (BTree.node (BTree.leaf 100) (BTree.leaf 101)) (BTree.node (BTree.leaf 102) (BTree.leaf 103)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 2001000) (BTree.leaf 2001001)) (BTree.node (BTree.leaf 1020010) (BTree.leaf 1020011))) (BTree.node (BTree.node (BTree.leaf 101000300) (BTree.leaf 101000301)) (BTree.node (BTree.leaf 110) (BTree.leaf 111))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 112) (BTree.leaf 113)) (BTree.node (BTree.leaf 2001010) (BTree.leaf 2001011))) (BTree.node (BTree.node (BTree.leaf 100010100) (BTree.leaf 100010101)) (BTree.node (BTree.leaf 100010102) (BTree.leaf 100010103)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 120) (BTree.leaf 121)) (BTree.node (BTree.leaf 122) (BTree.leaf 123))) (BTree.node (BTree.node (BTree.leaf 2001020) (BTree.leaf 2001021)) (BTree.node (BTree.leaf 100010110) (BTree.leaf 100010111)))))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 2000000) (BTree.leaf 2000001)) (BTree.node (BTree.leaf 130) (BTree.leaf 131))) (BTree.node (BTree.node (BTree.leaf 1000020100) (BTree.leaf 1000020101)) (BTree.node (BTree.leaf 2001030) (BTree.leaf 2001031)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 1000101000) (BTree.leaf 1000101001)) (BTree.node (BTree.leaf 2000010) (BTree.leaf 2000011))) (BTree.node (BTree.node (BTree.leaf 1001001100) (BTree.leaf 1001001101)) (BTree.node (BTree.leaf 1000020110) (BTree.leaf 1000020111))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 11002000) (BTree.leaf 11002001)) (BTree.node (BTree.leaf 1000101010) (BTree.leaf 1000101011))) (BTree.node (BTree.node (BTree.leaf 2000020) (BTree.leaf 2000021)) (BTree.node (BTree.leaf 1001001110) (BTree.leaf 1001001111)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 2200) (BTree.leaf 2201)) (BTree.node (BTree.leaf 11002010) (BTree.leaf 11002011))) (BTree.node (BTree.node (BTree.leaf 211100) (BTree.leaf 211101)) (BTree.node (BTree.leaf 2000030) (BTree.leaf 2000031)))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 1000100000) (BTree.leaf 1000100001)) (BTree.node (BTree.leaf 1000100002) (BTree.leaf 1000100003))) (BTree.node (BTree.node (BTree.leaf 1001000100) (BTree.leaf 1001000101)) (BTree.node (BTree.leaf 1001000102) (BTree.leaf 1001000103)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 11001000) (BTree.leaf 11001001)) (BTree.node (BTree.leaf 1000100010) (BTree.leaf 1000100011))) (BTree.node (BTree.node (BTree.leaf 1021100) (BTree.leaf 1021101)) (BTree.node (BTree.leaf 1001000110) (BTree.leaf 1001000111))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 1200) (BTree.leaf 1201)) (BTree.node (BTree.leaf 11001010) (BTree.leaf 11001011))) (BTree.node (BTree.node (BTree.leaf 210100) (BTree.leaf 210101)) (BTree.node (BTree.leaf 210102) (BTree.leaf 210103)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 100003000) (BTree.leaf 100003001)) (BTree.node (BTree.leaf 1210) (BTree.leaf 1211))) (BTree.node (BTree.node (BTree.leaf 11001020) (BTree.leaf 11001021)) (BTree.node (BTree.leaf 210110) (BTree.leaf 210111))))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 11000000) (BTree.leaf 11000001)) (BTree.node (BTree.leaf 11000002) (BTree.leaf 11000003))) (BTree.node (BTree.node (BTree.leaf 1020100) (BTree.leaf 1020101)) (BTree.node (BTree.leaf 1020102) (BTree.leaf 1020103)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 200) (BTree.leaf 201)) (BTree.node (BTree.leaf 11000010) (BTree.leaf 11000011))) (BTree.node (BTree.node (BTree.leaf 2001100) (BTree.leaf 2001101)) (BTree.node (BTree.leaf 1020110) (BTree.leaf 1020111))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 100002000) (BTree.leaf 100002001)) (BTree.node (BTree.leaf 210) (BTree.leaf 211))) (BTree.node (BTree.node (BTree.leaf 11000020) (BTree.leaf 11000021)) (BTree.node (BTree.leaf 2001110) (BTree.leaf 2001111)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 100010200) (BTree.leaf 100010201)) (BTree.node (BTree.leaf 100002010) (BTree.leaf 100002011))) (BTree.node (BTree.node (BTree.leaf 220) (BTree.leaf 221)) (BTree.node (BTree.leaf 11000030) (BTree.leaf 11000031)))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 1100000) (BTree.leaf 1100001)) (BTree.node (BTree.leaf 1100002) (BTree.leaf 1100003))) (BTree.node (BTree.node (BTree.leaf 2000100) (BTree.leaf 2000101)) (BTree.node (BTree.leaf 230) (BTree.leaf 231)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 100001000) (BTree.leaf 100001001)) (BTree.node (BTree.leaf 1100010) (BTree.leaf 1100011))) (BTree.node (BTree.node (BTree.leaf 1000101100) (BTree.leaf 1000101101)) (BTree.node (BTree.leaf 2000110) (BTree.leaf 2000111))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 10102000) (BTree.leaf 10102001)) (BTree.node (BTree.leaf 100001010) (BTree.leaf 100001011))) (BTree.node (BTree.node (BTree.leaf 1100020) (BTree.leaf 1100021)) (BTree.node (BTree.leaf 1000101110) (BTree.leaf 1000101111)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 1000011000) (BTree.leaf 1000011001)) (BTree.node (BTree.leaf 10102010) (BTree.leaf 10102011))) (BTree.node (BTree.node (BTree.leaf 100001020) (BTree.leaf 100001021)) (BTree.node (BTree.leaf 1100030) (BTree.leaf 1100031))))))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 100000000) (BTree.leaf 100000001)) (BTree.node (BTree.leaf 100000002) (BTree.leaf 100000003))) (BTree.node (BTree.node (BTree.leaf 1000100100) (BTree.leaf 1000100101)) (BTree.node (BTree.leaf 100001030) (BTree.leaf 100001031)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 10101000) (BTree.leaf 10101001)) (BTree.node (BTree.leaf 100000010) (BTree.leaf 100000011))) (BTree.node (BTree.node (BTree.leaf 11001100) (BTree.leaf 11001101)) (BTree.node (BTree.leaf 1000100110) (BTree.leaf 1000100111))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 1000010000) (BTree.leaf 1000010001)) (BTree.node (BTree.leaf 10101010) (BTree.leaf 10101011))) (BTree.node (BTree.node (BTree.leaf 100000020) (BTree.leaf 100000021)) (BTree.node (BTree.leaf 11001110) (BTree.leaf 11001111)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 31000) (BTree.leaf 31001)) (BTree.node (BTree.leaf 1000010010) (BTree.leaf 1000010011))) (BTree.node (BTree.node (BTree.leaf 10101020) (BTree.leaf 10101021)) (BTree.node (BTree.leaf 100000030) (BTree.leaf 100000031)))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 10100000) (BTree.leaf 10100001)) (BTree.node (BTree.leaf 10100002) (BTree.leaf 10100003))) (BTree.node (BTree.node (BTree.leaf 11000100) (BTree.leaf 11000101)) (BTree.node (BTree.leaf 11000102) (BTree.leaf 11000103)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 201000) (BTree.leaf 201001)) (BTree.node (BTree.leaf 10100010) (BTree.leaf 10100011))) (BTree.node (BTree.node (BTree.leaf 300) (BTree.leaf 301)) (BTree.node (BTree.leaf 11000110) (BTree.leaf 11000111))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 30000) (BTree.leaf 30001)) (BTree.node (BTree.leaf 201010) (BTree.leaf 201011))) (BTree.node (BTree.node (BTree.leaf 10100020) (BTree.leaf 10100021)) (BTree.node (BTree.leaf 310) (BTree.leaf 311)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 1011000) (BTree.leaf 1011001)) (BTree.node (BTree.leaf 30010) (BTree.leaf 30011))) (BTree.node (BTree.node (BTree.leaf 201020) (BTree.leaf 201021)) (BTree.node (BTree.leaf 10100030) (BTree.leaf 10100031))))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 200000) (BTree.leaf 200001)) (BTree.node (BTree.leaf 200002) (BTree.leaf 200003))) (BTree.node (BTree.node (BTree.leaf 1100100) (BTree.leaf 1100101)) (BTree.node (BTree.leaf 1100102) (BTree.leaf 1100103)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 2000200) (BTree.leaf 2000201)) (BTree.node (BTree.leaf 200010) (BTree.leaf 200011))) (BTree.node (BTree.node (BTree.leaf 100001100) (BTree.leaf 100001101)) (BTree.node (BTree.leaf 1100110) (BTree.leaf 1100111))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 1010000) (BTree.leaf 1010001)) (BTree.node (BTree.leaf 1010002) (BTree.leaf 1010003))) (BTree.node (BTree.node (BTree.leaf 200020) (BTree.leaf 200021)) (BTree.node (BTree.leaf 100001110) (BTree.leaf 100001111)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 1100120) (BTree.leaf 1100121)) (BTree.node (BTree.leaf 1010010) (BTree.leaf 1010011))) (BTree.node (BTree.node (BTree.leaf 1000011100) (BTree.leaf 1000011101)) (BTree.node (BTree.leaf 200030) (BTree.leaf 200031)))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 3100000) (BTree.leaf 3100001)) (BTree.node (BTree.leaf 3100002) (BTree.leaf 3100003))) (BTree.node (BTree.node (BTree.leaf 100000100) (BTree.leaf 100000101)) (BTree.node (BTree.leaf 100000102) (BTree.leaf 100000103)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 102001000) (BTree.leaf 102001001)) (BTree.node (BTree.leaf 3100010) (BTree.leaf 3100011))) (BTree.node (BTree.node (BTree.leaf 10101100) (BTree.leaf 10101101)) (BTree.node (BTree.leaf 100000110) (BTree.leaf 100000111))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 10310000) (BTree.leaf 10310001)) (BTree.node (BTree.leaf 102001010) (BTree.leaf 102001011))) (BTree.node (BTree.node (BTree.leaf 1000010100) (BTree.leaf 1000010101)) (BTree.node (BTree.leaf 10101110) (BTree.leaf 10101111)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 10011000) (BTree.leaf 10011001)) (BTree.node (BTree.leaf 10011002) (BTree.leaf 10011003))) (BTree.node (BTree.node (BTree.leaf 31100) (BTree.leaf 31101)) (BTree.node (BTree.leaf 1000010110) (BTree.leaf 1000010111)))))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 102000000) (BTree.leaf 102000001)) (BTree.node (BTree.leaf 10011010) (BTree.leaf 10011011))) (BTree.node (BTree.node (BTree.leaf 10100100) (BTree.leaf 10100101)) (BTree.node (BTree.leaf 10100102) (BTree.leaf 10100103)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 11000200) (BTree.leaf 11000201)) (BTree.node (BTree.leaf 102000010) (BTree.leaf 102000011))) (BTree.node (BTree.node (BTree.leaf 201100) (BTree.leaf 201101)) (BTree.node (BTree.leaf 10100110) (BTree.leaf 10100111))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 10010000) (BTree.leaf 10010001)) (BTree.node (BTree.leaf 10010002) (BTree.leaf 10010003))) (BTree.node (BTree.node (BTree.leaf 30100) (BTree.leaf 30101)) (BTree.node (BTree.leaf 201110) (BTree.leaf 201111)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 111000) (BTree.leaf 111001)) (BTree.node (BTree.leaf 10010010) (BTree.leaf 10010011))) (BTree.node (BTree.node (BTree.leaf 1011100) (BTree.leaf 1011101)) (BTree.node (BTree.leaf 30110) (BTree.leaf 30111)))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 1100100000) (BTree.leaf 1100100001)) (BTree.node (BTree.leaf 111010) (BTree.leaf 111011))) (BTree.node (BTree.node (BTree.leaf 200100) (BTree.leaf 200101)) (BTree.node (BTree.leaf 200102) (BTree.leaf 200103)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 1100200) (BTree.leaf 1100201)) (BTree.node (BTree.leaf 1100100010) (BTree.leaf 1100100011))) (BTree.node (BTree.node (BTree.leaf 111020) (BTree.leaf 111021)) (BTree.node (BTree.leaf 200110) (BTree.leaf 200111))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 110000) (BTree.leaf 110001)) (BTree.node (BTree.leaf 110002) (BTree.leaf 110003))) (BTree.node (BTree.node (BTree.leaf 1010100) (BTree.leaf 1010101)) (BTree.node (BTree.leaf 1010102) (BTree.leaf 1010103)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 1000003000) (BTree.leaf 1000003001)) (BTree.node (BTree.leaf 110010) (BTree.leaf 110011))) (BTree.node (BTree.node (BTree.leaf 110012) (BTree.leaf 110013)) (BTree.node (BTree.leaf 1010110) (BTree.leaf 1010111))))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 111000000) (BTree.leaf 111000001)) (BTree.node (BTree.leaf 111000002) (BTree.leaf 111000003))) (BTree.node (BTree.node (BTree.leaf 110020) (BTree.leaf 110021)) (BTree.node (BTree.leaf 110022) (BTree.leaf 110023)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 100000200) (BTree.leaf 100000201)) (BTree.node (BTree.leaf 111000010) (BTree.leaf 111000011))) (BTree.node (BTree.node (BTree.leaf 102001100) (BTree.leaf 102001101)) (BTree.node (BTree.leaf 110030) (BTree.leaf 110031))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 1000002000) (BTree.leaf 1000002001)) (BTree.node (BTree.leaf 100000210) (BTree.leaf 100000211))) (BTree.node (BTree.node (BTree.leaf 111000020) (BTree.leaf 111000021)) (BTree.node (BTree.leaf 102001110) (BTree.leaf 102001111)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 1000010200) (BTree.leaf 1000010201)) (BTree.node (BTree.leaf 1000002010) (BTree.leaf 1000002011))) (BTree.node (BTree.node (BTree.leaf 10011100) (BTree.leaf 10011101)) (BTree.node (BTree.leaf 10011102) (BTree.leaf 10011103)))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 101100000) (BTree.leaf 101100001)) (BTree.node (BTree.leaf 101100002) (BTree.leaf 101100003))) (BTree.node (BTree.node (BTree.leaf 102000100) (BTree.leaf 102000101)) (BTree.node (BTree.leaf 10011110) (BTree.leaf 10011111)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 1000001000) (BTree.leaf 1000001001)) (BTree.node (BTree.leaf 101100010) (BTree.leaf 101100011))) (BTree.node (BTree.node (BTree.leaf 11000300) (BTree.leaf 11000301)) (BTree.node (BTree.leaf 102000110) (BTree.leaf 102000111))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 22000) (BTree.leaf 22001)) (BTree.node (BTree.leaf 1000001010) (BTree.leaf 1000001011))) (BTree.node (BTree.node (BTree.leaf 10010100) (BTree.leaf 10010101)) (BTree.node (BTree.leaf 10010102) (BTree.leaf 10010103)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 1003000) (BTree.leaf 1003001)) (BTree.node (BTree.leaf 22010) (BTree.leaf 22011))) (BTree.node (BTree.node (BTree.leaf 111100) (BTree.leaf 111101)) (BTree.node (BTree.leaf 10010110) (BTree.leaf 10010111)))))))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 1000000000) (BTree.leaf 1000000001)) (BTree.node (BTree.leaf 1000000002) (BTree.leaf 1000000003))) (BTree.node (BTree.node (BTree.leaf 1100100100) (BTree.leaf 1100100101)) (BTree.node (BTree.leaf 111110) (BTree.leaf 111111)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 21000) (BTree.leaf 21001)) (BTree.node (BTree.leaf 1000000010) (BTree.leaf 1000000011))) (BTree.node (BTree.node (BTree.leaf 1000000012) (BTree.leaf 1000000013)) (BTree.node (BTree.leaf 1100100110) (BTree.leaf 1100100111))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 1002000) (BTree.leaf 1002001)) (BTree.node (BTree.leaf 21010) (BTree.leaf 21011))) (BTree.node (BTree.node (BTree.leaf 110100) (BTree.leaf 110101)) (BTree.node (BTree.leaf 110102) (BTree.leaf 110103)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 1010200) (BTree.leaf 1010201)) (BTree.node (BTree.leaf 1002010) (BTree.leaf 1002011))) (BTree.node (BTree.node (BTree.leaf 21020) (BTree.leaf 21021)) (BTree.node (BTree.leaf 110110) (BTree.leaf 110111)))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 20000) (BTree.leaf 20001)) (BTree.node (BTree.leaf 20002) (BTree.leaf 20003))) (BTree.node (BTree.node (BTree.leaf 111000100) (BTree.leaf 111000101)) (BTree.node (BTree.leaf 21030) (BTree.leaf 21031)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 1001000) (BTree.leaf 1001001)) (BTree.node (BTree.leaf 20010) (BTree.leaf 20011))) (BTree.node (BTree.node (BTree.leaf 100000300) (BTree.leaf 100000301)) (BTree.node (BTree.leaf 111000110) (BTree.leaf 111000111))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 2110000) (BTree.leaf 2110001)) (BTree.node (BTree.leaf 1001010) (BTree.leaf 1001011))) (BTree.node (BTree.node (BTree.leaf 20020) (BTree.leaf 20021)) (BTree.node (BTree.leaf 100000310) (BTree.leaf 100000311)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 10003000) (BTree.leaf 10003001)) (BTree.node (BTree.leaf 2110010) (BTree.leaf 2110011))) (BTree.node (BTree.node (BTree.leaf 1001020) (BTree.leaf 1001021)) (BTree.node (BTree.leaf 20030) (BTree.leaf 20031))))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 1000000) (BTree.leaf 1000001)) (BTree.node (BTree.leaf 1000002) (BTree.leaf 1000003))) (BTree.node (BTree.node (BTree.leaf 101100100) (BTree.leaf 101100101)) (BTree.node (BTree.leaf 1001030) (BTree.leaf 1001031)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 10301000) (BTree.leaf 10301001)) (BTree.node (BTree.leaf 1000010) (BTree.leaf 1000011))) (BTree.node (BTree.node (BTree.leaf 1000001100) (BTree.leaf 1000001101)) (BTree.node (BTree.leaf 101100110) (BTree.leaf 101100111))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 10002000) (BTree.leaf 10002001)) (BTree.node (BTree.leaf 10002002) (BTree.leaf 10002003))) (BTree.node (BTree.node (BTree.leaf 1000020) (BTree.leaf 1000021)) (BTree.node (BTree.leaf 1000001110) (BTree.leaf 1000001111)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 103000) (BTree.leaf 103001)) (BTree.node (BTree.leaf 10002010) (BTree.leaf 10002011))) (BTree.node (BTree.node (BTree.leaf 1003100) (BTree.leaf 1003101)) (BTree.node (BTree.leaf 1000030) (BTree.leaf 1000031)))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 10300000) (BTree.leaf 10300001)) (BTree.node (BTree.leaf 103010) (BTree.leaf 103011))) (BTree.node (BTree.node (BTree.leaf 1000000100) (BTree.leaf 1000000101)) (BTree.node (BTree.leaf 1000000102) (BTree.leaf 1000000103)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 10001000) (BTree.leaf 10001001)) (BTree.node (BTree.leaf 10001002) (BTree.leaf 10001003))) (BTree.node (BTree.node (BTree.leaf 21100) (BTree.leaf 21101)) (BTree.node (BTree.leaf 1000000110) (BTree.leaf 1000000111))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 102000) (BTree.leaf 102001)) (BTree.node (BTree.leaf 10001010) (BTree.leaf 10001011))) (BTree.node (BTree.node (BTree.leaf 1002100) (BTree.leaf 1002101)) (BTree.node (BTree.leaf 21110) (BTree.leaf 21111)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 110200) (BTree.leaf 110201)) (BTree.node (BTree.leaf 102010) (BTree.leaf 102011))) (BTree.node (BTree.node (BTree.leaf 10001020) (BTree.leaf 10001021)) (BTree.node (BTree.leaf 1002110) (BTree.leaf 1002111)))))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 10000000) (BTree.leaf 10000001)) (BTree.node (BTree.leaf 10000002) (BTree.leaf 10000003))) (BTree.node (BTree.node (BTree.leaf 20100) (BTree.leaf 20101)) (BTree.node (BTree.leaf 20102) (BTree.leaf 20103)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 101000) (BTree.leaf 101001)) (BTree.node (BTree.leaf 10000010) (BTree.leaf 10000011))) (BTree.node (BTree.node (BTree.leaf 1001100) (BTree.leaf 1001101)) (BTree.node (BTree.leaf 20110) (BTree.leaf 20111))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 110010000) (BTree.leaf 110010001)) (BTree.node (BTree.leaf 101010) (BTree.leaf 101011))) (BTree.node (BTree.node (BTree.leaf 10000020) (BTree.leaf 10000021)) (BTree.node (BTree.leaf 1001110) (BTree.leaf 1001111)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 100111000) (BTree.leaf 100111001)) (BTree.node (BTree.leaf 110010010) (BTree.leaf 110010011))) (BTree.node (BTree.node (BTree.leaf 101020) (BTree.leaf 101021)) (BTree.node (BTree.leaf 10000030) (BTree.leaf 10000031)))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 100000) (BTree.leaf 100001)) (BTree.node (BTree.leaf 100002) (BTree.leaf 100003))) (BTree.node (BTree.node (BTree.leaf 1000100) (BTree.leaf 1000101)) (BTree.node (BTree.leaf 1000102) (BTree.leaf 1000103)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 3001000) (BTree.leaf 3001001)) (BTree.node (BTree.leaf 100010) (BTree.leaf 100011))) (BTree.node (BTree.node (BTree.leaf 100012) (BTree.leaf 100013)) (BTree.node (BTree.leaf 1000110) (BTree.leaf 1000111))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 100110000) (BTree.leaf 100110001)) (BTree.node (BTree.leaf 3001010) (BTree.leaf 3001011))) (BTree.node (BTree.node (BTree.leaf 100020) (BTree.leaf 100021)) (BTree.node (BTree.leaf 100022) (BTree.leaf 100023)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 1000120) (BTree.leaf 1000121)) (BTree.node (BTree.leaf 100110010) (BTree.leaf 100110011))) (BTree.node (BTree.node (BTree.leaf 103100) (BTree.leaf 103101)) (BTree.node (BTree.leaf 100030) (BTree.leaf 100031))))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 3000000) (BTree.leaf 3000001)) (BTree.node (BTree.leaf 3000002) (BTree.leaf 3000003))) (BTree.node (BTree.node (BTree.leaf 10300100) (BTree.leaf 10300101)) (BTree.node (BTree.leaf 103110) (BTree.leaf 103111)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 1000000200) (BTree.leaf 1000000201)) (BTree.node (BTree.leaf 3000010) (BTree.leaf 3000011))) (BTree.node (BTree.node (BTree.leaf 10001100) (BTree.leaf 10001101)) (BTree.node (BTree.leaf 10001102) (BTree.leaf 10001103))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 10210000) (BTree.leaf 10210001)) (BTree.node (BTree.leaf 1000000210) (BTree.leaf 1000000211))) (BTree.node (BTree.node (BTree.leaf 102100) (BTree.leaf 102101)) (BTree.node (BTree.leaf 10001110) (BTree.leaf 10001111)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 311000) (BTree.leaf 311001)) (BTree.node (BTree.leaf 10210010) (BTree.leaf 10210011))) (BTree.node (BTree.node (BTree.leaf 110300) (BTree.leaf 110301)) (BTree.node (BTree.leaf 102110) (BTree.leaf 102111)))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 12000) (BTree.leaf 12001)) (BTree.node (BTree.leaf 12002) (BTree.leaf 12003))) (BTree.node (BTree.node (BTree.leaf 10000100) (BTree.leaf 10000101)) (BTree.node (BTree.leaf 10000102) (BTree.leaf 10000103)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 1100001000) (BTree.leaf 1100001001)) (BTree.node (BTree.leaf 12010) (BTree.leaf 12011))) (BTree.node (BTree.node (BTree.leaf 101100) (BTree.leaf 101101)) (BTree.node (BTree.leaf 10000110) (BTree.leaf 10000111))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 310000) (BTree.leaf 310001)) (BTree.node (BTree.leaf 1100001010) (BTree.leaf 1100001011))) (BTree.node (BTree.node (BTree.leaf 110010100) (BTree.leaf 110010101)) (BTree.node (BTree.leaf 101110) (BTree.leaf 101111)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 11000) (BTree.leaf 11001)) (BTree.node (BTree.leaf 11002) (BTree.leaf 11003))) (BTree.node (BTree.node (BTree.leaf 100111100) (BTree.leaf 100111101)) (BTree.node (BTree.leaf 110010110) (BTree.leaf 110010111))))))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 1100000000) (BTree.leaf 1100000001)) (BTree.node (BTree.leaf 11010) (BTree.leaf 11011))) (BTree.node (BTree.node (BTree.leaf 100100) (BTree.leaf 100101)) (BTree.node (BTree.leaf 100102) (BTree.leaf 100103)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 1000200) (BTree.leaf 1000201)) (BTree.node (BTree.leaf 1100000010) (BTree.leaf 1100000011))) (BTree.node (BTree.node (BTree.leaf 11020) (BTree.leaf 11021)) (BTree.node (BTree.leaf 100110) (BTree.leaf 100111))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 10000) (BTree.leaf 10001)) (BTree.node (BTree.leaf 10002) (BTree.leaf 10003))) (BTree.node (BTree.node (BTree.leaf 100110100) (BTree.leaf 100110101)) (BTree.node (BTree.leaf 11030) (BTree.leaf 11031)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 100120) (BTree.leaf 100121)) (BTree.node (BTree.leaf 10010) (BTree.leaf 10011))) (BTree.node (BTree.node (BTree.leaf 10012) (BTree.leaf 10013)) (BTree.node (BTree.leaf 100110110) (BTree.leaf 100110111)))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 2100000) (BTree.leaf 2100001)) (BTree.node (BTree.leaf 100130) (BTree.leaf 100131))) (BTree.node (BTree.node (BTree.leaf 10020) (BTree.leaf 10021)) (BTree.node (BTree.leaf 10022) (BTree.leaf 10023)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 101001000) (BTree.leaf 101001001)) (BTree.node (BTree.leaf 2100010) (BTree.leaf 2100011))) (BTree.node (BTree.node (BTree.leaf 1000000300) (BTree.leaf 1000000301)) (BTree.node (BTree.leaf 10030) (BTree.leaf 10031))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 10001200) (BTree.leaf 10001201)) (BTree.node (BTree.leaf 101001010) (BTree.leaf 101001011))) (BTree.node (BTree.node (BTree.leaf 2100020) (BTree.leaf 2100021)) (BTree.node (BTree.leaf 1000000310) (BTree.leaf 1000000311)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 1001011000) (BTree.leaf 1001011001)) (BTree.node (BTree.leaf 10001210) (BTree.leaf 10001211))) (BTree.node (BTree.node (BTree.leaf 101001020) (BTree.leaf 101001021)) (BTree.node (BTree.leaf 2100030) (BTree.leaf 2100031))))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 101000000) (BTree.leaf 101000001)) (BTree.node (BTree.leaf 101000002) (BTree.leaf 101000003))) (BTree.node (BTree.node (BTree.leaf 12100) (BTree.leaf 12101)) (BTree.node (BTree.leaf 12102) (BTree.leaf 12103)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 10000200) (BTree.leaf 10000201)) (BTree.node (BTree.leaf 101000010) (BTree.leaf 101000011))) (BTree.node (BTree.node (BTree.leaf 1100001100) (BTree.leaf 1100001101)) (BTree.node (BTree.leaf 12110) (BTree.leaf 12111))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 1001010000) (BTree.leaf 1001010001)) (BTree.node (BTree.leaf 10000210) (BTree.leaf 10000211))) (BTree.node (BTree.node (BTree.leaf 101000020) (BTree.leaf 101000021)) (BTree.node (BTree.leaf 1100001110) (BTree.leaf 1100001111)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 1031000) (BTree.leaf 1031001)) (BTree.node (BTree.leaf 1001010010) (BTree.leaf 1001010011))) (BTree.node (BTree.node (BTree.leaf 11100) (BTree.leaf 11101)) (BTree.node (BTree.leaf 11102) (BTree.leaf 11103)))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 11100000) (BTree.leaf 11100001)) (BTree.node (BTree.leaf 11100002) (BTree.leaf 11100003))) (BTree.node (BTree.node (BTree.leaf 1100000100) (BTree.leaf 1100000101)) (BTree.node (BTree.leaf 11110) (BTree.leaf 11111)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 100200) (BTree.leaf 100201)) (BTree.node (BTree.leaf 11100010) (BTree.leaf 11100011))) (BTree.node (BTree.node (BTree.leaf 1000300) (BTree.leaf 1000301)) (BTree.node (BTree.leaf 1100000110) (BTree.leaf 1100000111))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 1030000) (BTree.leaf 1030001)) (BTree.node (BTree.leaf 100210) (BTree.leaf 100211))) (BTree.node (BTree.node (BTree.leaf 10100) (BTree.leaf 10101)) (BTree.node (BTree.leaf 10102) (BTree.leaf 10103)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 2011000) (BTree.leaf 2011001)) (BTree.node (BTree.leaf 1030010) (BTree.leaf 1030011))) (BTree.node (BTree.node (BTree.leaf 100220) (BTree.leaf 100221)) (BTree.node (BTree.leaf 10110) (BTree.leaf 10111)))))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 110000000) (BTree.leaf 110000001)) (BTree.node (BTree.leaf 110000002) (BTree.leaf 110000003))) (BTree.node (BTree.node (BTree.leaf 2100100) (BTree.leaf 2100101)) (BTree.node (BTree.leaf 100230) (BTree.leaf 100231)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 100101000) (BTree.leaf 100101001)) (BTree.node (BTree.leaf 110000010) (BTree.leaf 110000011))) (BTree.node (BTree.node (BTree.leaf 101001100) (BTree.leaf 101001101)) (BTree.node (BTree.leaf 2100110) (BTree.leaf 2100111))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 2010000) (BTree.leaf 2010001)) (BTree.node (BTree.leaf 100101010) (BTree.leaf 100101011))) (BTree.node (BTree.node (BTree.leaf 110000020) (BTree.leaf 110000021)) (BTree.node (BTree.leaf 101001110) (BTree.leaf 101001111)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 1000111000) (BTree.leaf 1000111001)) (BTree.node (BTree.leaf 2010010) (BTree.leaf 2010011))) (BTree.node (BTree.node (BTree.leaf 100101020) (BTree.leaf 100101021)) (BTree.node (BTree.leaf 110000030) (BTree.leaf 110000031)))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 100100000) (BTree.leaf 100100001)) (BTree.node (BTree.leaf 100100002) (BTree.leaf 100100003))) (BTree.node (BTree.node (BTree.leaf 101000100) (BTree.leaf 101000101)) (BTree.node (BTree.leaf 101000102) (BTree.leaf 101000103)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 10201000) (BTree.leaf 10201001)) (BTree.node (BTree.leaf 100100010) (BTree.leaf 100100011))) (BTree.node (BTree.node (BTree.leaf 10000300) (BTree.leaf 10000301)) (BTree.node (BTree.leaf 101000110) (BTree.leaf 101000111))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 1000110000) (BTree.leaf 1000110001)) (BTree.node (BTree.leaf 10201010) (BTree.leaf 10201011))) (BTree.node (BTree.node (BTree.leaf 100100020) (BTree.leaf 100100021)) (BTree.node (BTree.leaf 10000310) (BTree.leaf 10000311)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 3000) (BTree.leaf 3001)) (BTree.node (BTree.leaf 1000110010) (BTree.leaf 1000110011))) (BTree.node (BTree.node (BTree.leaf 1031100) (BTree.leaf 1031101)) (BTree.node (BTree.leaf 100100030) (BTree.leaf 100100031))))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 10200000) (BTree.leaf 10200001)) (BTree.node (BTree.leaf 3010) (BTree.leaf 3011))) (BTree.node (BTree.node (BTree.leaf 11100100) (BTree.leaf 11100101)) (BTree.node (BTree.leaf 11100102) (BTree.leaf 11100103)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 301000) (BTree.leaf 301001)) (BTree.node (BTree.leaf 10200010) (BTree.leaf 10200011))) (BTree.node (BTree.node (BTree.leaf 100300) (BTree.leaf 100301)) (BTree.node (BTree.leaf 11100110) (BTree.leaf 11100111))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 2000) (BTree.leaf 2001)) (BTree.node (BTree.leaf 2002) (BTree.leaf 2003))) (BTree.node (BTree.node (BTree.leaf 1030100) (BTree.leaf 1030101)) (BTree.node (BTree.leaf 100310) (BTree.leaf 100311)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 10200) (BTree.leaf 10201)) (BTree.node (BTree.leaf 2010) (BTree.leaf 2011))) (BTree.node (BTree.node (BTree.leaf 2012) (BTree.leaf 2013)) (BTree.node (BTree.leaf 1030110) (BTree.leaf 1030111)))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 300000) (BTree.leaf 300001)) (BTree.node (BTree.leaf 10210) (BTree.leaf 10211))) (BTree.node (BTree.node (BTree.leaf 110000100) (BTree.leaf 110000101)) (BTree.node (BTree.leaf 110000102) (BTree.leaf 110000103)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 1000) (BTree.leaf 1001)) (BTree.node (BTree.leaf 1002) (BTree.leaf 1003))) (BTree.node (BTree.node (BTree.leaf 100101100) (BTree.leaf 100101101)) (BTree.node (BTree.leaf 110000110) (BTree.leaf 110000111))))) (BTree.node (BTree.node (BTree.node (BTree.node (BTree.leaf 1110000) (BTree.leaf 1110001)) (BTree.node (BTree.leaf 1010) (BTree.leaf 1011))) (BTree.node (BTree.node (BTree.leaf 1012) (BTree.leaf 1013)) (BTree.node (BTree.leaf 100101110) (BTree.leaf 100101111)))) (BTree.node (BTree.node (BTree.node (BTree.leaf 100011000) (BTree.leaf 100011001)) (BTree.node (BTree.leaf 1110010) (BTree.leaf 1110011))) (BTree.node (BTree.node (BTree.leaf 1020) (BTree.leaf 1021)) (BTree.node (BTree.leaf 1022) (BTree.leaf 1023))))))))))

def forallPow2 (P : Nat → Bool) : Nat → Nat → Bool
  | 0, base => P base
  | d + 1, base => forallPow2 P d base && forallPow2 P d (base + 2 ^ d)

theorem forallPow2_sound {P : Nat → Bool} :
    ∀ d base : Nat, forallPow2 P d base = true → ∀ i, i < 2 ^ d → P (base + i) = true := by
  intro d; induction d with
  | zero =>
    intro base h i hi
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0; simpa [forallPow2] using h
  | succ d ih =>
    intro base h i hi
    simp only [forallPow2, Bool.and_eq_true] at h
    by_cases hlt : i < 2 ^ d
    · exact ih base h.1 i hlt
    · have hi2 : i - 2 ^ d < 2 ^ d := by rw [Nat.pow_succ] at hi; omega
      have hres := ih (base + 2 ^ d) h.2 (i - 2 ^ d) hi2
      have heq : base + 2 ^ d + (i - 2 ^ d) = base + i := by omega
      rw [heq] at hres; exact hres

def checkCoverStep (r : Nat) : Bool :=
  let w := BTree.get 10 coverTree1024 r
  decide (w < 10 ^ 10) && decide (w % 1024 = r) && decide (digitSumFuel 10 w ≤ 7)

theorem cover1024_ok : forallPow2 checkCoverStep 10 0 = true := by decide

theorem cover1024_spec (r : Nat) (hr : r < 1024) :
    BTree.get 10 coverTree1024 r % 1024 = r ∧ digitSum (BTree.get 10 coverTree1024 r) ≤ 7 := by
  have h1 := forallPow2_sound 10 0 cover1024_ok r hr
  simp only [Nat.zero_add, checkCoverStep, Bool.and_eq_true] at h1
  have hlt := of_decide_eq_true h1.1.1
  have hmod := of_decide_eq_true h1.1.2
  have hds := of_decide_eq_true h1.2
  rw [digitSumFuel_eq_of_lt 10 _ hlt] at hds
  exact ⟨hmod, hds⟩

def oddInv1024 (a : Nat) : Nat :=
  let x0 := a % 1024
  let x1 := (x0 * (2 + 1024 - (a * x0) % 1024)) % 1024
  let x2 := (x1 * (2 + 1024 - (a * x1) % 1024)) % 1024
  let x3 := (x2 * (2 + 1024 - (a * x2) % 1024)) % 1024
  (x3 * (2 + 1024 - (a * x3) % 1024)) % 1024

def checkOddInvStep (k : Nat) : Bool :=
  let a := 2 * k + 1
  decide ((a * oddInv1024 a) % 1024 = 1)

theorem oddInv1024_ok : forallPow2 checkOddInvStep 9 0 = true := by decide

theorem oddInv1024_spec {a : Nat} (hodd : a % 2 = 1) : (a * oddInv1024 (a % 1024)) % 1024 = 1 := by
  have h1 := forallPow2_sound 9 0 oddInv1024_ok ((a % 1024) / 2) (by omega)
  simp only [Nat.zero_add, checkOddInvStep] at h1
  have hval : 2 * ((a % 1024) / 2) + 1 = a % 1024 := by omega
  rw [hval] at h1
  have hmod := of_decide_eq_true h1
  rw [Nat.mul_mod]; simpa [Nat.mul_mod] using hmod

theorem pow5_odd (k : Nat) : (5 ^ k) % 2 = 1 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.pow_succ, Nat.mul_mod, ih]

theorem pow10_split (k : Nat) : 10 ^ k = 2 ^ k * 5 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, ih]
    have h10 : (10 : Nat) = 2 * 5 := by decide
    rw [h10, ← Nat.mul_assoc, Nat.mul_assoc (2 ^ k) (5 ^ k) 2, Nat.mul_comm (5 ^ k) 2,
        ← Nat.mul_assoc, Nat.mul_assoc]

theorem exists_two_adic_block :
    ∀ k : Nat, ∃ N : Nat, 2 ^ (10 * k + 1) ∣ N ∧ N % 10 = 2 ∧ digitSum N ≤ 7 * k + 2 := by
  intro k
  induction k with
  | zero =>
    refine ⟨2, by decide, by decide, ?_⟩
    rw [digitSum_lt_ten (by decide)]; decide
  | succ k ih =>
    obtain ⟨N, h2k, hmod10, hds⟩ := ih
    obtain ⟨q, hq⟩ := h2k
    let e := 10 * k + 1
    let inv := oddInv1024 ((5 ^ e) % 1024)
    let r := ((1024 - q % 1024) * inv) % 1024
    have hr : r < 1024 := Nat.mod_lt _ (by decide)
    obtain ⟨w, hw_mod, hw_ds⟩ : ∃ w, w % 1024 = r ∧ digitSum w ≤ 7 := ⟨_, cover1024_spec r hr⟩
    refine ⟨N + w * 10 ^ e, ?_, ?_, ?_⟩
    · have hfactor : N + w * 10 ^ e = 2 ^ e * (q + w * 5 ^ e) := by
        rw [hq, pow10_split e, Nat.mul_left_comm w (2 ^ e) (5 ^ e), Nat.mul_add]
      rw [hfactor]
      have hpow : 2 ^ (10 * (k + 1) + 1) = 2 ^ e * 1024 := by
        have he : 10 * (k + 1) + 1 = e + 10 := by omega
        rw [he, Nat.pow_add]
      rw [hpow]
      refine Nat.mul_dvd_mul_left _ (Nat.dvd_of_mod_eq_zero ?_)
      have hinv := oddInv1024_spec (pow5_odd e)
      have h1 : (w * 5 ^ e) % 1024 = (1024 - q % 1024) % 1024 := by
        rw [Nat.mul_mod, hw_mod]
        change ((((1024 - q % 1024) * inv) % 1024) * (5 ^ e % 1024)) % 1024 = (1024 - q % 1024) % 1024
        rw [← Nat.mul_mod, Nat.mul_assoc, Nat.mul_comm inv (5 ^ e)]
        rw [Nat.mul_mod (1024 - q % 1024), hinv, Nat.mul_one, Nat.mod_mod]
      rw [Nat.add_mod, h1]
      have hqlt : q % 1024 < 1024 := Nat.mod_lt q (by decide)
      omega
    · have h10e : 10 ∣ 10 ^ e := by
        have he : e = 10 * k + 1 := rfl
        rw [he, Nat.pow_succ]; exact Nat.dvd_mul_left 10 _
      have h10w : (w * 10 ^ e) % 10 = 0 := Nat.mod_eq_zero_of_dvd (Nat.dvd_trans h10e (Nat.dvd_mul_left _ _))
      rw [Nat.add_mod, hmod10, h10w]
    · have h1 := digitSum_add_le N (w * 10 ^ e)
      rw [digitSum_mul_pow10] at h1
      omega

/-! ### Part 3: Universal Multi-Modulus Local No-Go Theorem -/

/-- **HEADLINE 1 — Universal Multi-Modulus Local No-Go Theorem**:
    For EVERY modulus `M ≥ 1` coprime to `10` and EVERY `t ≥ 1`, there exists `N ≥ 1` with:
      `M * 2^t ∣ N`, `¬ (5 ∣ N)`, and `10 * s(N) ≤ 7 * t + 10 * s(c) + 83` (with `c < M`).
    In particular `10 * s(N) ≤ 7 * t + 10 * M + 83`! -/
theorem universal_local_modular_nogo {M t : Nat} (hM : M ≥ 1) (hcop10 : Nat.gcd 10 M = 1) (ht : t ≥ 1) :
    ∃ N c : Nat, c < M ∧ N ≥ 1 ∧ M * 2 ^ t ∣ N ∧ ¬ (5 ∣ N) ∧
      10 * digitSum N ≤ 7 * t + 10 * digitSum c + 83 := by
  let k := (t + 8) / 10
  have htk : t ≤ 10 * k + 1 := by omega
  obtain ⟨N0, h2k, hmod10, hds0⟩ := exists_two_adic_block k
  have h2t_N0 : 2 ^ t ∣ N0 := Nat.dvd_trans (Nat.pow_dvd_pow 2 htk) h2k
  -- Choose `c < M` such that `N0 + c * 10^t ≡ 0 (mod M)`!
  have hcop_pow10 : Nat.gcd (10 ^ t) M = 1 := gcd_pow_eq_one hcop10 t
  let target := (M - N0 % M) % M
  have htarget_lt : target < M := Nat.mod_lt _ (by omega)
  obtain ⟨c, hc_lt, hc_mod⟩ := exists_mul_mod_eq hM hcop_pow10 htarget_lt
  let N := N0 + c * 10 ^ t
  refine ⟨N, c, hc_lt, ?_, ?_, ?_, ?_⟩
  · -- `N ≥ 1` since `N0 % 10 = 2`
    omega
  · -- `M * 2^t ∣ N`: both `M ∣ N` and `2^t ∣ N`, and `gcd(2^t, M) = 1`!
    have hM_dvd : M ∣ N := by
      refine Nat.dvd_of_mod_eq_zero ?_
      change (N0 + c * 10 ^ t) % M = 0
      rw [Nat.add_mod, hc_mod]
      dsimp only [target]
      have hlt : N0 % M < M := Nat.mod_lt N0 (by omega)
      by_cases h0 : N0 % M = 0
      · rw [h0]; simp
      · have hsub : (M - N0 % M) % M = M - N0 % M := Nat.mod_eq_of_lt (by omega)
        rw [hsub]; have : N0 % M + (M - N0 % M) = M := by omega
        rw [this, Nat.mod_self]
    have h2t_dvd : 2 ^ t ∣ N := by
      have h2t_10t : 2 ^ t ∣ 10 ^ t := by rw [pow10_split t]; exact Nat.dvd_mul_right _ _
      exact Nat.dvd_add h2t_N0 (Nat.dvd_trans h2t_10t (Nat.dvd_mul_left _ _))
    have hcop2 : Nat.gcd 2 M = 1 := by
      have hd : Nat.gcd 2 M ∣ Nat.gcd 10 M :=
        Nat.dvd_gcd (Nat.dvd_trans (Nat.gcd_dvd_left 2 M) (by decide : 2 ∣ 10)) (Nat.gcd_dvd_right 2 M)
      rw [hcop10] at hd
      exact Nat.le_antisymm (Nat.le_of_dvd (by decide) hd) (Nat.gcd_pos_of_pos_left M (by decide))
    exact mul_dvd_of_gcd_one (gcd_pow_eq_one hcop2 t) hM_dvd h2t_dvd
  · -- `¬ (5 ∣ N)` since `N % 10 = 2`!
    have h10t : 10 ∣ 10 ^ t := by
      cases t with | zero => omega | succ t' => rw [Nat.pow_succ]; exact Nat.dvd_mul_left 10 _
    have hc10 : (c * 10 ^ t) % 10 = 0 := Nat.mod_eq_zero_of_dvd (Nat.dvd_trans h10t (Nat.dvd_mul_left _ _))
    have hN10 : N % 10 = 2 := by change (N0 + c * 10 ^ t) % 10 = 2; rw [Nat.add_mod, hmod10, hc10]
    intro h5
    have := Nat.mod_eq_zero_of_dvd h5; omega
  · -- `10 * digitSum N ≤ 7 * t + 10 * digitSum c + 83`
    have hadd := digitSum_add_le N0 (c * 10 ^ t)
    rw [digitSum_mul_pow10] at hadd
    have hk_bound : 10 * k ≤ t + 8 := by omega
    dsimp only [N]; omega

/-- Bound `s(c) ≤ 10` for all `c < 27` (max at `c = 19`). -/
theorem digitSum_lt_27_le_10 {c : Nat} (hc : c < 27) : digitSum c ≤ 10 := by
  have hcheck : (List.range 27).all (fun x => decide (digitSumFuel 2 x ≤ 10)) = true := by decide
  have h1 := List.all_eq_true.mp hcheck c (List.mem_range.mpr hc)
  have hfuel : digitSumFuel 2 c ≤ 10 := of_decide_eq_true h1
  rw [digitSumFuel_eq_of_lt 2 c (by omega)] at hfuel
  exact hfuel

/-- **HEADLINE 2 — Simultaneous 2-Adic + 3-Adic (`27 * 2^t ∣ N, 5 ∤ N`) No-Go Theorem**:
    For EVERY `t ≥ 1`, there exists `N ≥ 1` with `27 * 2^t ∣ N`, `5 ∤ N`, and
    `10 * digitSum N ≤ 7 * t + 183`. Hence for ALL `t ≥ 62`, `digitSum N < t`! -/
theorem trap27_local_2adic_3adic_nogo {t : Nat} (ht : t ≥ 1) :
    ∃ N : Nat, N ≥ 1 ∧ 27 * 2 ^ t ∣ N ∧ ¬ (5 ∣ N) ∧ 10 * digitSum N ≤ 7 * t + 183 := by
  obtain ⟨N, c, hc, hpos, hdvd, h5, hds⟩ :=
    universal_local_modular_nogo (M := 27) (t := t) (by decide) (by decide) ht
  have hc10 := digitSum_lt_27_le_10 hc
  exact ⟨N, hpos, hdvd, h5, by omega⟩

theorem trap27_local_insufficient_ge_62 {t : Nat} (ht : t ≥ 62) :
    ∃ N : Nat, N ≥ 1 ∧ 27 * 2 ^ t ∣ N ∧ ¬ (5 ∣ N) ∧ digitSum N < t := by
  obtain ⟨N, hpos, hdvd, h5, hds⟩ := trap27_local_2adic_3adic_nogo (t := t) (by omega)
  exact ⟨N, hpos, hdvd, h5, by omega⟩

#print axioms exists_mul_mod_eq
#print axioms universal_local_modular_nogo
#print axioms trap27_local_2adic_3adic_nogo
#print axioms trap27_local_insufficient_ge_62

end Ch2UniversalLocalNoGo
