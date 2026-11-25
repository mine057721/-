import Mathlib

/-!
# 자릿수 합 계승 수열과 소인수 지수 추측

  a₁ = n,  a_{k+1} = a_k + gcd(a_k, s(a_k)!),  d_k = gcd(a_k, s(a_k)!)

추측: 모든 n ≥ 1, 모든 소수 p 에 대해 limsup_{k→∞} v_p(d_k) = ∞.

주의: 이 파일은 인덱스를 0부터 센다. 즉 `a n 0 = n` 이고,
문제의 a_k 는 `a n (k-1)` 에 해당한다.

Lean 4.37.0-rc1 + Mathlib master (2026-11) 에서 `sorry` 없이 컴파일됨.
`a_one_fifty` 만 `native_decide` (컴파일러 신뢰) 를 쓴다.
-/

open Nat

/-- 십진법 자릿수 합 s(m). -/
def s (m : ℕ) : ℕ := (Nat.digits 10 m).sum

/-- 한 단계: x ↦ x + gcd(x, s(x)!). -/
def step (x : ℕ) : ℕ := x + Nat.gcd x (s x)!

/-- 수열 a_k (0부터 셈): a n 0 = n, a n (k+1) = step (a n k). -/
def a (n k : ℕ) : ℕ := step^[k] n

/-- 증가량 d_k = gcd(a_k, s(a_k)!). -/
def d (n k : ℕ) : ℕ := Nat.gcd (a n k) (s (a n k))!

/-! ## 1. 원래 추측 -/

/-- limsup_{k→∞} v_p(d_k) = ∞ 를 "모든 B, 모든 K 에 대해 k ≥ K 이면서
v_p(d_k) > B 인 k 가 있다" 로 쓴 것. -/
def Conjecture : Prop :=
  ∀ n : ℕ, 0 < n → ∀ p : ℕ, p.Prime →
    ∀ B K : ℕ, ∃ k ≥ K, B < padicValNat p (d n k)

/-! ## 2. 2배 모드 -/

/-- 보조정리 1: x ∣ s(x)! 이면 다음 항은 정확히 2x 이다. -/
theorem step_of_dvd {x : ℕ} (h : x ∣ (s x)!) : step x = 2 * x := by
  unfold step
  rw [Nat.gcd_eq_left h]
  ring

/-- 보조정리 1': x ∣ s(x)! 이면 증가량은 x 자신이다. -/
theorem gcd_of_dvd {x : ℕ} (h : x ∣ (s x)!) : Nat.gcd x (s x)! = x :=
  Nat.gcd_eq_left h

/-! ## 3. n = 1 의 구체적 계산 -/

/-- 직접 계산: a_50 = 3315 · 2^35 (0부터 센 인덱스). 3315 = 3·5·13·17.
유한한 계산이라 `native_decide` 로 확인할 수 있다 (컴파일러를 신뢰하는 방식). -/
theorem a_one_fifty : a 1 50 = 3315 * 2 ^ 35 := by
  native_decide

/-! ## 4. 조건 (C) -/

/-- 조건 (C): 모든 m ≥ 35 에 대해 S = s(3315·2^m) 이 S − ν₂(S) ≥ m 을 만족한다.
여기서 ν₂(S) 는 S 의 2진 자릿수 합(1의 개수)이다.
자연수 뺄셈을 피하려고 m + ν₂(S) ≤ S 로 썼다.
(르장드르 공식: v₂(S!) = S − ν₂(S).) -/
def CondC : Prop :=
  ∀ m ≥ 35, m + (Nat.digits 2 (s (3315 * 2 ^ m))).sum ≤ s (3315 * 2 ^ m)

/-- 보조정리 2: (C) 이면 3315·2^m ∣ s(3315·2^m)! (m ≥ 35).
증명 개요:
* 르장드르 공식(`sub_one_mul_padicValNat_factorial`)으로 v₂(S!) = S − ν₂(S) ≥ m,
  따라서 2^m ∣ S!.
* (C) 에서 S ≥ m ≥ 35 ≥ 17 이고 3315 ∣ 17! ∣ S!.
* gcd(3315, 2^m) = 1 이므로 곱도 나눈다. -/
theorem dvd_of_condC (hC : CondC) {m : ℕ} (hm : 35 ≤ m) :
    3315 * 2 ^ m ∣ (s (3315 * 2 ^ m))! := by
  set S := s (3315 * 2 ^ m) with hS
  have hc := hC m hm
  rw [← hS] at hc
  -- 2^m ∣ S!
  have hleg := Nat.Prime.sub_one_mul_multiplicity_factorial (n := S) Nat.prime_two
  have h2 : 2 ^ m ∣ S ! := by
    have hv : m ≤ multiplicity 2 S ! := by
      have : multiplicity 2 S ! = S - (Nat.digits 2 S).sum := by simpa using hleg
      omega
    exact (Nat.pow_dvd_pow 2 hv).trans (pow_multiplicity_dvd _ _)
  -- 3315 ∣ S!
  have h3 : 3315 ∣ S ! :=
    (show 3315 ∣ Nat.factorial 17 by decide).trans (Nat.factorial_dvd_factorial (by omega))
  have hcop : Nat.Coprime 3315 (2 ^ m) :=
    Nat.Coprime.pow_right _ (by norm_num)
  exact hcop.mul_dvd_of_dvd_of_dvd h3 h2

/-- 정리 (조건부 반례): (C) 가 참이면 모든 j 에 대해 a_{50+j} = 3315 · 2^{35+j}. -/
theorem a_one_doubling (hC : CondC) (j : ℕ) :
    a 1 (50 + j) = 3315 * 2 ^ (35 + j) := by
  induction j with
  | zero => exact a_one_fifty
  | succ j ih =>
    have h : a 1 (50 + (j + 1)) = step (a 1 (50 + j)) := by
      simp only [a, ← Nat.add_assoc, Function.iterate_succ_apply']
    rw [h, ih, step_of_dvd (dvd_of_condC hC (by omega))]
    ring

/-- 정리: (C) 가 참이면 k ≥ 50 에서 v₇(d_k) = 0. -/
theorem v7_zero_of_condC (hC : CondC) {k : ℕ} (hk : 50 ≤ k) :
    padicValNat 7 (d 1 k) = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  have ha := a_one_doubling hC j
  have hd : d 1 (50 + j) = 3315 * 2 ^ (35 + j) := by
    unfold d
    rw [ha, gcd_of_dvd (dvd_of_condC hC (by omega))]
  rw [hd, padicValNat_def]
  apply multiplicity_eq_zero_of_not_dvd
  intro h7
  rcases (Nat.Prime.dvd_mul (by norm_num : (7 : ℕ).Prime)).1 h7 with h | h
  · norm_num at h
  · have := (Nat.Prime.dvd_of_dvd_pow (by norm_num : (7 : ℕ).Prime) h)
    norm_num at this

/-- 따름정리: (C) 가 참이면 원래 추측은 거짓이다 (반례: n = 1, p = 7). -/
theorem not_conjecture_of_condC (hC : CondC) : ¬ Conjecture := by
  intro h
  obtain ⟨k, hk, hB⟩ := h 1 one_pos 7 (by norm_num) 0 50
  rw [v7_zero_of_condC hC hk] at hB
  exact lt_irrefl 0 hB

/-! ## 5. 가장 근본적인 요건 (R) -/

/-- (R): s(u·2^m) 이 m 보다 선형적으로 크다.
u = 3315 에 대해 (R) 이 성립하면, 남는 유한 구간을 계산으로 확인해서 (C) 를 얻는다.
현재 알려진 최선의 하한은 대략 log m / log log m 수준이다 (Stewart, 1980). -/
def R (u : ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ M : ℕ, ∀ m ≥ M, (1 + ε) * (m : ℝ) ≤ (s (u * 2 ^ m) : ℝ)

/-- 추측이 참이기 위한 필요조건: n = 1 에서 2배 모드가 무한히 자주 깨져야 한다. -/
theorem conjecture_needs_breaks (h : Conjecture) :
    ∀ K : ℕ, ∃ k ≥ K, ¬ (a 1 k ∣ (s (a 1 k))!) := by
  intro K
  by_contra hne
  push Not at hne
  -- 이후 모든 단계가 2배 모드: a 1 (K + j) = 2^j * a 1 K
  have hsucc : ∀ k, a 1 (k + 1) = step (a 1 k) := fun k => by
    simp only [a, Function.iterate_succ_apply']
  have hpos : ∀ k, 0 < a 1 k := by
    intro k
    induction k with
    | zero => simp [a]
    | succ k ih => rw [hsucc]; unfold step; omega
  have hdbl : ∀ j, a 1 (K + j) = 2 ^ j * a 1 K := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [← Nat.add_assoc, hsucc, step_of_dvd (hne (K + j) (by omega)), ih]
      ring
  -- a 1 K 보다 큰 소수 p 를 고른다: p ≠ 2 이고 p ∤ a 1 K.
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (a 1 K + 3)
  obtain ⟨k, hk, hB⟩ := h 1 one_pos p hp 0 K
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hd : d 1 (K + j) = 2 ^ j * a 1 K := by
    unfold d
    rw [gcd_of_dvd (hne _ hk), hdbl]
  rw [hd, padicValNat_def, multiplicity_eq_zero_of_not_dvd] at hB
  · exact lt_irrefl 0 hB
  intro hdvd
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with h2 | ha
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2)
    omega
  · have := Nat.le_of_dvd (hpos K) ha
    omega
