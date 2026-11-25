import Mathlib

/-!
# 자릿수 합 계승 수열과 소인수 지수 추측

  a₁ = n,  a_{k+1} = a_k + gcd(a_k, s(a_k)!),  d_k = gcd(a_k, s(a_k)!)

추측: 모든 n ≥ 1, 모든 소수 p 에 대해 limsup_{k→∞} v_p(d_k) = ∞.

주의: 이 파일은 인덱스를 0부터 센다. 즉 `a n 0 = n` 이고,
문제의 a_k 는 `a n (k-1)` 에 해당한다.

Lean 4.37.0-rc1 + Mathlib master (2026-11) 에서 `sorry` 없이 컴파일됨.
`a_one_fifty` 만 `native_decide` (컴파일러 신뢰) 를 쓴다.

## 결과 요약
* `conjecture_two` (무조건): 모든 n ≥ 1 에서 limsup v₂(d_k) = ∞. 즉 추측은 p = 2 에서 참.
* `not_conjecture_of_condC`: 조건 (C) 이면 n = 1, p = 7 이 반례.
* `not_conjecture_of_absorbed`: 더 약한 "홀수 부분 흡수" 가정으로도 반례 (p ∤ 2^j+1 인 p).
* `conjecture_needs_entries` (무조건): 추측이 참이면 모든 n, p 에 대해
  p ∣ a_k/d_k + 1 이 무한히 자주 일어나야 한다.
* `conjecture_of_entries` (무조건, 일반 p 판정법): G 단계마다 "p 진입(p ∣ a_k/d_k + 1)"
  또는 "v_p(s_k!) < v_p(a_k)" 가 있으면 limsup v_p(d_k) = ∞. `conjecture_two` 는 G = 1 인 경우.
* `digit_sum_unbounded` (무조건): 모든 n 에서 limsup s(a_k) = ∞.
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

/-! ## 6. 약한 가정: "홀수 부분 흡수"

2배 모드가 깨져도 상관없다. x = u·2^m 이고 u ∣ s(x)! 이기만 하면
gcd(x, s(x)!) 의 여인수는 2의 거듭제곱 2^j 이고, 다음 항은 x·(2^j+1)/2^j 이다.
그러면 2^j + 1 을 나누지 않는 소수 p (예: 7) 의 지수는 절대 변하지 않는다. -/

/-- x 의 "홀수 부분" (정확히는 x 를 2의 거듭제곱으로 나눈 어떤 몫) 이 s(x)! 을 나눈다. -/
def Absorbed (x : ℕ) : Prop := ∃ u m : ℕ, x = u * 2 ^ m ∧ u ∣ (s x)!

/-- 2배 모드는 흡수의 특수한 경우 (u = x, m = 0). -/
theorem absorbed_of_dvd {x : ℕ} (h : x ∣ (s x)!) : Absorbed x :=
  ⟨x, 0, by simp, h⟩

/-- 핵심 보조정리: 흡수 상태에서 step x · 2^j = x · (2^j + 1) 인 j 가 있다. -/
theorem step_of_absorbed {x : ℕ} (hA : Absorbed x) (hx : 0 < x) :
    ∃ j, step x * 2 ^ j = x * (2 ^ j + 1) := by
  obtain ⟨u, m, rfl, hu⟩ := hA
  set g := Nat.gcd (u * 2 ^ m) (s (u * 2 ^ m))! with hg
  have hug : u ∣ g := Nat.dvd_gcd (Dvd.intro _ rfl) hu
  have hgx : g ∣ u * 2 ^ m := Nat.gcd_dvd_left _ _
  obtain ⟨q, hq⟩ := hgx
  obtain ⟨r, hr⟩ := hug
  have hu0 : 0 < u := Nat.pos_of_mul_pos_right hx
  have hrq : r * q = 2 ^ m := by
    have : u * (r * q) = u * 2 ^ m := by rw [← mul_assoc, ← hr, ← hq]
    exact Nat.eq_of_mul_eq_mul_left hu0 this
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro_left r hrq)
  refine ⟨j, ?_⟩
  have hstep : step (u * 2 ^ m) = g * (2 ^ j + 1) := by
    unfold step
    rw [← hg, hq, hj]
    ring
  rw [hstep, hq, hj]
  ring

/-- 7 은 어떤 2^j + 1 도 나누지 않는다 (2^j mod 7 ∈ {1, 2, 4}). -/
theorem seven_not_dvd_two_pow_add_one (j : ℕ) : ¬ 7 ∣ 2 ^ j + 1 := by
  intro h
  have hj : 2 ^ j = 8 ^ (j / 3) * 2 ^ (j % 3) := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul, ← pow_add, Nat.div_add_mod]
  have h8 : 8 ^ (j / 3) % 7 = 1 := by rw [Nat.pow_mod]; simp
  have hmod := Nat.mod_eq_zero_of_dvd h
  rw [hj, Nat.add_mod, Nat.mul_mod, h8] at hmod
  have hr : j % 3 < 3 := Nat.mod_lt _ (by norm_num)
  generalize j % 3 = r at hmod hr
  interval_cases r <;> simp at hmod

/-- 흡수 상태에서 한 단계를 가도 p-지수는 그대로다 (p ∤ 2^j+1 인 소수 p). -/
theorem multiplicity_step_of_absorbed {p x : ℕ} (hp : p.Prime)
    (h2 : ∀ j, ¬ p ∣ 2 ^ j + 1) (hA : Absorbed x) (hx : 0 < x) :
    multiplicity p (step x) = multiplicity p x := by
  have := Fact.mk hp
  obtain ⟨j, hj⟩ := step_of_absorbed hA hx
  have hs : step x ≠ 0 := by unfold step; omega
  have hp2 : ¬ p ∣ 2 ^ j := fun h => h2 0 (by simpa using hp.dvd_of_dvd_pow h)
  have := congrArg (multiplicity p) hj
  rwa [Nat.multiplicity_mul hs (by positivity), Nat.multiplicity_mul hx.ne' (Nat.add_one_ne_zero _),
    multiplicity_eq_zero_of_not_dvd hp2, multiplicity_eq_zero_of_not_dvd (h2 j),
    Nat.add_zero, Nat.add_zero] at this

theorem a_succ (n k : ℕ) : a n (k + 1) = step (a n k) := by
  simp only [a, Function.iterate_succ_apply']

theorem a_pos {n : ℕ} (hn : 0 < n) (k : ℕ) : 0 < a n k := by
  induction k with
  | zero => simpa [a] using hn
  | succ k ih => rw [a_succ]; unfold step; omega

/-- 정리 (약한 가정의 조건부 반례): 어떤 n 과 K 에 대해 k ≥ K 인 모든 a_k 가 흡수 상태이면
원래 추측은 거짓이다. p ∤ 2^j + 1 (모든 j) 인 소수 p 가 반례가 된다. -/
theorem not_conjecture_of_absorbed {n p K : ℕ} (hn : 0 < n) (hp : p.Prime)
    (h2 : ∀ j, ¬ p ∣ 2 ^ j + 1) (hA : ∀ k ≥ K, Absorbed (a n k)) : ¬ Conjecture := by
  have := Fact.mk hp
  intro hC
  have hconst : ∀ j, multiplicity p (a n (K + j)) = multiplicity p (a n K) := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [← Nat.add_assoc, a_succ,
        multiplicity_step_of_absorbed hp h2 (hA _ (by omega)) (a_pos hn _), ih]
  obtain ⟨k, hk, hB⟩ := hC n hn p hp (multiplicity p (a n K)) K
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hle : multiplicity p (d n (K + j)) ≤ multiplicity p (a n (K + j)) :=
    (multiplicity_dvd_iff_le (a_pos hn _).ne').1
      ((pow_multiplicity_dvd _ _).trans (Nat.gcd_dvd_left _ _))
  rw [padicValNat_def] at hB
  have := hconst j
  omega

/-- 따름정리: 추측이 참이라면, 모든 n 에서 흡수가 무한히 자주 깨져야 한다.
(`conjecture_needs_breaks` 보다 강하다: 2-지수 쪽 깨짐만으로는 부족하다.) -/
theorem conjecture_needs_absorption_breaks (h : Conjecture) {n : ℕ} (hn : 0 < n) :
    ∀ K : ℕ, ∃ k ≥ K, ¬ Absorbed (a n k) := by
  intro K
  by_contra hne
  push Not at hne
  exact not_conjecture_of_absorbed hn (by norm_num) seven_not_dvd_two_pow_add_one hne h

/-! ## 7. 정확한 메커니즘: p 가 들어오는 통로는 q_k + 1 뿐

q_k = a_k / d_k 라 하면 a_{k+1} = d_k · (q_k + 1) 이므로
v_p(a_{k+1}) = v_p(d_k) + v_p(q_k + 1) ≤ v_p(a_k) + v_p(q_k + 1).
즉 p ∤ q_k + 1 이면 p-지수는 늘지 않는다. -/

theorem d_dvd_a (n k : ℕ) : d n k ∣ a n k := Nat.gcd_dvd_left _ _

theorem a_succ_eq (n k : ℕ) : a n (k + 1) = d n k * (a n k / d n k + 1) := by
  have h1 : a n (k + 1) = a n k + d n k := by rw [a_succ]; rfl
  rw [h1, Nat.mul_add, Nat.mul_div_cancel' (d_dvd_a n k), Nat.mul_one]

/-- p ∤ q_k + 1 이면 v_p(a_{k+1}) ≤ v_p(a_k). -/
theorem multiplicity_succ_le {n p k : ℕ} (hn : 0 < n) (hp : p.Prime)
    (h : ¬ p ∣ a n k / d n k + 1) :
    multiplicity p (a n (k + 1)) ≤ multiplicity p (a n k) := by
  have := Fact.mk hp
  have ha0 : a n k ≠ 0 := (a_pos hn k).ne'
  have hd0 : d n k ≠ 0 := (Nat.gcd_pos_of_pos_left _ (a_pos hn k)).ne'
  rw [a_succ_eq, Nat.multiplicity_mul hd0 (Nat.add_one_ne_zero _),
    multiplicity_eq_zero_of_not_dvd h, Nat.add_zero]
  exact (multiplicity_dvd_iff_le ha0).1 ((pow_multiplicity_dvd _ _).trans (d_dvd_a n k))

/-- 정리: 어떤 n, p, K 에 대해 k ≥ K 에서 항상 p ∤ a_k/d_k + 1 이면 추측은 거짓이다.
(`not_conjecture_of_absorbed` 는 q_k 가 2의 거듭제곱인 특수한 경우.) -/
theorem not_conjecture_of_no_entry {n p K : ℕ} (hn : 0 < n) (hp : p.Prime)
    (h : ∀ k ≥ K, ¬ p ∣ a n k / d n k + 1) : ¬ Conjecture := by
  have := Fact.mk hp
  intro hC
  have hbound : ∀ j, multiplicity p (a n (K + j)) ≤ multiplicity p (a n K) := by
    intro j
    induction j with
    | zero => exact le_rfl
    | succ j ih =>
      rw [← Nat.add_assoc]
      exact (multiplicity_succ_le hn hp (h _ (by omega))).trans ih
  obtain ⟨k, hk, hB⟩ := hC n hn p hp (multiplicity p (a n K)) K
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hle : multiplicity p (d n (K + j)) ≤ multiplicity p (a n (K + j)) :=
    (multiplicity_dvd_iff_le (a_pos hn _).ne').1
      ((pow_multiplicity_dvd _ _).trans (d_dvd_a _ _))
  rw [padicValNat_def] at hB
  have := hbound j
  omega

/-- 따름정리 (필요조건): 추측이 참이면, 모든 n 과 모든 소수 p 에 대해
p ∣ a_k/d_k + 1 인 k 가 무한히 많아야 한다. -/
theorem conjecture_needs_entries (h : Conjecture) {n p : ℕ} (hn : 0 < n) (hp : p.Prime) :
    ∀ K : ℕ, ∃ k ≥ K, p ∣ a n k / d n k + 1 := by
  intro K
  by_contra hne
  push Not at hne
  exact not_conjecture_of_no_entry hn hp (fun k hk => hne k hk) h

/-! ## 8. p = 2 에서는 추측이 (무조건) 참이다

v₂(d_k) ≤ B 가 계속된다고 하자.
* v₂(a_k) ≤ v₂(s_k!) 이면 q_k = a_k/d_k 가 홀수라 q_k+1 이 짝수 → v₂(a) 가 1 이상 증가.
  이런 단계는 B+1 번 넘게 연속될 수 없다.
* 그렇지 않으면 v₂(s_k!) ≤ v₂(d_k) ≤ B 이므로 s_k ≤ 2B+1.
* s(x+y) ≤ s(x)+s(y) 로 그 사이 단계의 자릿수 합도 상수 C 로 유계 → d_k ≤ C!.
* 증가량이 유계인 증가 수열은 [10^N − C!, 10^N) 에 들어가야 하는데,
  그곳의 수는 자릿수 합이 9(N − L) 이상이라 모순. -/

theorem s_eq (x : ℕ) : s x = x % 10 + s (x / 10) := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp [s]
  · unfold s
    rw [Nat.digits_def' (by norm_num) hx, List.sum_cons]

theorem s_zero : s 0 = 0 := by simp [s]

theorem s_le_one {c : ℕ} (h : c ≤ 1) : s c = c := by
  rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl
  · exact s_zero
  · rw [s_eq]; simp [s_zero]

/-- 자릿수 합의 열등가법성. -/
theorem s_add_le_aux : ∀ N x y : ℕ, x + y ≤ N → s (x + y) ≤ s x + s y := by
  intro N
  induction N with
  | zero =>
    intro x y h
    obtain rfl : x = 0 := by omega
    obtain rfl : y = 0 := by omega
    simp [s_zero]
  | succ N ih =>
    intro x y h
    rcases Nat.eq_zero_or_pos (x + y) with h0 | hpos
    · obtain rfl : x = 0 := by omega
      obtain rfl : y = 0 := by omega
      simp [s_zero]
    · obtain ⟨c, hc⟩ : ∃ c, c = (x % 10 + y % 10) / 10 := ⟨_, rfl⟩
      have hq : (x + y) / 10 = (x / 10 + y / 10) + c := by omega
      have hr : (x + y) % 10 = (x % 10 + y % 10) % 10 := by omega
      have hsc : s c = c := s_le_one (by omega)
      have h1 := ih (x / 10 + y / 10) c (by omega)
      have h2 := ih (x / 10) (y / 10) (by omega)
      rw [s_eq (x + y), hq, hr, s_eq x, s_eq y]
      omega

theorem s_add_le (x y : ℕ) : s (x + y) ≤ s x + s y := s_add_le_aux _ x y le_rfl

theorem s_div_pow_le (L x : ℕ) : s (x / 10 ^ L) ≤ s x := by
  induction L generalizing x with
  | zero => simp
  | succ L ih =>
    rw [pow_succ, ← Nat.div_div_eq_div_mul]
    have := s_eq (x / 10 ^ L)
    have := ih x
    omega

theorem s_pow_sub_one (M : ℕ) : s (10 ^ M - 1) = 9 * M := by
  induction M with
  | zero => simp [s_zero]
  | succ M ih =>
    have hP : 1 ≤ 10 ^ M := Nat.one_le_pow _ _ (by norm_num)
    rw [s_eq, pow_succ]
    have h1 : (10 ^ M * 10 - 1) % 10 = 9 := by omega
    have h2 : (10 ^ M * 10 - 1) / 10 = 10 ^ M - 1 := by omega
    rw [h1, h2, ih]
    ring

/-- 10^N 바로 아래 수는 자릿수 합이 크다. -/
theorem s_ge_of_near {x N L : ℕ} (hL : L ≤ N) (h1 : 10 ^ N - 10 ^ L ≤ x) (h2 : x < 10 ^ N) :
    9 * (N - L) ≤ s x := by
  have hN : 10 ^ N = 10 ^ (N - L) * 10 ^ L := by rw [← pow_add, Nat.sub_add_cancel hL]
  have hQ : 0 < 10 ^ L := by positivity
  have hP : 1 ≤ 10 ^ (N - L) := Nat.one_le_pow _ _ (by norm_num)
  have hdiv : x / 10 ^ L = 10 ^ (N - L) - 1 := by
    apply Nat.div_eq_of_lt_le
    · rw [Nat.sub_mul, one_mul, ← hN]; exact h1
    · rw [Nat.sub_add_cancel hP, ← hN]; exact h2
  calc 9 * (N - L) = s (10 ^ (N - L) - 1) := (s_pow_sub_one _).symm
    _ = s (x / 10 ^ L) := by rw [hdiv]
    _ ≤ s x := s_div_pow_le L x

theorem pow_dvd_factorial_mul {p : ℕ} (hp : 0 < p) (m : ℕ) : p ^ m ∣ (p * m)! := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h : (p * (m + 1))! = (p * m + p) * (p * m + p - 1)! := by
      rw [show p * (m + 1) = (p * m + p - 1) + 1 by rw [Nat.mul_succ]; omega, Nat.factorial_succ,
        show p * m + p - 1 + 1 = p * m + p by omega]
    rw [h, pow_succ, mul_comm (p ^ m) p]
    exact Nat.mul_dvd_mul (Dvd.intro (m + 1) (by ring))
      (ih.trans (Nat.factorial_dvd_factorial (by omega)))

/-- v_p(S!) ≤ B 이면 S < p(B+1). -/
theorem small_of_vp_le {p S B : ℕ} (hp : p.Prime) (h : multiplicity p S ! ≤ B) :
    S < p * (B + 1) := by
  by_contra hlt
  push Not at hlt
  have := Fact.mk hp
  have h1 : p ^ (B + 1) ∣ S ! :=
    (pow_dvd_factorial_mul hp.pos (B + 1)).trans (Nat.factorial_dvd_factorial hlt)
  have := (multiplicity_dvd_iff_le (Nat.factorial_ne_zero S)).1 h1
  omega

theorem d_pos {n : ℕ} (hn : 0 < n) (k : ℕ) : 0 < d n k :=
  Nat.gcd_pos_of_pos_left _ (a_pos hn k)

theorem a_succ_add (n k : ℕ) : a n (k + 1) = a n k + d n k := by rw [a_succ]; rfl

theorem a_ge {n : ℕ} (hn : 0 < n) (k : ℕ) : k ≤ a n k := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih => rw [a_succ_add]; have := d_pos hn k; omega

/-! ### 자릿수 합이 유계일 수는 없다 -/

/-- 증가량이 유계인 증가 수열은 10^N 바로 아래(999…9 구간)를 밟으므로
자릿수 합이 계속 C 이하일 수 없다. -/
theorem no_bounded_digit_sum {n K C : ℕ} (hn : 0 < n) (hS : ∀ k ≥ K, s (a n k) ≤ C) :
    False := by
  have hD : ∀ k ≥ K, d n k ≤ C ! := fun k hk =>
    (Nat.le_of_dvd (Nat.factorial_pos _) (Nat.gcd_dvd_right _ _)).trans
      (Nat.factorial_le (hS k hk))
  obtain ⟨L, hL⟩ : ∃ L, L = C ! := ⟨_, rfl⟩
  have hL10 : C ! ≤ 10 ^ L := hL ▸ (Nat.lt_pow_self (by norm_num)).le
  obtain ⟨N, hN⟩ : ∃ N, N = L + C + 1 + a n K := ⟨_, rfl⟩
  have hN10 : a n K < 10 ^ N :=
    lt_of_lt_of_le (by omega : a n K < N) (Nat.lt_pow_self (by norm_num)).le
  have hex : ∃ j, 10 ^ N ≤ a n (K + j) :=
    ⟨10 ^ N, le_trans (by omega) (a_ge hn (K + 10 ^ N))⟩
  classical
  obtain ⟨j, hj, hmin⟩ : ∃ j, 10 ^ N ≤ a n (K + j) ∧ ∀ i < j, ¬ 10 ^ N ≤ a n (K + i) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩
  have hj0 : j ≠ 0 := by
    rintro rfl
    simp only [Nat.add_zero] at hj
    omega
  have hlt : a n (K + (j - 1)) < 10 ^ N := by
    have := hmin (j - 1) (by omega); omega
  have hstep : a n (K + j) = a n (K + (j - 1)) + d n (K + (j - 1)) := by
    rw [show K + j = K + (j - 1) + 1 by omega, a_succ_add]
  have hdle := hD (K + (j - 1)) (by omega)
  have hnear : 10 ^ N - 10 ^ L ≤ a n (K + (j - 1)) := by omega
  have hs := s_ge_of_near (by omega : L ≤ N) hnear hlt
  have hc := hS (K + (j - 1)) (by omega)
  omega

/-- 따름정리 (무조건): 모든 n 에서 limsup s(a_k) = ∞. -/
theorem digit_sum_unbounded {n : ℕ} (hn : 0 < n) : ∀ C K : ℕ, ∃ k ≥ K, C < s (a n k) := by
  intro C K
  by_contra hne
  push Not at hne
  exact no_bounded_digit_sum hn hne

/-! ### 자릿수 합 한 단계 상한에 쓰는 단조 함수들 -/

def Smax (t : ℕ) : ℕ := (Finset.range (t + 1)).sup s
def Fb (t : ℕ) : ℕ := t + Smax (t !)
def Gb (c : ℕ) : ℕ := (Finset.range (c + 1)).sup Fb

theorem s_le_Smax {y t : ℕ} (h : y ≤ t) : s y ≤ Smax t :=
  Finset.le_sup (f := s) (Finset.mem_range.2 (by omega))

theorem Fb_le_Gb {t c : ℕ} (h : t ≤ c) : Fb t ≤ Gb c :=
  Finset.le_sup (f := Fb) (Finset.mem_range.2 (by omega))

theorem le_Gb (c : ℕ) : c ≤ Gb c := (Nat.le_add_right c _).trans (Fb_le_Gb le_rfl)

theorem Gb_mono : Monotone Gb := fun _ _ h =>
  Finset.sup_mono (Finset.range_mono (by omega))

theorem le_Gb_iter (j x : ℕ) : x ≤ Gb^[j] x := by
  induction j with
  | zero => exact le_rfl
  | succ j ih => rw [Function.iterate_succ_apply']; exact ih.trans (le_Gb _)

theorem Gb_iter_mono {i m : ℕ} (h : i ≤ m) (x : ℕ) : Gb^[i] x ≤ Gb^[m] x := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Function.iterate_add_apply]
  exact Gb_mono.iterate i (le_Gb_iter j x)

theorem s_succ_le (n k : ℕ) : s (a n (k + 1)) ≤ Fb (s (a n k)) := by
  rw [a_succ_add]
  have hd : d n k ≤ (s (a n k))! :=
    Nat.le_of_dvd (Nat.factorial_pos _) (Nat.gcd_dvd_right _ _)
  exact (s_add_le _ _).trans (Nat.add_le_add_left (s_le_Smax hd) _)

theorem window {n k c : ℕ} (h : s (a n k) ≤ c) (j : ℕ) : s (a n (k + j)) ≤ Gb^[j] c := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    rw [← Nat.add_assoc, Function.iterate_succ_apply']
    exact (s_succ_le n (k + j)).trans (Fb_le_Gb ih)

/-- W 단계마다 한 번씩 자릿수 합이 c 이하이면, 이후 자릿수 합은 항상 유계. -/
theorem S_bound_gen {n K W c : ℕ} (h : ∀ k ≥ K, ∃ i ≤ W, s (a n (k + i)) ≤ c) :
    ∀ k ≥ K + W, s (a n k) ≤ Gb^[W] c := by
  intro k hk
  obtain ⟨i, hi, hs⟩ := h (k - W) (by omega)
  have hw := window hs (W - i)
  rw [show k - W + i + (W - i) = k by omega] at hw
  exact hw.trans (Gb_iter_mono (by omega) _)

/-! ### 경우 A / 경우 B (일반 소수 p) -/

/-- 경우 A: v_p(a) ≤ v_p(s!) 이면 v_p(d) = v_p(a), p ∤ q, 그리고
v_p(a_{k+1}) = v_p(a_k) + v_p(q_k + 1). -/
theorem caseA_gen {n k p : ℕ} (hn : 0 < n) (hp : p.Prime)
    (h : multiplicity p (a n k) ≤ multiplicity p (s (a n k))!) :
    multiplicity p (d n k) = multiplicity p (a n k) ∧
      multiplicity p (a n (k + 1)) =
        multiplicity p (a n k) + multiplicity p (a n k / d n k + 1) ∧
      ¬ p ∣ a n k / d n k := by
  have := Fact.mk hp
  have ha0 : a n k ≠ 0 := (a_pos hn k).ne'
  have hd0 : d n k ≠ 0 := (d_pos hn k).ne'
  have hdge : multiplicity p (a n k) ≤ multiplicity p (d n k) := by
    have hdvd : p ^ multiplicity p (a n k) ∣ d n k :=
      Nat.dvd_gcd (pow_multiplicity_dvd _ _) ((Nat.pow_dvd_pow p h).trans (pow_multiplicity_dvd _ _))
    exact (multiplicity_dvd_iff_le hd0).1 hdvd
  have hdle : multiplicity p (d n k) ≤ multiplicity p (a n k) :=
    (multiplicity_dvd_iff_le ha0).1 ((pow_multiplicity_dvd _ _).trans (d_dvd_a n k))
  have hq0 : multiplicity p (a n k / d n k) = 0 := by
    rw [Nat.multiplicity_div_of_dvd (d_dvd_a n k)]; omega
  have hqne : a n k / d n k ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (a_pos hn k) (d_dvd_a n k)) (d_pos hn k)).ne'
  refine ⟨by omega, ?_, ?_⟩
  · rw [a_succ_eq, Nat.multiplicity_mul hd0 (Nat.add_one_ne_zero _)]
    omega
  · intro hpq
    have := (multiplicity_dvd_iff_le (p := p) (n := 1) hqne).1 (by simpa using hpq)
    omega

/-- 경우 B: v_p(s!) < v_p(a) 이면 v_p(s!) ≤ v_p(d). -/
theorem caseB_gen {n k p : ℕ} (hn : 0 < n) (hp : p.Prime)
    (h : multiplicity p (s (a n k))! < multiplicity p (a n k)) :
    multiplicity p (s (a n k))! ≤ multiplicity p (d n k) := by
  have := Fact.mk hp
  have hdvd : p ^ multiplicity p (s (a n k))! ∣ d n k :=
    Nat.dvd_gcd ((Nat.pow_dvd_pow p h.le).trans (pow_multiplicity_dvd _ _))
      (pow_multiplicity_dvd _ _)
  exact (multiplicity_dvd_iff_le (d_pos hn k).ne').1 hdvd

/-- 경우 A 가 계속되는 구간에서 v_p(a) 는 줄지 않는다. -/
theorem mono_run {n p k : ℕ} (hn : 0 < n) (hp : p.Prime) (m : ℕ)
    (hA : ∀ j, k ≤ j → j < k + m → multiplicity p (a n j) ≤ multiplicity p (s (a n j))!) :
    multiplicity p (a n k) ≤ multiplicity p (a n (k + m)) := by
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    have h1 := ih (fun j h1 h2 => hA j h1 (by omega))
    have h2 := (caseA_gen hn hp (hA (k + m) (by omega) (by omega))).2.1
    rw [← Nat.add_assoc]
    omega

/-- 경우 A 이면서 p ∣ q+1 이면 v_p(a) 가 1 이상 증가. -/
theorem entry_step {n p j : ℕ} (hn : 0 < n) (hp : p.Prime)
    (hA : multiplicity p (a n j) ≤ multiplicity p (s (a n j))!)
    (he : p ∣ a n j / d n j + 1) :
    multiplicity p (a n j) + 1 ≤ multiplicity p (a n (j + 1)) := by
  have := Fact.mk hp
  have h1 := (caseA_gen hn hp hA).2.1
  have h2 := (multiplicity_dvd_iff_le (p := p) (n := 1) (Nat.add_one_ne_zero _)).1
    (by simpa using he)
  omega

/-- v_p(d) ≤ B 가 계속되고, G 단계마다 "진입 또는 경우 B" 가 있으면,
(B+1)·G 단계 안에 반드시 경우 B 가 온다. -/
theorem caseB_soon_gen {n p G K B : ℕ} (hn : 0 < n) (hp : p.Prime)
    (hE : ∀ k ≥ K, ∃ i < G, p ∣ a n (k + i) / d n (k + i) + 1 ∨
      multiplicity p (s (a n (k + i)))! < multiplicity p (a n (k + i)))
    (H : ∀ k ≥ K, multiplicity p (d n k) ≤ B) {k : ℕ} (hk : K ≤ k) :
    ∃ i ≤ (B + 1) * G,
      multiplicity p (s (a n (k + i)))! < multiplicity p (a n (k + i)) := by
  by_contra hne
  push Not at hne
  have hA : ∀ j, k ≤ j → j ≤ k + (B + 1) * G →
      multiplicity p (a n j) ≤ multiplicity p (s (a n j))! := fun j h1 h2 => by
    have := hne (j - k) (by omega)
    rwa [show k + (j - k) = j by omega] at this
  have hgrow : ∀ t ≤ B + 1, t ≤ multiplicity p (a n (k + t * G)) := by
    intro t
    induction t with
    | zero => intro _; exact Nat.zero_le _
    | succ t ih =>
      intro ht
      have ih' := ih (by omega)
      have hG1 : (t + 1) * G = t * G + G := by ring
      have hG2 : (t + 1) * G ≤ (B + 1) * G := Nat.mul_le_mul_right _ ht
      obtain ⟨i, hi, hent⟩ := hE (k + t * G) (by omega)
      rcases hent with hent | hent
      · have m1 := mono_run hn hp (k := k + t * G) i
          (fun j h1 h2 => hA j (by omega) (by omega))
        have e := entry_step hn hp (hA _ (by omega) (by omega)) hent
        have m2 := mono_run hn hp (k := k + t * G + i + 1) (G - i - 1)
          (fun j h1 h2 => hA j (by omega) (by omega))
        rw [show k + t * G + i + 1 + (G - i - 1) = k + (t + 1) * G by omega] at m2
        omega
      · have := hA (k + t * G + i) (by omega) (by omega)
        omega
  have h1 := hgrow (B + 1) le_rfl
  have h2 := (caseA_gen hn hp (hA (k + (B + 1) * G) (by omega) le_rfl)).1
  have h3 := H (k + (B + 1) * G) (by omega)
  omega

/-- **일반 판정법 (무조건)**: 어떤 G, K 에 대해, k ≥ K 부터 G 단계마다 적어도 한 번
"p ∣ a_k/d_k + 1 (p 진입)" 이거나 "v_p(s_k!) < v_p(a_k) (경우 B)" 이면
limsup v_p(d_k) = ∞. -/
theorem conjecture_of_entries {n p G K : ℕ} (hn : 0 < n) (hp : p.Prime)
    (hE : ∀ k ≥ K, ∃ i < G, p ∣ a n (k + i) / d n (k + i) + 1 ∨
      multiplicity p (s (a n (k + i)))! < multiplicity p (a n (k + i))) :
    ∀ B K' : ℕ, ∃ k ≥ K', B < padicValNat p (d n k) := by
  intro B K'
  by_contra hne
  push Not at hne
  have H : ∀ k ≥ max K K', multiplicity p (d n k) ≤ B := fun k hk => by
    rw [← padicValNat_def]; exact hne k (by omega)
  have hE' : ∀ k ≥ max K K', ∃ i < G, p ∣ a n (k + i) / d n (k + i) + 1 ∨
      multiplicity p (s (a n (k + i)))! < multiplicity p (a n (k + i)) :=
    fun k hk => hE k (by omega)
  have hsmall : ∀ k ≥ max K K', ∃ i ≤ (B + 1) * G, s (a n (k + i)) ≤ p * (B + 1) := by
    intro k hk
    obtain ⟨i, hi, hB⟩ := caseB_soon_gen hn hp hE' H hk
    exact ⟨i, hi, (small_of_vp_le hp ((caseB_gen hn hp hB).trans (H _ (by omega)))).le⟩
  exact no_bounded_digit_sum hn (S_bound_gen hsmall)

/-- **정리 (무조건)**: 모든 n ≥ 1 에 대해 limsup_{k→∞} v₂(d_k) = ∞.
즉 원래 추측은 p = 2 에서 참이다. (판정법에서 G = 1: 경우 A 이면 q 가 홀수라 2 ∣ q+1.) -/
theorem conjecture_two {n : ℕ} (hn : 0 < n) :
    ∀ B K : ℕ, ∃ k ≥ K, B < padicValNat 2 (d n k) :=
  conjecture_of_entries (G := 1) (K := 0) hn Nat.prime_two fun k _ => ⟨0, by omega, by
    by_cases h : multiplicity 2 (s (a n (k + 0)))! < multiplicity 2 (a n (k + 0))
    · exact Or.inr h
    · left
      push Not at h
      have := (caseA_gen hn Nat.prime_two h).2.2
      generalize a n (k + 0) / d n (k + 0) = q at this ⊢
      omega⟩

/-! ## 9. 추측의 남은 내용은 홀수 소수뿐 -/

/-- p = 2 는 `conjecture_two` 로 해결되었으므로, 원래 추측은 홀수 소수에 대한 명제와 동치다. -/
theorem conjecture_iff_odd : Conjecture ↔
    ∀ n : ℕ, 0 < n → ∀ p : ℕ, p.Prime → p ≠ 2 →
      ∀ B K : ℕ, ∃ k ≥ K, B < padicValNat p (d n k) := by
  constructor
  · intro h n hn p hp _
    exact h n hn p hp
  · intro h n hn p hp
    by_cases h2 : p = 2
    · subst h2; exact conjecture_two hn
    · exact h n hn p hp h2

/-! ## 10. 탐구: s(u·2^m) 의 하한 (미해결 핵심을 직접 공략)

### 라운드 1: 끝자리 창(window) 논법
x = u·2^m, 5 ∤ u 이면 끝 k 자리 y = x mod 10^k 는 0 이 아닌 2^k 의 배수라 y ≥ 2^k ≥ 10^⌊3k/10⌋.
따라서 자리 [⌊3k/10⌋, k) 에 0 아닌 숫자가 있고, 이를 재귀하면 log_{10/3} k 개의 창을 얻는다. -/

/-- 자릿수 합은 아래 j 자리와 나머지로 쪼개진다. -/
theorem s_split (j y : ℕ) : s y = s (y % 10 ^ j) + s (y / 10 ^ j) := by
  induction j generalizing y with
  | zero => simp [Nat.mod_one, s_zero]
  | succ j ih =>
    have h1 : y % 10 ^ (j + 1) % 10 = y % 10 := by
      rw [_root_.pow_succ']; exact Nat.mod_mul_right_mod _ _ _
    have h2 : y % 10 ^ (j + 1) / 10 = y / 10 % 10 ^ j := by
      rw [_root_.pow_succ']; exact Nat.mod_mul_right_div_self _ _ _
    have h3 : y / 10 ^ (j + 1) = y / 10 / 10 ^ j := by
      rw [_root_.pow_succ', Nat.div_div_eq_div_mul]
    rw [s_eq y, ih (y / 10), s_eq (y % 10 ^ (j + 1)), h1, h2, h3]
    ring

theorem s_pos : ∀ z, 0 < z → 0 < s z := by
  intro z
  induction z using Nat.strong_induction_on with
  | _ z ih =>
    intro hz
    rw [s_eq]
    rcases Nat.eq_zero_or_pos (z % 10) with h | h
    · have := ih (z / 10) (by omega) (by omega)
      omega
    · omega

theorem ten_pow_le_two_pow {j k : ℕ} (h : 10 * j ≤ 3 * k) : 10 ^ j ≤ 2 ^ k := by
  have h1 : (10 ^ j) ^ 10 ≤ (2 ^ k) ^ 10 := by
    calc (10 ^ j) ^ 10 = 10 ^ (10 * j) := by rw [← pow_mul, mul_comm]
      _ ≤ 10 ^ (3 * k) := Nat.pow_le_pow_right (by norm_num) h
      _ = 1000 ^ k := by rw [pow_mul]; norm_num
      _ ≤ 1024 ^ k := Nat.pow_le_pow_left (by norm_num) k
      _ = (2 ^ k) ^ 10 := by rw [← pow_mul, show k * 10 = 10 * k by ring, pow_mul]; norm_num
  exact (Nat.pow_le_pow_iff_left (by norm_num)).1 h1

/-- 창의 개수: wlog k = 1 + wlog ⌊3k/10⌋ (k > 0). 대략 log_{10/3} k. -/
def wlog (k : ℕ) : ℕ := if h : k = 0 then 0 else 1 + wlog (3 * k / 10)
termination_by k
decreasing_by omega

theorem window_bound : ∀ k x, 2 ^ k ∣ x → ¬ 5 ∣ x → wlog k ≤ s (x % 10 ^ k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro x h2 h5
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [wlog]
    · obtain ⟨j, hj⟩ : ∃ j, j = 3 * k / 10 := ⟨_, rfl⟩
      have hjk : j < k := by omega
      have hwl : wlog k = 1 + wlog j := by
        rw [wlog]; split_ifs with h
        · omega
        · rw [hj]
      have hy2 : 2 ^ k ∣ x % 10 ^ k :=
        (Nat.dvd_mod_iff (pow_dvd_pow_of_dvd (by norm_num) k)).2 h2
      have hy0 : x % 10 ^ k ≠ 0 := by
        intro h0
        have h10 : 10 ^ k ∣ x := Nat.dvd_of_mod_eq_zero h0
        exact h5 ((show (5 : ℕ) ∣ 10 by norm_num).trans ((dvd_pow_self 10 hk.ne').trans h10))
      have hyge : 10 ^ j ≤ x % 10 ^ k :=
        (ten_pow_le_two_pow (by omega)).trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hy0) hy2)
      have hsplit := s_split j (x % 10 ^ k)
      have hmod : x % 10 ^ k % 10 ^ j = x % 10 ^ j :=
        Nat.mod_mod_of_dvd x (pow_dvd_pow 10 hjk.le)
      have hih := ih j hjk x ((pow_dvd_pow 2 hjk.le).trans h2) h5
      have htop : 0 < s (x % 10 ^ k / 10 ^ j) :=
        s_pos _ (Nat.div_pos hyge (by positivity))
      rw [hmod] at hsplit
      omega

theorem s_mul_pow_ge {u : ℕ} (hu : ¬ 5 ∣ u) (m : ℕ) : wlog m ≤ s (u * 2 ^ m) := by
  have h5 : ¬ 5 ∣ u * 2 ^ m := by
    intro h
    rcases (Nat.Prime.dvd_mul (by norm_num)).1 h with h | h
    · exact hu h
    · have := Nat.Prime.dvd_of_dvd_pow (by norm_num : (5 : ℕ).Prime) h
      omega
  have := window_bound m (u * 2 ^ m) (Dvd.intro_left u rfl) h5
  have hs := s_split m (u * 2 ^ m)
  omega

theorem le_wlog : ∀ t k, 4 ^ t ≤ k → t ≤ wlog k := by
  intro t
  induction t with
  | zero => intro _ _; exact Nat.zero_le _
  | succ t ih =>
    intro k hk
    have h4 : 4 ^ (t + 1) = 4 * 4 ^ t := _root_.pow_succ' 4 t
    have hP : 1 ≤ 4 ^ t := Nat.one_le_pow _ _ (by norm_num)
    have hk0 : k ≠ 0 := by omega
    have := ih (3 * k / 10) (by omega)
    rw [wlog]; split_ifs with h
    · omega
    · omega

/-- **라운드 1 결과 (Radcliffe 형 하한)**: 5 ∤ u 이면 4^t ≤ m 일 때 t ≤ s(u·2^m).
즉 s(u·2^m) ≥ log₄ m. -/
theorem s_mul_pow_ge_log {u : ℕ} (hu : ¬ 5 ∣ u) {m t : ℕ} (h : 4 ^ t ≤ m) :
    t ≤ s (u * 2 ^ m) :=
  (le_wlog t m h).trans (s_mul_pow_ge hu m)

theorem s_mul_ten (y : ℕ) : s (10 * y) = s y := by
  rw [s_eq]; simp [Nat.mul_mod_right, Nat.mul_div_cancel_left y (by norm_num : 0 < 10)]

/-- 우리 수열에 적용: s(3315·2^(m+1)) ≥ log₄ m. -/
theorem s_3315_ge_log {m t : ℕ} (h : 4 ^ t ≤ m) : t ≤ s (3315 * 2 ^ (m + 1)) := by
  have : 3315 * 2 ^ (m + 1) = 10 * (663 * 2 ^ m) := by ring
  rw [this, s_mul_ten]
  exact s_mul_pow_ge_log (by norm_num) h

/-! ### 라운드 2: 받아올림 항등식 s(2x) + 9·c(x) = 2·s(x)
c(x) = 5 이상인 자릿수 개수 = x 를 2배 할 때 생기는 받아올림 수. -/

def c5 (x : ℕ) : ℕ := ((Nat.digits 10 x).map (fun d => if 5 ≤ d then 1 else 0)).sum

theorem c5_eq (x : ℕ) : c5 x = (if 5 ≤ x % 10 then 1 else 0) + c5 (x / 10) := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp [c5]
  · unfold c5
    rw [Nat.digits_def' (by norm_num) hx, List.map_cons, List.sum_cons]

theorem s_two_mul_add_one (q : ℕ) : s (2 * q + 1) = s (2 * q) + 1 := by
  rw [s_eq (2 * q + 1), s_eq (2 * q)]
  have h1 : (2 * q + 1) % 10 = (2 * q) % 10 + 1 := by omega
  have h2 : (2 * q + 1) / 10 = (2 * q) / 10 := by omega
  rw [h1, h2]; ring

theorem carry_identity : ∀ x, s (2 * x) + 9 * c5 x = 2 * s x := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp [s_zero, c5]
    · have hq := ih (x / 10) (by omega)
      rw [s_eq (2 * x), c5_eq x, s_eq x]
      have h1 : (2 * x) % 10 = (2 * (x % 10)) % 10 := by omega
      have h2 : (2 * x) / 10 = 2 * (x / 10) + (if 5 ≤ x % 10 then 1 else 0) := by
        split_ifs <;> omega
      rw [h1, h2]
      split_ifs with h
      · rw [s_two_mul_add_one]; omega
      · simp only [Nat.add_zero, Nat.zero_add]; omega

theorem c5_le : ∀ x, 5 * c5 x ≤ s x := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp [c5]
    · have := ih (x / 10) (by omega)
      rw [c5_eq, s_eq x]
      split_ifs <;> omega

/-- 2배 하면 자릿수 합은 최대 2배, 최소 1/5 배. -/
theorem s_two_mul_le (x : ℕ) : s (2 * x) ≤ 2 * s x := by
  have := carry_identity x; omega

theorem s_le_five_mul_s_two_mul (x : ℕ) : s x ≤ 5 * s (2 * x) := by
  have := carry_identity x; have := c5_le x; omega

/-- 누적 형태: Σ_{m<M} s(u·2^m) + s(u) = s(u·2^M) + 9·Σ_{m<M} c(u·2^m).
즉 "s 가 평균적으로 선형" ⇔ "5 이상 자릿수의 개수가 평균적으로 선형". -/
theorem sum_s_eq (u M : ℕ) :
    (∑ m ∈ Finset.range M, s (u * 2 ^ m)) + s u =
      s (u * 2 ^ M) + 9 * ∑ m ∈ Finset.range M, c5 (u * 2 ^ m) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hc := carry_identity (u * 2 ^ M)
    rw [show 2 * (u * 2 ^ M) = u * 2 ^ (M + 1) by ring] at hc
    omega

/-! ### 라운드 3: 0 블록은 시간을 거슬러 가면 1 씩만 줄어든다
2x 의 자리 [i, i+L) 이 모두 0 이면 x 의 자리 [i, i+L−1) 도 모두 0. -/

theorem zero_block_back {x i L : ℕ} (hL : 1 ≤ L) (h : 10 ^ L ∣ (2 * x) / 10 ^ i) :
    10 ^ (L - 1) ∣ x / 10 ^ i := by
  have hpos : 0 < 10 ^ i := by positivity
  have hx : x = 10 ^ i * (x / 10 ^ i) + x % 10 ^ i := (Nat.div_add_mod x (10 ^ i)).symm
  have hC : x % 10 ^ i < 10 ^ i := Nat.mod_lt _ hpos
  have h2x : (2 * x) / 10 ^ i = 2 * (x / 10 ^ i) + (2 * (x % 10 ^ i)) / 10 ^ i := by
    conv_lhs => rw [hx]
    rw [show 2 * (10 ^ i * (x / 10 ^ i) + x % 10 ^ i) =
      2 * (x % 10 ^ i) + 10 ^ i * (2 * (x / 10 ^ i)) by ring, Nat.add_mul_div_left _ _ hpos]
    ring
  have hc : (2 * (x % 10 ^ i)) / 10 ^ i ≤ 1 := by
    have : (2 * (x % 10 ^ i)) / 10 ^ i < 2 := Nat.div_lt_of_lt_mul (by linarith)
    omega
  rw [h2x] at h
  have h10 : 10 ^ L = 2 * (5 * 10 ^ (L - 1)) := by
    rw [← mul_assoc, show (2 : ℕ) * 5 = 10 by rfl, ← _root_.pow_succ']
    congr 1; omega
  have heven : 2 ∣ 2 * (x / 10 ^ i) + (2 * (x % 10 ^ i)) / 10 ^ i :=
    (Dvd.intro _ h10.symm).trans h
  have hc0 : (2 * (x % 10 ^ i)) / 10 ^ i = 0 := by
    generalize (2 * (x % 10 ^ i)) / 10 ^ i = c at hc heven ⊢
    generalize x / 10 ^ i = X at heven
    omega
  rw [hc0, Nat.add_zero, h10] at h
  have h5 : 5 * 10 ^ (L - 1) ∣ x / 10 ^ i := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h
  exact (Dvd.intro_left 5 rfl).trans h5

/-- 반복: u·2^m 의 자리 [i, i+L) 이 0 블록이면, t ≤ m 단계 전 u·2^(m−t) 에도
길이 L − t 인 0 블록이 같은 자리에 있다. -/
theorem zero_block_back_iter {u i L m : ℕ} (h : 10 ^ L ∣ (u * 2 ^ m) / 10 ^ i) :
    ∀ t ≤ m, 10 ^ (L - t) ∣ (u * 2 ^ (m - t)) / 10 ^ i := by
  intro t
  induction t with
  | zero => intro _; simpa using h
  | succ t ih =>
    intro ht
    have h1 := ih (by omega)
    rcases Nat.lt_or_ge (L - t) 1 with hlt | hge
    · rw [show L - (t + 1) = 0 by omega]; simp
    · have heq : u * 2 ^ (m - t) = 2 * (u * 2 ^ (m - (t + 1))) := by
        rw [show m - t = (m - (t + 1)) + 1 by omega]; ring
      rw [heq] at h1
      have := zero_block_back hge h1
      rwa [show L - t - 1 = L - (t + 1) by omega] at this

/-! ### 라운드 5: 0 블록 ⇔ 작은 5-진 잉여, 그리고 조건부 m/log m 하한

j ≤ m 이면 u·2^m mod 10^j = 2^j · (u·2^(m−j) mod 5^j).
따라서 "자리 [kB, (k+1)B) 가 0 블록" ⇔ "2^{(k+1)B}·r < 10^{kB}" (r 은 5-진 잉여).
잉여가 너무 작지 않다는 Diophantine 가설이면 길이 B 블록마다 0 아닌 자리가 있어
s ≥ (블록 수) 가 된다. -/

theorem mod_ten_pow_eq (u m j : ℕ) (h : j ≤ m) :
    u * 2 ^ m % 10 ^ j = 2 ^ j * (u * 2 ^ (m - j) % 5 ^ j) := by
  have h2 : 2 ^ m = 2 ^ j * 2 ^ (m - j) := by rw [← pow_add, Nat.add_sub_cancel' h]
  have e1 : u * 2 ^ m = 2 ^ j * (u * 2 ^ (m - j)) := by rw [h2]; ring
  have e2 : (10 : ℕ) ^ j = 2 ^ j * 5 ^ j := by rw [← mul_pow]; norm_num
  rw [e1, e2, Nat.mul_mod_mul_left]

/-- 정렬된 길이 B 블록이 t 개 모두 0 이 아니면 s(x) ≥ t. -/
theorem s_ge_blocks (B : ℕ) : ∀ t x, (∀ k < t, (x / 10 ^ (k * B)) % 10 ^ B ≠ 0) → t ≤ s x := by
  intro t
  induction t with
  | zero => intro _ _; exact Nat.zero_le _
  | succ t ih =>
    intro x h
    have h0 : x % 10 ^ B ≠ 0 := by simpa using h 0 (by omega)
    have hrest : ∀ k < t, ((x / 10 ^ B) / 10 ^ (k * B)) % 10 ^ B ≠ 0 := fun k hk => by
      have := h (k + 1) (by omega)
      rwa [Nat.div_div_eq_div_mul, ← pow_add, show B + k * B = (k + 1) * B by ring]
    have h1 := ih (x / 10 ^ B) hrest
    have hs := s_split B x
    have hp := s_pos _ (Nat.pos_of_ne_zero h0)
    omega

/-- 블록 (x / 10^a) % 10^b 가 0 이 아니려면 x mod 10^a·10^b ≥ 10^a 이면 된다. -/
theorem block_ne_zero {x a b : ℕ} (h : 10 ^ a ≤ x % (10 ^ a * 10 ^ b)) :
    (x / 10 ^ a) % 10 ^ b ≠ 0 := by
  intro h0
  rw [Nat.mod_mul, h0, Nat.mul_zero, Nat.add_zero] at h
  exact absurd (Nat.mod_lt x (by positivity : 0 < 10 ^ a)) (not_lt.2 h)

/-- **라운드 5 조건부 정리**: tB ≤ m 이고, 각 k < t 에 대해 5-진 잉여
r = u·2^(m−(k+1)B) mod 5^{(k+1)B} 가 10^{kB} ≤ 2^{(k+1)B}·r (즉 r/5^{(k+1)B} ≥ 10^{−B}) 이면
s(u·2^m) ≥ t. -/
theorem s_ge_of_no_small_residue {u m B t : ℕ} (hB : t * B ≤ m)
    (H : ∀ k < t, 10 ^ (k * B) ≤
      2 ^ ((k + 1) * B) * (u * 2 ^ (m - (k + 1) * B) % 5 ^ ((k + 1) * B))) :
    t ≤ s (u * 2 ^ m) := by
  apply s_ge_blocks B t
  intro k hk
  apply block_ne_zero
  have hj : (k + 1) * B ≤ m := le_trans (Nat.mul_le_mul_right _ hk) hB
  rw [← pow_add, show k * B + B = (k + 1) * B by ring, mod_ten_pow_eq u m _ hj]
  exact H k hk

/-! ### 라운드 7: 2-진 정보만으로는 (C) 를 얻을 수 없다 (장벽의 인증)

"2^m ∣ x, 5 ∤ x" 만 쓰는 논법(라운드 1 등)의 한계를 잰다. 2-진 자릿수 DP 로 구한
2^t 배수의 최소 자릿수 합은 t = 4..56 에서 4,6,8,9,11,12,13,14,15,16,19,22 로 약 0.39t.
특히 t = 48 에서 자릿수 합 19 인 배수가 있으므로, 2-진 정보만으로는 s ≥ m/2 조차 나올 수 없다.
(C) 는 s ≥ m 을 요구하므로, (C) 의 증명은 반드시 u 가 작다는 (크기) 정보를 써야 한다. -/

theorem two_adic_witness :
    2 ^ 48 ∣ 10000001000001000000030100101011000000210010112 ∧
      ¬ 5 ∣ 10000001000001000000030100101011000000210010112 ∧
      s 10000001000001000000030100101011000000210010112 = 19 := by
  refine ⟨by norm_num, by norm_num, by norm_num [s]⟩

/-- 따라서 "2^48 ∣ x, 5 ∤ x ⇒ s(x) ≥ 24" 같은 명제는 거짓이다. -/
theorem two_adic_info_insufficient : ¬ (∀ x, 2 ^ 48 ∣ x → ¬ 5 ∣ x → 24 ≤ s x) := by
  intro h
  obtain ⟨h1, h2, h3⟩ := two_adic_witness
  have := h _ h1 h2
  omega

/-! ### 라운드 8: f(t) = min{ s(N) : 2^t ∣ N, 5 ∤ N } 의 상·하한 (Lean 으로 확정된 범위)

상한 (고전적 구성): 마지막 자리 2, 나머지 자리 0/1 로 2^t 의 배수를 만든다.
2^k ∣ N 이면 N 과 N + 10^k (≡ N + 2^k mod 2^(k+1)) 중 하나는 2^(k+1) 의 배수이기 때문.
하한: 라운드 1 의 창 논법. 따라서 wlog t ≤ f(t) ≤ t + 1. (수치로는 f(t) ≈ 0.39t.) -/

theorem s_add_ten_pow {N k : ℕ} (h : N < 10 ^ k) : s (N + 10 ^ k) = s N + 1 := by
  have hs := s_split k (N + 10 ^ k)
  have h1 : (N + 10 ^ k) % 10 ^ k = N := by
    rw [Nat.add_mod_right]; exact Nat.mod_eq_of_lt h
  have h2 : (N + 10 ^ k) / 10 ^ k = 1 := by
    rw [Nat.add_div_right _ (by positivity), Nat.div_eq_of_lt h]
  rw [h1, h2] at hs
  have : s 1 = 1 := s_le_one le_rfl
  omega

theorem exists_sparse_multiple (t : ℕ) (ht : 1 ≤ t) :
    ∃ N, 2 ^ t ∣ N ∧ N % 10 = 2 ∧ N < 10 ^ t ∧ s N ≤ t + 1 := by
  induction t with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact ⟨2, by norm_num, by norm_num, by norm_num, by norm_num [s]⟩
    · obtain ⟨N, ⟨w, hw⟩, h10, hlt, hs⟩ := ih hk
      have hk10 : 10 ^ k % 10 = 0 := by
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        rw [pow_succ]; simp
      have h10k : (10 : ℕ) ^ (k + 1) = 10 * 10 ^ k := by ring
      rcases Nat.even_or_odd w with ⟨v, hv⟩ | ⟨v, hv⟩
      · refine ⟨N, ⟨v, ?_⟩, h10, by omega, by omega⟩
        rw [hw, hv, pow_succ]; ring
      · refine ⟨N + 10 ^ k, ?_, by omega, by omega, ?_⟩
        · obtain ⟨c, hc⟩ : Odd (5 ^ k) := Odd.pow ⟨2, by norm_num⟩
          refine ⟨v + c + 1, ?_⟩
          rw [hw, show (10 : ℕ) ^ k = 2 ^ k * 5 ^ k by rw [← mul_pow]; norm_num, hv, hc, pow_succ]
          ring
        · rw [s_add_ten_pow hlt]; omega

/-- **라운드 8 결과 (확정된 범위)**: t ≥ 1 이면
(1) s(N) ≤ t+1 인 2^t 의 배수 N (5 ∤ N) 이 존재하고,
(2) 2^t ∣ N, 5 ∤ N 인 모든 N 은 s(N) ≥ wlog t (≈ log_{10/3} t). -/
theorem f_sandwich (t : ℕ) (ht : 1 ≤ t) :
    (∃ N, 2 ^ t ∣ N ∧ ¬ 5 ∣ N ∧ s N ≤ t + 1) ∧
      ∀ N, 2 ^ t ∣ N → ¬ 5 ∣ N → wlog t ≤ s N := by
  refine ⟨?_, ?_⟩
  · obtain ⟨N, h2, h10, -, hs⟩ := exists_sparse_multiple t ht
    exact ⟨N, h2, by omega, hs⟩
  · intro N h2 h5
    have := window_bound t N h2 h5
    have := s_split t N
    omega

/-! ### 라운드 9: 길이 제한 — (C) 는 "u 가 정말 상수" 라는 정보를 써야 한다

t = 24 에서 길이 ℓ 인 2^t 배수의 최소 자릿수 합 곡선은 랜덤 모델 문턱과 거의 일치한다
(ℓ = 8..24: 29,25,22,20,20,17,17,17,12,… vs 모델 30,24,21,19,17,16,15,14,13,…).
"u 가 작기만 하면 s(u·2^m) ≥ m" 같은 균일한 (C) 는 거짓이다: -/

theorem uniform_C_fails : s (1637 * 2 ^ 100) = 92 := by norm_num [s]

/-- 반면 우리 수열의 값은 여유가 있다: s(3315·2^101) = s(663·2^100) = 132 ≥ 101. -/
theorem our_value_100 : s (663 * 2 ^ 100) = 132 := by norm_num [s]

/-! ### 라운드 10: 정확한 공식과 "골짜기 폭"

(1) 자릿수 합의 Legendre 형 공식: s(x) = x − 9·Σ_{k≥1} ⌊x/10^k⌋.
    x = u·2^m 이면 ⌊x/10^k⌋ = ⌊u·2^(m−k)/5^k⌋ 이므로 (C) ⇔ 5-진 분수 {u·2^(m−k)/5^k} 의
    평균 ≥ 0.369 (랜덤 모델 기대값 0.5).
(2) 골짜기 폭: s(2^t x) ≤ 2^t s(x), s(x) ≤ 5^t s(2^t x). 한 m 에서 자릿수 합이 작으면
    주변도 작지만, 그 폭은 log 수준이라 밀도 정리(대부분의 m 에서 큼)와 모순을 만들지 못한다. -/

theorem s_legendre : ∀ L x, x < 10 ^ L → s x + 9 * ∑ k ∈ Finset.range L, x / 10 ^ (k + 1) = x := by
  intro L
  induction L with
  | zero =>
    intro x hx
    have : x = 0 := by simpa using hx
    subst this; simp [s_zero]
  | succ L ih =>
    intro x hx
    have hx' : x / 10 < 10 ^ L := by rw [pow_succ] at hx; omega
    have h := ih (x / 10) hx'
    rw [Finset.sum_range_succ']
    have hterm : ∀ k ∈ Finset.range L, x / 10 ^ (k + 1 + 1) = x / 10 / 10 ^ (k + 1) := by
      intro k _
      rw [Nat.div_div_eq_div_mul, ← _root_.pow_succ']
    rw [Finset.sum_congr rfl hterm, s_eq x]
    simp only [zero_add, pow_one]
    omega

theorem s_pow_two_mul_le (x t : ℕ) : s (2 ^ t * x) ≤ 2 ^ t * s x := by
  induction t with
  | zero => simp
  | succ t ih =>
    have e : 2 ^ (t + 1) * x = 2 * (2 ^ t * x) := by ring
    rw [e]
    calc s (2 * (2 ^ t * x)) ≤ 2 * s (2 ^ t * x) := s_two_mul_le _
      _ ≤ 2 * (2 ^ t * s x) := Nat.mul_le_mul_left _ ih
      _ = 2 ^ (t + 1) * s x := by ring

theorem s_le_pow_five_mul (x t : ℕ) : s x ≤ 5 ^ t * s (2 ^ t * x) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h := s_le_five_mul_s_two_mul (2 ^ t * x)
    rw [show 2 * (2 ^ t * x) = 2 ^ (t + 1) * x by ring] at h
    calc s x ≤ 5 ^ t * s (2 ^ t * x) := ih
      _ ≤ 5 ^ t * (5 * s (2 ^ (t + 1) * x)) := Nat.mul_le_mul_left _ h
      _ = 5 ^ (t + 1) * s (2 ^ (t + 1) * x) := by ring

/-! ### 라운드 11: 대부분의 잉여류는 자릿수 합 ≥ 0.29t 가 필요하다 (Chernoff 개수 세기)

정확한 지수 모멘트: Σ_{X<10^t} 4^(9t − s(X)) = 349525^t  (349525 = Σ_{d<10} 4^(9−d)).
Markov 로 #{X < 10^t : s(X) ≤ σ} · 4^(9t−σ) ≤ 349525^t. 잉여류 개수도 같은 상한을 갖는다.
σ ≤ 0.29t 이면 이 개수는 2^t 보다 작다 (실제 비율 ≤ 0.9965^t).
수치(빔 탐색): f(t) ≤ 96, 190, 279 (t = 300, 600, 900), 한계 기울기 → ≈ 0.29–0.30.
즉 특정 류 −1/5 도 "평범한 류" 의 값 c* ≈ 0.294 를 따르는 것으로 보인다. -/

theorem s_le_nine_mul : ∀ t x, x < 10 ^ t → s x ≤ 9 * t := by
  intro t
  induction t with
  | zero =>
    intro x hx
    have : x = 0 := by simpa using hx
    subst this; simp [s_zero]
  | succ t ih =>
    intro x hx
    have hx' : x / 10 < 10 ^ t := by rw [pow_succ] at hx; omega
    have := ih _ hx'
    rw [s_eq]; omega

theorem s_ten_mul_add {Y d : ℕ} (hd : d < 10) : s (10 * Y + d) = d + s Y := by
  rw [s_eq]
  have h1 : (10 * Y + d) % 10 = d := by omega
  have h2 : (10 * Y + d) / 10 = Y := by omega
  rw [h1, h2]

theorem sum_range_ten_mul (f : ℕ → ℕ) (n : ℕ) :
    ∑ X ∈ Finset.range (10 * n), f X =
      ∑ Y ∈ Finset.range n, ∑ d ∈ Finset.range 10, f (10 * Y + d) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 10 * (n + 1) = 10 * n + 10 by ring, Finset.sum_range_add, ih,
      Finset.sum_range_succ (fun Y => ∑ d ∈ Finset.range 10, f (10 * Y + d)) n]

theorem sum_four_pow (t : ℕ) :
    ∑ X ∈ Finset.range (10 ^ t), 4 ^ (9 * t - s X) = 349525 ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show (10 : ℕ) ^ (t + 1) = 10 * 10 ^ t by ring, sum_range_ten_mul]
    have hY : ∀ Y ∈ Finset.range (10 ^ t),
        ∑ d ∈ Finset.range 10, 4 ^ (9 * (t + 1) - s (10 * Y + d)) =
          349525 * 4 ^ (9 * t - s Y) := by
      intro Y hYm
      have hsY := s_le_nine_mul t Y (Finset.mem_range.1 hYm)
      have hterm : ∀ d ∈ Finset.range 10,
          4 ^ (9 * (t + 1) - s (10 * Y + d)) = 4 ^ (9 - d) * 4 ^ (9 * t - s Y) := by
        intro d hd
        have hd' := Finset.mem_range.1 hd
        rw [s_ten_mul_add hd', ← pow_add]
        congr 1; omega
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul,
        show (∑ d ∈ Finset.range 10, (4 : ℕ) ^ (9 - d)) = 349525 by simp [Finset.sum_range_succ]]
    rw [Finset.sum_congr rfl hY, ← Finset.mul_sum, ih]
    ring

/-- Markov: 자릿수 합 ≤ σ 인 X < 10^t 의 개수 상한. -/
theorem card_small_digit_sum_le (t σ : ℕ) :
    ((Finset.range (10 ^ t)).filter (fun X => s X ≤ σ)).card * 4 ^ (9 * t - σ) ≤ 349525 ^ t := by
  rw [← sum_four_pow t]
  calc ((Finset.range (10 ^ t)).filter (fun X => s X ≤ σ)).card * 4 ^ (9 * t - σ)
      = ∑ X ∈ (Finset.range (10 ^ t)).filter (fun X => s X ≤ σ), 4 ^ (9 * t - σ) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ X ∈ (Finset.range (10 ^ t)).filter (fun X => s X ≤ σ), 4 ^ (9 * t - s X) :=
        Finset.sum_le_sum fun X hX =>
          Nat.pow_le_pow_right (by norm_num) (by have := (Finset.mem_filter.1 hX).2; omega)
    _ ≤ ∑ X ∈ Finset.range (10 ^ t), 4 ^ (9 * t - s X) :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- 자릿수 합 ≤ σ 인 대표원(< 10^t) 을 갖는 잉여류(mod 2^t) 의 개수 상한. -/
theorem classes_small_le (t σ : ℕ) :
    (((Finset.range (10 ^ t)).filter (fun X => s X ≤ σ)).image (· % 2 ^ t)).card *
      4 ^ (9 * t - σ) ≤ 349525 ^ t :=
  le_trans (Nat.mul_le_mul_right _ Finset.card_image_le) (card_small_digit_sum_le t σ)

/-- **라운드 11 결과**: 100σ ≤ 29t, t ≥ 1 이면 자릿수 합 ≤ σ 로 닿는 잉여류는 2^t 개 미만.
즉 어떤 잉여류 mod 2^t 는 자릿수 합 > 0.29t 인 원소만 갖는다 (사실은 거의 모든 류가 그렇다). -/
theorem classes_small_lt (t σ : ℕ) (ht : 1 ≤ t) (hσ : 100 * σ ≤ 29 * t) :
    (((Finset.range (10 ^ t)).filter (fun X => s X ≤ σ)).image (· % 2 ^ t)).card < 2 ^ t := by
  have h1 := classes_small_le t σ
  have hσ9 : σ ≤ 9 * t := by omega
  have key : 349525 ^ t * 4 ^ σ < 2 ^ t * 4 ^ (9 * t) := by
    have hb : (349525 : ℕ) ^ 100 * 4 ^ 29 < (2 * 4 ^ 9) ^ 100 := by norm_num
    have e1 : (349525 ^ t * 4 ^ σ) ^ 100 = 349525 ^ (100 * t) * 4 ^ (100 * σ) := by
      rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm t 100, mul_comm σ 100]
    have e2 : (349525 : ℕ) ^ (100 * t) * 4 ^ (29 * t) = (349525 ^ 100 * 4 ^ 29) ^ t := by
      rw [mul_pow, ← pow_mul, ← pow_mul]
    have e3 : (((2 : ℕ) * 4 ^ 9) ^ 100) ^ t = (2 ^ t * 4 ^ (9 * t)) ^ 100 := by
      calc (((2 : ℕ) * 4 ^ 9) ^ 100) ^ t = (2 * 4 ^ 9) ^ (100 * t) := (pow_mul _ _ _).symm
        _ = 2 ^ (100 * t) * (4 ^ 9) ^ (100 * t) := mul_pow _ _ _
        _ = 2 ^ (100 * t) * 4 ^ (9 * (100 * t)) := by rw [← pow_mul]
        _ = (2 ^ t) ^ 100 * (4 ^ (9 * t)) ^ 100 := by rw [← pow_mul, ← pow_mul]; ring_nf
        _ = (2 ^ t * 4 ^ (9 * t)) ^ 100 := (mul_pow _ _ _).symm
    have h100 : (349525 ^ t * 4 ^ σ) ^ 100 < (2 ^ t * 4 ^ (9 * t)) ^ 100 := by
      rw [e1, ← e3]
      calc 349525 ^ (100 * t) * 4 ^ (100 * σ) ≤ 349525 ^ (100 * t) * 4 ^ (29 * t) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hσ)
        _ = (349525 ^ 100 * 4 ^ 29) ^ t := e2
        _ < ((2 * 4 ^ 9) ^ 100) ^ t := Nat.pow_lt_pow_left hb (by omega)
    exact (Nat.pow_lt_pow_iff_left (by norm_num)).1 h100
  have hsplit : 4 ^ (9 * t) = 4 ^ (9 * t - σ) * 4 ^ σ := by
    rw [← pow_add, Nat.sub_add_cancel hσ9]
  rw [hsplit] at key
  by_contra hge
  push Not at hge
  have h2 : 2 ^ t * (4 ^ (9 * t - σ) * 4 ^ σ) ≤
      (((Finset.range (10 ^ t)).filter (fun X => s X ≤ σ)).image (· % 2 ^ t)).card *
        4 ^ (9 * t - σ) * 4 ^ σ := by
    rw [← mul_assoc]; exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hge)
  have h3 := Nat.mul_le_mul_right (4 ^ σ) h1
  exact absurd ((h2.trans h3).trans_lt key) (lt_irrefl _)
