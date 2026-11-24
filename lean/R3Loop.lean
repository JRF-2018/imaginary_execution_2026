/-
  時間ループと最適化(report3)の Lean 4 形式化

  Author: JRF / 形式化: Claude Opus 5.5
  Lean 4 v4.34.1 + Mathlib v4.34.1
-/
import Mathlib

set_option autoImplicit false

namespace ImagExec.R3

open Complex

/-! ## 1. メビウス変換の不動点と、そこでの微分(反作用の強さ)

`f x = (a x + b) / (c x + d)`。不動点 `z` は `c z² + (d − a) z − b = 0` を満たす。 -/

/-- メビウス変換。 -/
noncomputable def mob (a b c d : ℂ) (x : ℂ) : ℂ := (a * x + b) / (c * x + d)

/-- 微分: `f' x = (a d − b c) / (c x + d)²`。 -/
theorem mob_hasDerivAt (a b c d x : ℂ) (hx : c * x + d ≠ 0) :
    HasDerivAt (mob a b c d) ((a * d - b * c) / (c * x + d) ^ 2) x := by
  have h1 : HasDerivAt (fun y => a * y + b) a x := by
    simpa using ((hasDerivAt_id x).const_mul a).add_const b
  have h2 : HasDerivAt (fun y => c * y + d) c x := by
    simpa using ((hasDerivAt_id x).const_mul c).add_const d
  have := h1.div h2 hx
  convert this using 1
  · rfl
  · rw [div_eq_div_iff (pow_ne_zero 2 hx) (pow_ne_zero 2 hx)]
    ring

/-- 不動点 `z` での微分は `(a − c z)/(c z + d)` に等しい。これを不動点の **乗数** と呼ぶ。 -/
theorem multiplier_at_fixed (a b c d z : ℂ) (hz : c * z ^ 2 + (d - a) * z - b = 0)
    (hd : c * z + d ≠ 0) :
    (a * d - b * c) / (c * z + d) ^ 2 = (a - c * z) / (c * z + d) := by
  rw [div_eq_div_iff (pow_ne_zero 2 hd) hd]
  linear_combination ((c * z + d) * c) * hz

/-- 不動点 `z` からのずれは、乗数の倍率で伸び縮みする: `f x − z = (x − z)(a − c z)/(c x + d)`。 -/
theorem sub_fixed (a b c d z x : ℂ) (hz : c * z ^ 2 + (d - a) * z - b = 0)
    (hx : c * x + d ≠ 0) :
    mob a b c d x - z = (x - z) * (a - c * z) / (c * x + d) := by
  unfold mob
  rw [div_sub' hx, div_eq_div_iff hx hx]
  linear_combination (-(c * x + d)) * hz

/-! ## 2. 標準形: 二つの不動点で座標を取り直すと、メビウス変換は掛け算になる

二つの不動点 `z₁ ≠ z₂` について `R(x) = (x − z₁)/(x − z₂)` とおくと、`R(f x) = λ R(x)`、
`λ = (a − c z₁)/(a − c z₂)`。`λ` は `z₁` での乗数(微分)に等しい。 -/

/-- 二つの不動点の和(根と係数の関係): `a − c z₂ = c z₁ + d`。 -/
theorem vieta (a b c d z₁ z₂ : ℂ) (h₁ : c * z₁ ^ 2 + (d - a) * z₁ - b = 0)
    (h₂ : c * z₂ ^ 2 + (d - a) * z₂ - b = 0) (hne : z₁ ≠ z₂) : a - c * z₂ = c * z₁ + d := by
  have : (z₁ - z₂) * (c * (z₁ + z₂) + d - a) = 0 := by linear_combination h₁ - h₂
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · linear_combination -h

theorem normal_form (a b c d z₁ z₂ x : ℂ) (h₁ : c * z₁ ^ 2 + (d - a) * z₁ - b = 0)
    (h₂ : c * z₂ ^ 2 + (d - a) * z₂ - b = 0) (hx : c * x + d ≠ 0) :
    (mob a b c d x - z₁) / (mob a b c d x - z₂) =
      (a - c * z₁) / (a - c * z₂) * ((x - z₁) / (x - z₂)) := by
  rw [sub_fixed a b c d z₁ x h₁ hx, sub_fixed a b c d z₂ x h₂ hx]
  rw [div_div_div_cancel_right₀ hx, mul_div_mul_comm, mul_comm]

/-- n 回繰り返すと乗数の n 乗: 列 `x (k+1) = f (x k)` について `R(x n) = λⁿ R(x 0)`。 -/
theorem iterate_ratio (a b c d z₁ z₂ : ℂ) (h₁ : c * z₁ ^ 2 + (d - a) * z₁ - b = 0)
    (h₂ : c * z₂ ^ 2 + (d - a) * z₂ - b = 0)
    (x : ℕ → ℂ) (hrec : ∀ k, x (k + 1) = mob a b c d (x k))
    (hden : ∀ k, c * x k + d ≠ 0) (n : ℕ) :
    (x n - z₁) / (x n - z₂) = ((a - c * z₁) / (a - c * z₂)) ^ n * ((x 0 - z₁) / (x 0 - z₂)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hrec n, normal_form a b c d z₁ z₂ (x n) h₁ h₂ (hden n), ih, pow_succ]
    ring

/-- **定理 F(周期).** 乗数が 1 の n 乗根なら、実行は n 回で元に戻る。 -/
theorem period (a b c d z₁ z₂ : ℂ) (h₁ : c * z₁ ^ 2 + (d - a) * z₁ - b = 0)
    (h₂ : c * z₂ ^ 2 + (d - a) * z₂ - b = 0) (hne : z₁ ≠ z₂)
    (x : ℕ → ℂ) (hrec : ∀ k, x (k + 1) = mob a b c d (x k))
    (hden : ∀ k, c * x k + d ≠ 0) (hnz : ∀ k, x k ≠ z₂) (n : ℕ)
    (hn : ((a - c * z₁) / (a - c * z₂)) ^ n = 1) : x n = x 0 := by
  have h := iterate_ratio a b c d z₁ z₂ h₁ h₂ x hrec hden n
  rw [hn, one_mul] at h
  have e1 : x n - z₂ ≠ 0 := sub_ne_zero.mpr (hnz n)
  have e0 : x 0 - z₂ ≠ 0 := sub_ne_zero.mpr (hnz 0)
  rw [div_eq_div_iff e1 e0] at h
  have hz : z₁ - z₂ ≠ 0 := sub_ne_zero.mpr hne
  have : (x n - x 0) * (z₁ - z₂) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h' | h'
  · exact sub_eq_zero.mp h'
  · exact absurd h' hz

/-! ## 3. 回転: 時間ループの解 ±i と、そこでの微分 e^{2iθ}

角度 θ の回転 `x ↦ (cos θ · x + sin θ)/(−sin θ · x + cos θ)`(= `(x + tan θ)/(1 − x tan θ)`)。
不動点は `±i` で、`i` での乗数は `e^{2iθ}`。 -/

theorem rot_fixed (θ : ℂ) (z : ℂ) (hz : z = I ∨ z = -I) :
    (-sin θ) * z ^ 2 + (cos θ - cos θ) * z - sin θ = 0 := by
  rcases hz with rfl | rfl <;> simp [sq]

/-- **定理 G.** 回転の時間ループの解 `i` での微分(乗数)は `e^{2iθ}`。 -/
theorem rot_multiplier (θ : ℂ) (h : cos θ - sin θ * I ≠ 0) :
    (cos θ - (-sin θ) * I) / ((-sin θ) * I + cos θ) = exp (2 * θ * I) := by
  have hc : (cos θ - sin θ * I) * (cos θ + sin θ * I) = 1 := by
    have := cos_sq_add_sin_sq θ
    linear_combination this - (sin θ) ^ 2 * (I_sq)
  have e : exp (2 * θ * I) = (cos θ + sin θ * I) ^ 2 := by
    rw [show 2 * θ * I = θ * I + θ * I by ring, exp_add, exp_mul_I, sq]
  rw [e, show (-sin θ) * I + cos θ = cos θ - sin θ * I by ring, div_eq_iff h]
  linear_combination (-(cos θ + sin θ * I)) * hc

/-! ## 4. 楕円型: 実の繰り返しは単位円上の回転で、乗数が 1 の冪根のときに限って戻る

係数が実数で、不動点 `z` が実数でない(楕円型)とき、もう一つの不動点は共役 `conj z` で、
乗数 `λ = (a − c z)/(a − c conj z)` の絶対値は 1。座標 `R(x) = (x − z)/(x − conj z)` は実数直線を単位円に移し、
実の繰り返しは単位円上の角度 `arg λ` の回転になる。実の繰り返しが元に戻るのは `λⁿ = 1` のときに限る。 -/

theorem conj_fixed (a b c d : ℝ) (z : ℂ) (hz : (c : ℂ) * z ^ 2 + ((d : ℂ) - a) * z - b = 0) :
    (c : ℂ) * (starRingEnd ℂ z) ^ 2 + ((d : ℂ) - a) * starRingEnd ℂ z - b = 0 := by
  have := congrArg (starRingEnd ℂ) hz
  simpa [map_sub, map_add, map_mul, map_pow, Complex.conj_ofReal] using this

theorem conj_ne (z : ℂ) (hzi : z.im ≠ 0) : z ≠ starRingEnd ℂ z := by
  intro h
  apply hzi
  have := congrArg Complex.im h
  simp at this
  linarith

/-- 実数 `x` について `|x − z| = |x − conj z|`。よって `R` は実数直線を単位円に移す。 -/
theorem real_to_circle (x : ℝ) (z : ℂ) (hzi : z.im ≠ 0) :
    ‖((x : ℂ) - z) / ((x : ℂ) - starRingEnd ℂ z)‖ = 1 := by
  have hne : (x : ℂ) - starRingEnd ℂ z ≠ 0 := by
    intro h
    apply hzi
    have := congrArg Complex.im h
    simp at this
    linarith
  rw [norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.mpr hne)]
  have : (x : ℂ) - starRingEnd ℂ z = starRingEnd ℂ ((x : ℂ) - z) := by simp
  rw [this, Complex.norm_conj]

/-- **楕円型の乗数は絶対値 1.** -/
theorem elliptic_unit (a c : ℝ) (z : ℂ) (hc : c ≠ 0) (hzi : z.im ≠ 0) :
    ‖((a : ℂ) - c * z) / ((a : ℂ) - c * starRingEnd ℂ z)‖ = 1 := by
  have hw : (a : ℂ) - c * z ≠ 0 := by
    intro h
    apply hzi
    have := congrArg Complex.im h
    simp at this
    rcases this with h1 | h1
    · exact absurd h1 hc
    · exact h1
  have : (a : ℂ) - c * starRingEnd ℂ z = starRingEnd ℂ ((a : ℂ) - c * z) := by simp
  rw [this, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hw)]

/-- **定理 F′(戻るのは乗数が 1 の冪根のときに限る).** 楕円型のメビウス変換の実の繰り返しについて、
`n` 回で元の値に戻る ⇔ 乗数の `n` 乗が 1。乗数が 1 の冪根でなければ、実の繰り返しは決して元の値に戻らない。 -/
theorem elliptic_return (a b c d : ℝ) (z : ℂ) (hz : (c : ℂ) * z ^ 2 + ((d : ℂ) - a) * z - b = 0)
    (hzi : z.im ≠ 0) (x : ℕ → ℝ) (hrec : ∀ k, ((x (k + 1) : ℝ) : ℂ) = mob a b c d (x k))
    (hden : ∀ k, (c : ℂ) * x k + d ≠ 0) (n : ℕ) :
    x n = x 0 ↔ (((a : ℂ) - c * z) / ((a : ℂ) - c * starRingEnd ℂ z)) ^ n = 1 := by
  have h2 := conj_fixed a b c d z hz
  have hne := conj_ne z hzi
  have hnz : ∀ k, ((x k : ℝ) : ℂ) ≠ starRingEnd ℂ z := by
    intro k h
    apply hzi
    have := congrArg Complex.im h
    simp at this
    linarith
  have hit := iterate_ratio a b c d z (starRingEnd ℂ z) hz h2 (fun k => (x k : ℂ)) hrec hden n
  constructor
  · intro hx
    rw [hx] at hit
    have hR : ((x 0 : ℂ) - z) / ((x 0 : ℂ) - starRingEnd ℂ z) ≠ 0 := by
      intro h0
      have := real_to_circle (x 0) z hzi
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    have := hit.symm
    rw [mul_eq_right₀ hR] at this
    exact this
  · intro hl
    exact_mod_cast period a b c d z (starRingEnd ℂ z) hz h2 hne (fun k => (x k : ℂ)) hrec hden hnz n hl

/-! ## 5. 双曲型: 乗数の絶対値が 1 より小さければ、傾けても戻る

二つの不動点 `z₁ ≠ z₂` の乗数 `λ` が `|λ| < 1` なら、`z₂` を通らない繰り返しは `z₁` に収束する
(「ある方向に傾けると、反作用的な力が生じる」の正確な形)。 -/

theorem converge (a b c d z₁ z₂ : ℂ) (h₁ : c * z₁ ^ 2 + (d - a) * z₁ - b = 0)
    (h₂ : c * z₂ ^ 2 + (d - a) * z₂ - b = 0) (hne : z₁ ≠ z₂)
    (x : ℕ → ℂ) (hrec : ∀ k, x (k + 1) = mob a b c d (x k))
    (hden : ∀ k, c * x k + d ≠ 0) (hnz : ∀ k, x k ≠ z₂)
    (hl : ‖(a - c * z₁) / (a - c * z₂)‖ < 1) :
    Filter.Tendsto x Filter.atTop (nhds z₁) := by
  set lam := (a - c * z₁) / (a - c * z₂)
  set R0 := (x 0 - z₁) / (x 0 - z₂)
  have hR : ∀ n, (x n - z₁) / (x n - z₂) = lam ^ n * R0 :=
    iterate_ratio a b c d z₁ z₂ h₁ h₂ x hrec hden
  -- x n = (z₁ − r z₂)/(1 − r)、r = λⁿ R0
  have hx : ∀ n, x n = (z₁ - lam ^ n * R0 * z₂) / (1 - lam ^ n * R0) := by
    intro n
    have e := hR n
    have hd : x n - z₂ ≠ 0 := sub_ne_zero.mpr (hnz n)
    have h1 : 1 - lam ^ n * R0 ≠ 0 := by
      rw [← e]
      intro h
      apply hne
      have : (x n - z₁) / (x n - z₂) = 1 := by linear_combination -h
      rw [div_eq_one_iff_eq hd] at this
      linear_combination -this
    rw [eq_div_iff h1, ← e]
    field_simp
    ring
  have hpow : Filter.Tendsto (fun n => lam ^ n * R0) Filter.atTop (nhds 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hl
    simpa using this.mul_const R0
  have hlim : Filter.Tendsto (fun n => (z₁ - lam ^ n * R0 * z₂) / (1 - lam ^ n * R0))
      Filter.atTop (nhds ((z₁ - 0 * z₂) / (1 - 0))) := by
    apply Filter.Tendsto.div
    · exact tendsto_const_nhds.sub (hpow.mul_const z₂)
    · exact tendsto_const_nhds.sub hpow
    · simp
  simp only [zero_mul, sub_zero, div_one] at hlim
  exact (funext hx ▸ hlim : _)

/-! ## 6. リング発振器: ±1 で書けば線形で、乗数(固有値)はどれも 1 でない

インバータ `N` 個(`N` 奇数)の輪。各段は 1 時刻遅れて前段の否定を出す。状態を ±1 で書けば否定は −1 倍なので、
一時刻の写像は線形 `s ↦ −C s`(`C` は巡回シフト)。`N` 時刻で全体の否定になり(自己無撞着な状態はない)、
`2N` 時刻で元に戻る。 -/

/-- 一時刻: 段 `k` は前段 `k − 1` の否定(±1 で書いて −1 倍)を出す。 -/
def ringStep (N : ℕ) (s : ZMod N → ℤ) : ZMod N → ℤ := fun k => -s (k - 1)

theorem ringStep_iter (N : ℕ) (s : ZMod N → ℤ) (m : ℕ) (k : ZMod N) :
    (ringStep N)^[m] s k = (-1) ^ m * s (k - m) := by
  induction m generalizing k with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ringStep, ih]
    push_cast
    ring_nf

/-- **リング発振器(N 奇数).** `N` 時刻で全体が否定になる(自己無撞着な状態はない)。 -/
theorem ring_N (N : ℕ) (hN : Odd N) (s : ZMod N → ℤ) :
    (ringStep N)^[N] s = fun k => - s k := by
  funext k
  rw [ringStep_iter, ZMod.natCast_self, sub_zero, hN.neg_one_pow]
  ring

/-- **リング発振器.** `2N` 時刻で元に戻る。 -/
theorem ring_2N (N : ℕ) (s : ZMod N → ℤ) : (ringStep N)^[2 * N] s = s := by
  funext k
  rw [ringStep_iter]
  have : ((2 * N : ℕ) : ZMod N) = 0 := by
    rw [Nat.cast_mul, ZMod.natCast_self, mul_zero]
  rw [this, sub_zero, pow_mul]
  simp

/-- 状態がどれも 0 でない(±1 の)とき、`N` 時刻後の状態は元と違う: 輪は止まらない。 -/
theorem ring_no_fixed (N : ℕ) (hN : Odd N) (s : ZMod N → ℤ) (k : ZMod N) (hk : s k ≠ 0) :
    (ringStep N)^[N] s ≠ s := by
  intro h
  have := congrFun h k
  rw [ring_N N hN] at this
  exact hk (by linarith)

end ImagExec.R3

#print axioms ImagExec.R3.mob_hasDerivAt
#print axioms ImagExec.R3.multiplier_at_fixed
#print axioms ImagExec.R3.period
#print axioms ImagExec.R3.rot_multiplier
#print axioms ImagExec.R3.elliptic_unit
#print axioms ImagExec.R3.elliptic_return
#print axioms ImagExec.R3.converge
#print axioms ImagExec.R3.ring_N
#print axioms ImagExec.R3.ring_2N
#print axioms ImagExec.R3.ring_no_fixed
