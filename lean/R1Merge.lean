/-
  虚実行と合流(report1)の Lean 4 形式化

  Author: JRF / 形式化: Claude Opus 5.5
  Lean 4 v4.34.1 + Mathlib v4.34.1
-/
import Mathlib

set_option autoImplicit false
set_option linter.deprecated false

namespace ImagExec.R1

open Classical

variable {X V : Type}

/-! ## 1. トランザクションと合流

状態は変数 `X` から値 `V` への関数。トランザクション `t` は読み集合 `R`、書き集合 `W` と、
スナップショットから書き込む値を計算する `f` を持つ。`f` は `R` の値だけに依存する(`dep`)。 -/

structure Txn (X V : Type) where
  R : Set X
  W : Set X
  f : (X → V) → X → V
  dep : ∀ s s' : X → V, (∀ x ∈ R, s x = s' x) → ∀ x ∈ W, f s x = f s' x

/-- 合流: スナップショット `snap` から計算した書き込みを、現在の状態 `cur` に上書きする
(書き集合の外は `cur` のまま)。`snap = cur` なら普通の(直列の)実行。 -/
noncomputable def merge (t : Txn X V) (snap cur : X → V) : X → V :=
  fun x => if x ∈ t.W then t.f snap x else cur x

/-! ## 2. 定理 A: 合流が直列実行と区別できない条件

確定の列 `k = 0, 1, 2, …`。`k` 番目に確定するトランザクション `ts k` は、版 `js k`(それまでに
確定した数、`js k ≤ k`)をスナップショットとして読み、版 `k` に合流して版 `k+1` を作る。
状態の列 `st` はこの漸化式を満たすものとして与える。直列実行 `ser` はスナップショットが常に最新のもの。 -/

/-- 版 `j` から版 `k` までに、書き集合が `x` を含む確定がなければ、`x` の値は変わらない。 -/
theorem unchanged (ts : ℕ → Txn X V) (js : ℕ → ℕ) (st : ℕ → X → V)
    (hst : ∀ k, st (k + 1) = merge (ts k) (st (js k)) (st k)) (x : X) (j : ℕ) :
    ∀ k, j ≤ k → (∀ i, j ≤ i → i < k → x ∉ (ts i).W) → st k x = st j x := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => intro _; rfl
  | succ k hjk ih =>
    intro h
    rw [hst k]
    simp only [merge]
    rw [if_neg (h k hjk (Nat.lt_succ_self k))]
    exact ih (fun i hi hik => h i hi (Nat.lt_succ_of_lt hik))

/-- **定理 A.** 各トランザクションの読み集合が、自分のスナップショット以後・自分の確定以前に
確定した相手の書き集合と交わらない(楽観的並行制御の後ろ向き検証)なら、確定順の直列実行と
すべての版が一致する。とくに、各トランザクションが読んだ値も一致する。 -/
theorem thmA (ts : ℕ → Txn X V) (js : ℕ → ℕ) (hjs : ∀ k, js k ≤ k)
    (st ser : ℕ → X → V) (h0 : ser 0 = st 0)
    (hst : ∀ k, st (k + 1) = merge (ts k) (st (js k)) (st k))
    (hser : ∀ k, ser (k + 1) = merge (ts k) (ser k) (ser k))
    (hval : ∀ k i, js k ≤ i → i < k → ∀ x ∈ (ts k).R, x ∉ (ts i).W) :
    (∀ k, st k = ser k) ∧ (∀ k, ∀ x ∈ (ts k).R, st (js k) x = ser k x) := by
  -- スナップショットと最新の版は、読み集合の上で一致する
  have agree : ∀ k, ∀ x ∈ (ts k).R, st (js k) x = st k x := fun k x hx =>
    (unchanged ts js st hst x (js k) k (hjs k) (fun i hi hik => hval k i hi hik x hx)).symm
  have main : ∀ k, st k = ser k := by
    intro k
    induction k with
    | zero => exact h0.symm
    | succ k ih =>
      rw [hst k, hser k, ← ih]
      funext x
      simp only [merge]
      split_ifs with hx
      · exact (ts k).dep _ _ (agree k) x hx
      · rfl
  exact ⟨main, fun k x hx => (agree k x hx).trans (congrFun (main k) x)⟩

/-- 系: 共通のスナップショット `s` から出た二つのトランザクションの合流は、
`T₂` が `T₁` の書いた変数を読まなければ、直列実行 `T₁; T₂` と一致する。 -/
theorem two_txn (t₁ t₂ : Txn X V) (s : X → V) (h : ∀ x ∈ t₂.R, x ∉ t₁.W) :
    merge t₂ s (merge t₁ s s) = merge t₂ (merge t₁ s s) (merge t₁ s s) := by
  funext x
  simp only [merge]
  split_ifs with h2
  · apply t₂.dep
    · intro y hy
      simp only [merge, if_neg (h y hy)]
    · exact h2
  all_goals rfl

/-! ## 3. write skew: 書き集合が交わらなくても、直列実行と一致しない

当直の医師が二人(`x`, `y`、1 なら当直)。どちらのトランザクションも「二人とも当直なら自分を外す」。
共通のスナップショットから両方を確定させると(スナップショット分離の first-committer-wins は
書き集合が交わらないので通す)、二人とも外れる。直列ならどちらの順でも一人は残る。 -/

/-- 変数: `false` が x、`true` が y。 -/
def offDuty (me : Bool) : Txn Bool ℕ where
  R := Set.univ
  W := {me}
  f := fun s v => if v = me ∧ s false + s true ≥ 2 then 0 else s v
  dep := by
    intro s s' h x _
    have h1 := h false (Set.mem_univ _)
    have h2 := h true (Set.mem_univ _)
    have h3 := h x (Set.mem_univ _)
    simp only [h1, h2, h3]

theorem write_skew :
    let s : Bool → ℕ := fun _ => 1
    let si := merge (offDuty true) s (merge (offDuty false) s s)              -- 合流
    let ser₁ := merge (offDuty true) (merge (offDuty false) s s) (merge (offDuty false) s s)
    let ser₂ := merge (offDuty false) (merge (offDuty true) s s) (merge (offDuty true) s s)
    (offDuty false).W ∩ (offDuty true).W = ∅ ∧
      si false + si true = 0 ∧ ser₁ false + ser₁ true = 1 ∧ ser₂ false + ser₂ true = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext x; simp [offDuty]
  all_goals simp [merge, offDuty]

/-! ## 4. 定理 B: スナップショット分離の危険構造(Fekete ら 2005)

トランザクション `t` は時刻 `s t` に開始(スナップショットをとる)し、`c t` に確定する。事象の時刻はどれも違う。
スナップショット分離(SI)の二つの規則:

* **スナップショット**: `b` が読むのは、`s b` より前に確定した版だけ。
* **first-committer-wins**: 同じ変数を書く二つのトランザクションは、時間が重ならない。

依存グラフ(Adya 1999)の辺を、版の言葉で次のように書く(Adya の定義の辺は、どれもこの条件を満たす)。

* `ww a b`: `a` と `b` が同じ変数を書き、`a` の版が先(`c a < c b`)。
* `wr a b`: `b` が読んだ版を `a` が書いた。`b` に見えるので `c a < s b`。
* `rw a b`: `a` が読んだ変数の、`a` に見えたどの版より後の版を `b` が書いた(`a` は `b` の書き込みを見ていない)。 -/

/-- SI の実行の時刻と読み書き。 -/
structure SIRun (T X : Type) where
  s : T → ℕ
  c : T → ℕ
  W : T → Set X
  R : T → Set X
  sc : ∀ t, s t < c t
  dist : ∀ t u, s t ≠ c u
  fcw : ∀ a b x, a ≠ b → x ∈ W a → x ∈ W b → c a < s b ∨ c b < s a

inductive Kind
  | ww
  | wr
  | rw
  deriving DecidableEq

variable {T X : Type}

/-- 依存グラフの辺。 -/
def Edge (M : SIRun T X) : Kind → T → T → Prop
  | Kind.ww, a, b => a ≠ b ∧ ∃ x, x ∈ M.W a ∧ x ∈ M.W b ∧ M.c a < M.c b
  | Kind.wr, a, b => a ≠ b ∧ ∃ x, x ∈ M.R b ∧ x ∈ M.W a ∧ M.c a < M.s b
  | Kind.rw, a, b => a ≠ b ∧ ∃ x, x ∈ M.R a ∧ x ∈ M.W b ∧
      ∀ w, x ∈ M.W w → M.c w < M.s a → M.c w < M.c b

/-- 時間が重なる(並行に動いた)。 -/
def Concurrent (M : SIRun T X) (a b : T) : Prop := M.s a < M.c b ∧ M.s b < M.c a

/-- rw 以外の辺は、前のトランザクションの確定が後のトランザクションの開始より前。 -/
theorem nonrw_time (M : SIRun T X) {k : Kind} {a b : T} (hk : k ≠ Kind.rw) (h : Edge M k a b) :
    M.c a < M.s b := by
  cases k with
  | ww =>
    obtain ⟨hab, x, ha, hb, hc⟩ := h
    rcases M.fcw a b x hab ha hb with h1 | h1
    · exact h1
    · have := M.sc a; omega
  | wr => exact h.2.choose_spec.2.2
  | rw => exact absurd rfl hk

/-- rw の辺は、前のトランザクションの開始が後のトランザクションの確定より前(`a` は `b` を見ていない)。 -/
theorem rw_time (M : SIRun T X) {a b : T} (h : Edge M Kind.rw a b) : M.s a < M.c b := by
  obtain ⟨_, x, _, hb, hall⟩ := h
  rcases lt_or_gt_of_ne (M.dist a b) with h1 | h1
  · exact h1
  · exact absurd (hall b hb h1) (lt_irrefl _)

/-- 周期 `m` の列。 -/
theorem periodic_mod {α : Type} (v : ℕ → α) (m : ℕ) (hv : ∀ i, v (i + m) = v i) (j : ℕ) :
    v j = v (j % m) := by
  have : ∀ q r, v (r + m * q) = v r := by
    intro q
    induction q with
    | zero => intro r; simp
    | succ q ih => intro r; rw [Nat.mul_succ, ← Nat.add_assoc, hv, ih]
  conv_lhs => rw [← Nat.mod_add_div j m]
  exact this _ _

/-- **定理 B(Fekete ら 2005、Cahill ら 2008 の形).** SI のもとで、依存グラフの循環
(長さ `m`、`i` 番目の辺は `v i` から `v (i+1)`)には、続く二本の rw 辺 `v i →rw v (i+1) →rw v (i+2)` があり、
`v (i+2)` は循環の中で最初に確定したトランザクションで、どちらの rw 辺の両端も時間が重なっている。 -/
theorem thmB (M : SIRun T X) (v : ℕ → T) (k : ℕ → Kind) (m : ℕ) (hm : 1 ≤ m)
    (hv : ∀ i, v (i + m) = v i) (he : ∀ i, Edge M (k i) (v i) (v (i + 1))) :
    ∃ i, k i = Kind.rw ∧ k (i + 1) = Kind.rw ∧
      Concurrent M (v i) (v (i + 1)) ∧ Concurrent M (v (i + 1)) (v (i + 2)) ∧
      ∀ j, M.c (v (i + 2)) ≤ M.c (v j) := by
  obtain ⟨j0, -, hj0⟩ := Finset.exists_min_image (Finset.range m) (fun j => M.c (v j))
    ⟨0, Finset.mem_range.mpr (by omega)⟩
  have hmin : ∀ j, M.c (v j0) ≤ M.c (v j) := by
    intro j
    rw [periodic_mod v m hv j]
    exact hj0 _ (Finset.mem_range.mpr (Nat.mod_lt _ (by omega)))
  set i := j0 + 2 * m - 2 with hi
  have h2 : v (i + 2) = v j0 := by
    have : i + 2 = j0 + m + m := by omega
    rw [this, hv, hv]
  -- 最初に確定した v (i+2) に入る辺は rw
  have k1 : k (i + 1) = Kind.rw := by
    by_contra hk
    have := nonrw_time M hk (he (i + 1))
    have := M.sc (v (i + 2))
    have := hmin (i + 1)
    rw [h2] at *
    omega
  have t1 := rw_time M (k1 ▸ he (i + 1))
  -- その前の辺も rw
  have k0 : k i = Kind.rw := by
    by_contra hk
    have := nonrw_time M hk (he i)
    have := hmin i
    rw [h2] at t1
    omega
  have t0 := rw_time M (k0 ▸ he i)
  refine ⟨i, k0, k1, ⟨t0, ?_⟩, ⟨t1, ?_⟩, fun j => h2 ▸ hmin j⟩
  · have := hmin i
    rw [h2] at t1
    omega
  · have := M.sc (v (i + 2))
    have := hmin (i + 1)
    rw [h2] at *
    omega

/-- **系(SSI).** rw の辺が入ってきて rw の辺が出ていき、どちらも時間の重なる相手との辺であるような
トランザクション(危険構造の要)を一つも許さなければ、依存グラフに循環はない(直列化可能)。 -/
theorem ssi_safe (M : SIRun T X)
    (hnp : ∀ u t w, Edge M Kind.rw u t → Edge M Kind.rw t w →
      Concurrent M u t → Concurrent M t w → False)
    (v : ℕ → T) (k : ℕ → Kind) (m : ℕ) (hm : 1 ≤ m)
    (hv : ∀ i, v (i + m) = v i) (he : ∀ i, Edge M (k i) (v i) (v (i + 1))) : False := by
  obtain ⟨i, k0, k1, c0, c1, -⟩ := thmB M v k m hm hv he
  exact hnp _ _ _ (k0 ▸ he i) (k1 ▸ he (i + 1)) c0 c1

end ImagExec.R1

#print axioms ImagExec.R1.thmA
#print axioms ImagExec.R1.two_txn
#print axioms ImagExec.R1.write_skew
#print axioms ImagExec.R1.thmB
#print axioms ImagExec.R1.ssi_safe
