/-
  部品の意味と計算量(report2)の Lean 4 形式化

  Author: JRF / 形式化: Claude Opus 5.5
  Lean 4 v4.34.1 + Mathlib v4.34.1
-/
import Mathlib

set_option autoImplicit false

namespace ImagExec.R2

/-! ## 1. 定理 C: 実実行だけの意味は、並列合成について合成的でない

状態は `Fin 3`。プロセスは CS の関数の列 `List (Fin 3 → Fin 3)`(記憶のないプロセス)。
並列合成の結果は、二つの列のすべてのインタリーブを初期状態 0 から実行した最終状態の集合。
プロセスを単独で(誰にも邪魔されずに)走らせたときの全体の関数 `comp` を「実実行だけの意味」とする。 -/

/-- 二つの列のインタリーブをすべて並べる。 -/
def inter {α : Type} : List α → List α → List (List α)
  | [], ys => [ys]
  | xs, [] => [xs]
  | x :: xs, y :: ys => (inter xs (y :: ys)).map (x :: ·) ++ (inter (x :: xs) ys).map (y :: ·)

/-- 関数の列を順に施す。 -/
def runSeq (fs : List (Fin 3 → Fin 3)) (s : Fin 3) : Fin 3 := fs.foldl (fun s f => f s) s

/-- 並列合成 P ∥ Q の観測: 初期状態 0 からの最終状態の集合。 -/
def results (P Q : List (Fin 3 → Fin 3)) : Finset (Fin 3) :=
  ((inter P Q).map (fun fs => runSeq fs 0)).toFinset

/-- 実実行だけの意味: 単独で走らせたときの全体の関数。 -/
def comp (P : List (Fin 3 → Fin 3)) : Fin 3 → Fin 3 := runSeq P

/-- `P₁` は一つの CS で 2 を書く。`P₂` は 1 を書いてから 1 を足す。単独では区別できない。 -/
def P₁ : List (Fin 3 → Fin 3) := [fun _ => 2]
def P₂ : List (Fin 3 → Fin 3) := [fun _ => 1, fun x => x + 1]
/-- 文脈 `Q` は一つの CS で 0 を書く。 -/
def Q : List (Fin 3 → Fin 3) := [fun _ => 0]

theorem comp_eq : comp P₁ = comp P₂ := by
  funext s; fin_cases s <;> rfl

/-- `P₂ ∥ Q` では、`Q` が二つの CS の間に入ると最終状態 1 が出る。`P₁ ∥ Q` では出ない。 -/
theorem one_mem : (1 : Fin 3) ∈ results P₂ Q := by
  simp [results, inter, P₂, Q, runSeq]

theorem one_not_mem : (1 : Fin 3) ∉ results P₁ Q := by
  simp [results, inter, P₁, Q, runSeq]

theorem results_ne : results P₁ Q ≠ results P₂ Q := fun h => one_not_mem (h ▸ one_mem)

/-- **定理 C.** 並列合成の結果を、各プロセスの「実実行だけの意味」から計算する関数 `F` は存在しない。 -/
theorem not_compositional :
    ¬ ∃ F : (Fin 3 → Fin 3) → (Fin 3 → Fin 3) → Finset (Fin 3),
      ∀ P Q, results P Q = F (comp P) (comp Q) := by
  rintro ⟨F, hF⟩
  apply results_ne
  rw [hF P₁ Q, hF P₂ Q, comp_eq]

/-- 一方、各 CS の関数の列そのもの(各 lock でどんな状態を受け取ってもどう振る舞うか。
「虚の入力」を含む意味)からは、並列合成の結果は定義によって計算できる。 -/
theorem compositional_full : ∃ F : List (Fin 3 → Fin 3) → List (Fin 3 → Fin 3) → Finset (Fin 3),
    ∀ P Q, results P Q = F P Q := ⟨results, fun _ _ => rfl⟩

/-! ## 2. 定理 E: 世界の数 = 1 + 余分に再開した回数

有限の集合 `V` の各要素(CS、または継続を再開してできた世界)が、どこから続いたかを
`par : V → Option V` で表す(`none` は最初)。どの要素からも続かないものが葉(最後まで行った世界)。
葉の数は、1 + Σ(各点から続いたものの数 − 1)(続いたものが一つ以上ある点について)に等しい。
継続の言葉では、捕まえた時点 `x` から続いた回数(通常の return を含む)が `x` のファイバーの大きさで、
**世界の数 = 1 + 継続を余分に再開した回数**。一度しか再開しない(線形な)継続だけなら、世界は一つ。 -/

variable {V : Type} [Fintype V] [DecidableEq V]

def leaves (par : V → Option V) : Finset (Option V) :=
  Finset.univ.filter (fun x => ∀ v, par v ≠ x)

/-- 点 `x` から続いたものの数。 -/
def fanout (par : V → Option V) (x : Option V) : ℕ :=
  (Finset.univ.filter (fun v => par v = x)).card

theorem card_leaves (par : V → Option V) :
    (leaves par).card + (Finset.univ.image par).card = Fintype.card V + 1 := by
  have h : leaves par = Finset.univ \ Finset.univ.image par := by
    ext x; simp [leaves]
  rw [h, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Fintype.card_option]
  have := Finset.card_le_univ (Finset.univ.image par)
  rw [Fintype.card_option] at this
  omega

theorem sum_fanout (par : V → Option V) :
    ∑ x ∈ Finset.univ.image par, fanout par x = Fintype.card V := by
  rw [← Finset.card_univ, Finset.card_eq_sum_card_image par Finset.univ]
  rfl

/-- **定理 E.** 葉の数 = 1 + Σ_x (x から続いたものの数 − 1)。 -/
theorem thmE (par : V → Option V) :
    (leaves par).card = 1 + ∑ x ∈ Finset.univ.image par, (fanout par x - 1) := by
  have hc := card_leaves par
  have hs := sum_fanout par
  have hpos : ∀ x ∈ Finset.univ.image par, 1 ≤ fanout par x := by
    intro x hx
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hx
    unfold fanout
    exact Finset.card_pos.mpr ⟨v, by simp⟩
  have : ∑ x ∈ Finset.univ.image par, (fanout par x - 1) + (Finset.univ.image par).card =
      ∑ x ∈ Finset.univ.image par, fanout par x := by
    rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x hx => Nat.sub_add_cancel (hpos x hx))
  omega

/-! ## 3. 定理 E′: スケジューラで作れる実行は、rf ∪ po が循環しないものに限る

一度しか再開できない継続(ジェネレータ)でプロセスを動かし、状態の値はいくらでも保存して配れるスケジューラを考える。
CS `v` を実行できるのは、`v` が読む状態を書いた CS(`rf v`)と、同じプロセスで `v` より前の CS(`po`)が、
すでに実行されたときだけである。スケジューラの実行順(メタな時刻)を単射 `τ` で表す。
そういう順序がある ⇔ rf ∪ po が循環しない(report0 の階層の I 以下)。
時間逆行・時間ループ(B・L)の rf は、どんなスケジューラでも作れず、自己無撞着性(report0 定理 4)でしか存在しない。 -/

section Sched

variable {V : Type} [Fintype V]

/-- rf ∪ po の辺。 -/
def EdgeRP (rf : V → Option V) (po : V → V → Prop) (a b : V) : Prop := rf b = some a ∨ po a b

open Relation in
/-- **定理 E′.** スケジューラの実行順があるのは、rf ∪ po が循環しないときに限る。 -/
theorem sched_iff (rf : V → Option V) (po : V → V → Prop) :
    (∃ τ : V → ℕ, Function.Injective τ ∧ ∀ a b, EdgeRP rf po a b → τ a < τ b) ↔
      ∀ a, ¬ TransGen (EdgeRP rf po) a a := by
  classical
  constructor
  · rintro ⟨τ, -, hτ⟩ a h
    have : ∀ x y, TransGen (EdgeRP rf po) x y → τ x < τ y := by
      intro x y hxy
      induction hxy with
      | single h => exact hτ _ _ h
      | tail _ h ih => exact ih.trans (hτ _ _ h)
    exact lt_irrefl _ (this a a h)
  · intro hac
    -- 祖先の数で並べ、同じ数のものは番号で並べる
    let anc : V → ℕ := fun v => (Finset.univ.filter (fun u => TransGen (EdgeRP rf po) u v)).card
    let e := Fintype.equivFin V
    let N := Fintype.card V
    have hanc : ∀ a b, EdgeRP rf po a b → anc a < anc b := by
      intro a b hab
      apply Finset.card_lt_card
      refine ⟨fun u hu => ?_, fun hsub => ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
        exact hu.tail hab
      · have : a ∈ Finset.univ.filter (fun u => TransGen (EdgeRP rf po) u b) := by
          simp [TransGen.single hab]
        have := hsub this
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
        exact hac a this
    refine ⟨fun v => anc v * N + (e v : ℕ), ?_, ?_⟩
    · intro a b h
      have ha : (e a : ℕ) < N := (e a).isLt
      have hb : (e b : ℕ) < N := (e b).isLt
      have hmod : (e a : ℕ) = (e b : ℕ) := by
        have h1 := congrArg (· % N) h
        simp only at h1
        rwa [Nat.mul_add_mod_of_lt ha, Nat.mul_add_mod_of_lt hb] at h1
      exact e.injective (Fin.ext hmod)
    · intro a b hab
      have hlt := hanc a b hab
      have ha : (e a : ℕ) < N := (e a).isLt
      calc anc a * N + (e a : ℕ) < anc a * N + N := by omega
        _ = (anc a + 1) * N := by ring
        _ ≤ anc b * N := Nat.mul_le_mul_right _ hlt
        _ ≤ anc b * N + (e b : ℕ) := Nat.le_add_right _ _

end Sched

end ImagExec.R2

#print axioms ImagExec.R2.not_compositional
#print axioms ImagExec.R2.thmE
#print axioms ImagExec.R2.sched_iff
