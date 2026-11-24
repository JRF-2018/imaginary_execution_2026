/-
  report0 定理 4(実行の決まり方)の Lean 4 形式化

  Author: JRF / 形式化: Claude Opus 5.5
  Lean 4 v4.34.1 + Mathlib v4.34.1
-/
import Mathlib

set_option autoImplicit false

namespace ImagExec.T4

open Relation Classical

/-! ## 1. モデル

CS の集合 `V`(有限)。`rf v` は CS `v` が読む状態を書いた CS(`none` は初期状態)。`po w u` は
「`w` は `u` と同じプロセスで `u` より前」。CS `u` の出力は、`u` 自身と、同じプロセスでそれより前の CS が
受け取った入力だけで決まる(局所変数がある)。実行とは、各 CS が受け取る入力の組 `x` で、
「`v` の入力 = `rf v` の出力」を満たすもの。 -/

structure Frame (V S : Type) where
  rf : V → Option V
  po : V → V → Prop
  init : S

/-- 各 CS の出力。`u` の出力は、`u` と `u` より前の CS の入力だけで決まる。 -/
structure Proc {V S : Type} (F : Frame V S) where
  out : V → (V → S) → S
  loc : ∀ u x y, (∀ w, w = u ∨ F.po w u → x w = y w) → out u x = out u y

variable {V S : Type}

/-- `v` が受け取る入力(`rf v` の出力、または初期状態)。 -/
def inp {F : Frame V S} (P : Proc F) (x : V → S) (v : V) : S :=
  (F.rf v).elim F.init (fun u => P.out u x)

/-- 実行: 一周して整合する入力の組。 -/
def IsExec {F : Frame V S} (P : Proc F) (x : V → S) : Prop := ∀ v, x v = inp P x v

/-- rf ∪ po の辺。 -/
def E (F : Frame V S) (a b : V) : Prop := F.rf b = some a ∨ F.po a b

/-- 入力の依存: `v` の入力は、`w` の入力に依存しうる(`w` から `rf v` までプロセスの中で進む)。 -/
def D (F : Frame V S) (w v : V) : Prop := ∃ u, F.rf v = some u ∧ (w = u ∨ F.po w u)

theorem inp_loc {F : Frame V S} (P : Proc F) (x y : V → S) (v : V)
    (h : ∀ w, D F w v → x w = y w) : inp P x v = inp P y v := by
  unfold inp
  cases hv : F.rf v with
  | none => rfl
  | some u =>
    exact P.loc u x y (fun w hw => h w ⟨u, hv, hw⟩)

theorem D_sub_E (F : Frame V S) {w v : V} (h : D F w v) : TransGen (E F) w v := by
  obtain ⟨u, hv, hw | hw⟩ := h
  · subst hw
    exact TransGen.single (Or.inl hv)
  · exact TransGen.tail (TransGen.single (Or.inr hw)) (Or.inl hv)

/-! ## 2. 定理 4 (1): rf ∪ po が循環しなければ、実行はちょうど一つ -/

theorem thm4_1 [Finite V] (F : Frame V S) (P : Proc F)
    (hac : ∀ a, ¬ TransGen (E F) a a) : ∃! x, IsExec P x := by
  -- 依存 D の推移閉包は狭義の順序なので、有限集合の上で整礎
  have hirr : ∀ a, ¬ TransGen (D F) a a := by
    intro a h
    apply hac a
    have key : ∀ b c, TransGen (D F) b c → TransGen (E F) b c := by
      intro b c hbc
      induction hbc with
      | single h => exact D_sub_E F h
      | tail _ h ih => exact ih.trans (D_sub_E F h)
    exact key a a h
  have : IsTrans V (TransGen (D F)) := ⟨fun _ _ _ => TransGen.trans⟩
  have : Std.Irrefl (TransGen (D F)) := ⟨hirr⟩
  have hwfT : WellFounded (TransGen (D F)) := Finite.wellFounded_of_trans_of_irrefl _
  have hwf : WellFounded (D F) := Subrelation.wf (fun h => TransGen.single h) hwfT
  -- 存在: D に沿った整礎な再帰で、前から順に計算する
  let x : V → S := hwf.fix (fun v rec =>
    inp P (fun w => if h : D F w v then rec w h else F.init) v)
  have hx : IsExec P x := by
    intro v
    show hwf.fix _ v = _
    rw [WellFounded.fix_eq]
    apply inp_loc
    intro w hw
    simp [hw, x]
  refine ⟨x, hx, fun y hy => ?_⟩
  -- 一意性: D に沿った帰納法
  funext v
  induction v using hwf.induction with
  | _ v ih =>
    rw [hy v, hx v]
    exact inp_loc P y x v (fun w hw => ih w hw)

/-! ## 3. 定理 4 (2): rf ∪ po が循環すれば、実行のないプロセスも、二つ以上あるプロセスもある

状態を整数とする。循環から、入力の依存 `D` の循環が得られる。その循環を含む強連結な部分 `C` の各 CS は、
`C` の中の CS の入力に依存する CS から読んでいる。そこで、そういう CS が「`C` の中の入力 + 1」を出力するようにすれば、
`C` の中で入力が最小の CS で矛盾する(実行がない)。「`C` の中の入力」をそのまま出力するようにすれば、
`C` の上で一定の値はどれも整合する(実行が二つ以上)。 -/

/-- `po` を広げた「同じか前」。 -/
def Le (F : Frame V S) (a b : V) : Prop := a = b ∨ F.po a b

/-- rf ∪ po の道は、po だけの道か、D の道を含む。 -/
theorem path_split (F : Frame V S) (hpt : ∀ a b c, F.po a b → F.po b c → F.po a c)
    {a b : V} (h : TransGen (E F) a b) :
    F.po a b ∨ ∃ v t, D F a v ∧ ReflTransGen (D F) v t ∧ Le F t b := by
  induction h with
  | single h =>
    rcases h with h | h
    · exact Or.inr ⟨_, _, ⟨a, h, Or.inl rfl⟩, ReflTransGen.refl, Or.inl rfl⟩
    · exact Or.inl h
  | @tail c b _ hcb ih =>
    rcases ih with hac | ⟨v, t, hav, hvt, htc⟩
    · rcases hcb with h | h
      · exact Or.inr ⟨b, b, ⟨c, h, Or.inr hac⟩, ReflTransGen.refl, Or.inl rfl⟩
      · exact Or.inl (hpt _ _ _ hac h)
    · rcases hcb with h | h
      · have : D F t b := by
          rcases htc with e | e
          · exact ⟨c, h, Or.inl e⟩
          · exact ⟨c, h, Or.inr e⟩
        exact Or.inr ⟨v, b, hav, hvt.tail this, Or.inl rfl⟩
      · refine Or.inr ⟨v, t, hav, hvt, ?_⟩
        rcases htc with e | e
        · subst e; exact Or.inr h
        · exact Or.inr (hpt _ _ _ e h)

/-- rf ∪ po の循環から、入力の依存 D の循環が得られる(po は狭義の順序)。 -/
theorem D_cycle (F : Frame V S) (hpt : ∀ a b c, F.po a b → F.po b c → F.po a c)
    (hpi : ∀ a, ¬ F.po a a) {a : V} (h : TransGen (E F) a a) : ∃ t, TransGen (D F) t t := by
  rcases path_split F hpt h with h1 | ⟨v, t, hav, hvt, hta⟩
  · exact absurd h1 (hpi a)
  · refine ⟨t, ?_⟩
    obtain ⟨u, hu, hau⟩ := hav
    have htv : D F t v := by
      refine ⟨u, hu, ?_⟩
      rcases hta with e | e
      · subst e; exact hau
      · rcases hau with e' | e'
        · subst e'; exact Or.inr e
        · exact Or.inr (hpt _ _ _ e e')
    exact TransGen.head' htv hvt

section Cycle

variable (F : Frame V S) (t : V) (ht : TransGen (D F) t t)
include ht

/-- 循環を含む強連結な部分。 -/
def Comp : Set V := {v | TransGen (D F) t v ∧ TransGen (D F) v t}

omit ht in
theorem mem_comp_t : t ∈ Comp F t ↔ TransGen (D F) t t := by
  simp [Comp]

/-- `C` の各 CS には、`C` の中に D の前の CS がある。 -/
theorem comp_pred {v : V} (hv : v ∈ Comp F t) : ∃ p ∈ Comp F t, D F p v := by
  obtain ⟨htv, hvt⟩ := hv
  rcases TransGen.tail'_iff.mp htv with ⟨p, hp, hpv⟩
  refine ⟨p, ⟨?_, TransGen.head hpv hvt⟩, hpv⟩
  rcases ReflTransGen.cases_tail hp with e | ⟨q, hq, hqp⟩
  · subst e; exact ht
  · exact TransGen.tail' hq hqp

end Cycle

/-- `C` の CS が読む CS(`rf v` の中身)。 -/
noncomputable def src (F : Frame V S) (v : V) (h : ∃ p, D F p v) : V :=
  Classical.choose (Classical.choose_spec h)

theorem src_spec (F : Frame V S) (v : V) (h : ∃ p, D F p v) :
    F.rf v = some (src F v h) := (Classical.choose_spec (Classical.choose_spec h)).1

/-- **定理 4 (2).** rf ∪ po が循環すれば(po は狭義の順序)、整数の状態で、
実行が一つもないプロセスと、実行が二つ以上あるプロセスがある。 -/
theorem thm4_2 [Finite V] (F : Frame V ℤ) (hpt : ∀ a b c, F.po a b → F.po b c → F.po a c)
    (hpi : ∀ a, ¬ F.po a a) {a : V} (hcyc : TransGen (E F) a a) :
    (∃ P : Proc F, ∀ x, ¬ IsExec P x) ∧
    (∃ P : Proc F, ∃ x y, IsExec P x ∧ IsExec P y ∧ x ≠ y) := by
  obtain ⟨t, ht⟩ := D_cycle F hpt hpi hcyc
  set C := Comp F t with hC
  -- C の各 CS v について、C の中の前の CS pred v と、v が読む CS
  have hpred : ∀ v, v ∈ C → ∃ p ∈ C, D F p v := fun v hv => comp_pred F t ht hv
  -- 「C の CS が読んでいる CS」u について、それを読む C の CS の前の CS を一つ選ぶ
  let isSrc : V → Prop := fun u => ∃ v ∈ C, F.rf v = some u
  have pick : ∀ u, isSrc u → ∃ p ∈ C, p = u ∨ F.po p u := by
    rintro u ⟨v, hv, hvu⟩
    obtain ⟨p, hp, u', hu', hpu⟩ := hpred v hv
    rw [hvu] at hu'
    cases hu'
    exact ⟨p, hp, hpu⟩
  let pr : V → V := fun u => if h : isSrc u then Classical.choose (pick u h) else u
  have pr_spec : ∀ u, isSrc u → pr u ∈ C ∧ (pr u = u ∨ F.po (pr u) u) := by
    intro u hu
    simp only [pr]
    rw [dite_eq_left_of_eq_true (eq_true hu)]
    exact Classical.choose_spec (pick u hu)
  -- 出力「C の中の入力 + k」(k = 1 なら実行なし、k = 0 なら実行が二つ以上)
  let mk : ℤ → Proc F := fun k =>
    { out := fun u x => if isSrc u then x (pr u) + k else 0
      loc := by
        intro u x y hxy
        by_cases hu : isSrc u
        · simp only [hu, ite_true]
          rw [hxy _ (pr_spec u hu).2]
        · simp [hu] }
  -- C の CS の入力は、C の中のある CS の入力 + k
  have step : ∀ k x, IsExec (mk k) x → ∀ v ∈ C, ∃ p ∈ C, x v = x p + k := by
    intro k x hx v hv
    obtain ⟨p, hp, u, hu, -⟩ := hpred v hv
    have hs : isSrc u := ⟨v, hv, hu⟩
    refine ⟨pr u, (pr_spec u hs).1, ?_⟩
    rw [hx v]
    simp [inp, hu, mk, hs]
  have htC : t ∈ C := (mem_comp_t F t).mpr ht
  constructor
  · refine ⟨mk 1, fun x hx => ?_⟩
    -- C の中で入力が最小の CS で矛盾
    have hfin : C.Finite := Set.toFinite C
    obtain ⟨m, hm, hmin⟩ := Set.exists_min_image C x hfin ⟨t, htC⟩
    obtain ⟨p, hp, hxp⟩ := step 1 x hx m hm
    have := hmin p hp
    omega
  · -- C の上で一定の値 c をとる実行が、c ごとに一つずつある
    let sol : ℤ → V → ℤ := fun c v =>
      match F.rf v with
      | none => F.init
      | some u => if isSrc u then c else 0
    have hsol : ∀ c, IsExec (mk 0) (sol c) := by
      intro c v
      simp only [inp, sol, mk]
      cases hv : F.rf v with
      | none => simp
      | some u =>
        simp only [Option.elim]
        by_cases hu : isSrc u
        · simp only [hu, ite_true, add_zero]
          -- pr u は C の CS なので、C の CS を読む CS を読んでいる
          obtain ⟨hpC, -⟩ := pr_spec u hu
          obtain ⟨q, -, u', hu', -⟩ := hpred (pr u) hpC
          have : isSrc u' := ⟨pr u, hpC, hu'⟩
          simp [hu', this]
        · simp [hu]
    refine ⟨mk 0, sol 0, sol 1, hsol 0, hsol 1, fun e => ?_⟩
    have := congrFun e t
    obtain ⟨p, -, u, hu, -⟩ := hpred t htC
    have hs : isSrc u := ⟨t, htC, hu⟩
    simp [sol, hu, hs] at this

end ImagExec.T4

#print axioms ImagExec.T4.thm4_1
#print axioms ImagExec.T4.thm4_2
