/-
  虚実行論 定理 1 の Lean 4 形式化(report0 §4.2)

  CS の全体 V(有限)、各 CS が読んだ状態を書いた CS を与える par : V → Option V
  (none は初期状態 ⊥)、プログラム順序 po。
  因果的(po ∪ rf が循環しない)を、それと同値な「両方の辺に沿って真に増える番号 ρ がある」で表す。
-/
import Mathlib

set_option autoImplicit false

namespace ImagExec.T1

variable {V : Type}

/-- 因果的: rf の辺(読まれた側 → 読んだ側)と po の辺に沿って真に増える番号がある。 -/
def Causal (par : V → Option V) (po : V → V → Prop) : Prop :=
  ∃ ρ : V → ℕ, (∀ v u, par v = some u → ρ u < ρ v) ∧ (∀ u v, po u v → ρ u < ρ v)

/-- 全順序 σ で、v は σ で直前の CS(なければ ⊥)を読む。 -/
def ReadsPrev (σ : V → ℕ) (par : V → Option V) (v : V) : Prop :=
  match par v with
  | none => ∀ w, ¬ σ w < σ v
  | some u => σ u < σ v ∧ ∀ w, σ w < σ v → σ w ≤ σ u

/-- 実実行: CS の全順序(プログラム順序と両立)で、各 CS が直前の CS の結果を読むもの。 -/
def IsReal (par : V → Option V) (po : V → V → Prop) : Prop :=
  ∃ σ : V → ℕ, Function.Injective σ ∧ (∀ u v, po u v → σ u < σ v) ∧ ∀ v, ReadsPrev σ par v

/-- 葉: 誰にも読まれない状態(⊥ も含めて数える)。 -/
def leaves [Fintype V] [DecidableEq V] (par : V → Option V) : Finset (Option V) :=
  Finset.univ.filter (fun x => ∀ v, par v ≠ x)

/-! ### (2) ⇔ (3): どの状態も高々一度しか読まれない ⇔ 葉がちょうど一つ -/

theorem card_leaves [Fintype V] [DecidableEq V] (par : V → Option V) :
    (leaves par).card + (Finset.univ.image par).card = Fintype.card V + 1 := by
  classical
  have h : leaves par = Finset.univ \ Finset.univ.image par := by
    ext x; simp [leaves]
  rw [h, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Fintype.card_option]
  have := Finset.card_le_univ (Finset.univ.image par)
  rw [Fintype.card_option] at this
  omega

theorem injective_iff_one_leaf [Fintype V] [DecidableEq V] (par : V → Option V) :
    Function.Injective par ↔ (leaves par).card = 1 := by
  have hc := card_leaves par
  have e : Function.Injective par ↔ (Finset.univ.image par).card = Fintype.card V := by
    rw [← Finset.card_univ, Finset.card_image_iff, Finset.coe_univ, Set.injOn_univ]
  rw [e]
  omega

/-! ### (1) ⇒ (2): 実実行では、どの状態も高々一度しか読まれない -/

theorem real_injective {par : V → Option V} {po : V → V → Prop} (h : IsReal par po) :
    Function.Injective par := by
  obtain ⟨σ, hσ, -, hr⟩ := h
  intro a b hab
  by_contra hne
  have side : ∀ a b, σ a < σ b → par a = par b → False := by
    intro a b hlt he
    have ha := hr a
    have hb := hr b
    unfold ReadsPrev at ha hb
    rw [← he] at hb
    cases hpa : par a with
    | none => rw [hpa] at hb; exact hb a hlt
    | some u =>
      rw [hpa] at ha hb
      exact absurd (hb.2 a hlt) (not_le.mpr ha.1)
  rcases lt_or_gt_of_ne (fun h => hne (hσ h)) with h | h
  · exact side a b h hab
  · exact side b a h hab.symm

/-! ### (2) ⇒ (1): 線形なら、根からの深さが実実行の順序になる -/

section Depth
variable (par : V → Option V) (ρ : V → ℕ) (hρ : ∀ v u, par v = some u → ρ u < ρ v)

/-- ⊥ からの深さ(⊥ を読む CS が 1)。 -/
def depth (par : V → Option V) (ρ : V → ℕ) (hρ : ∀ v u, par v = some u → ρ u < ρ v)
    (v : V) : ℕ :=
  match hp : par v with
  | none => 1
  | some u => depth par ρ hρ u + 1
termination_by ρ v
decreasing_by exact hρ v u hp

include hρ in
theorem depth_none {v : V} (h : par v = none) : depth par ρ hρ v = 1 := by
  rw [depth]; split <;> simp_all

include hρ in
theorem depth_some {v u : V} (h : par v = some u) :
    depth par ρ hρ v = depth par ρ hρ u + 1 := by
  rw [depth]; split <;> simp_all

include hρ in
theorem depth_pos (v : V) : 1 ≤ depth par ρ hρ v := by
  cases h : par v with
  | none => rw [depth_none par ρ hρ h]
  | some u => rw [depth_some par ρ hρ h]; omega

/-- 祖先(⊥ 側へたどれる CS、自分を含む)。 -/
inductive Anc : V → V → Prop
  | refl (v : V) : Anc v v
  | step {u v w : V} : par v = some u → Anc w u → Anc w v

include hρ in
/-- 深さ d(w) ≤ d(v) なら、v の祖先に深さ d(w) のものがいる。 -/
theorem exists_anc (v : V) : ∀ k, 1 ≤ k → k ≤ depth par ρ hρ v →
    ∃ a, Anc par a v ∧ depth par ρ hρ a = k := by
  induction v using (measure ρ).wf.induction with
  | h v ih =>
    intro k hk1 hk
    rcases Nat.lt_or_eq_of_le hk with hlt | heq
    · cases hp : par v with
      | none => rw [depth_none par ρ hρ hp] at hlt; omega
      | some u =>
        rw [depth_some par ρ hρ hp] at hlt
        obtain ⟨a, ha, hd⟩ := ih u (hρ v u hp) k hk1 (by omega)
        exact ⟨a, Anc.step hp ha, hd⟩
    · exact ⟨v, Anc.refl v, heq.symm⟩

include hρ in
theorem anc_rho {a v : V} (h : Anc par a v) : ρ a ≤ ρ v := by
  induction h with
  | refl => exact le_refl _
  | step hp _ ih => exact le_trans ih (hρ _ _ hp).le

include hρ in
theorem depth_injective (hinj : Function.Injective par) :
    Function.Injective (depth par ρ hρ) := by
  have key : ∀ k, ∀ a b, depth par ρ hρ a = k → depth par ρ hρ b = k → a = b := by
    intro k
    induction k with
    | zero => intro a _ ha _; have := depth_pos par ρ hρ a; omega
    | succ k ih =>
      intro a b ha hb
      cases hpa : par a with
      | none =>
        cases hpb : par b with
        | none => exact hinj (hpa.trans hpb.symm)
        | some ub =>
          rw [depth_none par ρ hρ hpa] at ha
          rw [depth_some par ρ hρ hpb] at hb
          have := depth_pos par ρ hρ ub; omega
      | some ua =>
        cases hpb : par b with
        | none =>
          rw [depth_some par ρ hρ hpa] at ha
          rw [depth_none par ρ hρ hpb] at hb
          have := depth_pos par ρ hρ ua; omega
        | some ub =>
          rw [depth_some par ρ hρ hpa] at ha
          rw [depth_some par ρ hρ hpb] at hb
          have := ih ua ub (by omega) (by omega)
          subst this
          exact hinj (hpa.trans hpb.symm)
  intro a b h
  exact key _ a b rfl h.symm

end Depth

theorem injective_real [Fintype V] {par : V → Option V} {po : V → V → Prop} (hc : Causal par po)
    (hinj : Function.Injective par) : IsReal par po := by
  obtain ⟨ρ, hρ, hpo⟩ := hc
  let d := depth par ρ hρ
  have dinj := depth_injective par ρ hρ hinj
  refine ⟨d, dinj, fun u v huv => ?_, fun v => ?_⟩
  · -- d(v) ≤ d(u) なら v は u の祖先で、po u v と合わせて循環する
    by_contra hc'
    push Not at hc'
    obtain ⟨a, ha, hd⟩ := exists_anc par ρ hρ u (d v) (depth_pos par ρ hρ v) hc'
    have : a = v := dinj hd
    subst this
    have := anc_rho par ρ hρ ha
    have := hpo u a huv
    omega
  · unfold ReadsPrev
    cases hp : par v with
    | none =>
      intro w hw
      have := depth_pos par ρ hρ w
      have := depth_none par ρ hρ hp
      simp only [d] at hw
      omega
    | some u =>
      have h1 := depth_some par ρ hρ hp
      refine ⟨by simp only [d]; omega, fun w hw => ?_⟩
      simp only [d] at hw ⊢
      omega

/-- **定理 1.** 因果的な rf について、次は同値:
(1) 実実行から来る、(2) どの状態も高々一度しか読まれない、(3) 葉がちょうど一つ。 -/
theorem thm1 [Fintype V] [DecidableEq V] (par : V → Option V) (po : V → V → Prop) (hc : Causal par po) :
    (IsReal par po ↔ Function.Injective par) ∧
    (Function.Injective par ↔ (leaves par).card = 1) :=
  ⟨⟨real_injective, injective_real hc⟩, injective_iff_one_leaf par⟩

end ImagExec.T1

#print axioms ImagExec.T1.thm1
