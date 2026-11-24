/-
  虚実行論 定理 2・定理 3 の Lean 4 形式化
  (report0 「虚実行論 ―― 並列処理の総当りから「虚」の理論へ」0.1.0 の §5・§6)

  Author: JRF / 形式化: Claude Opus 5.5
  Lean 4 v4.34.1 + Mathlib v4.34.1
-/
import Mathlib

set_option autoImplicit false
set_option linter.deprecated false

namespace ImagExec

/-! ## 0. 共通の言葉

* プロセスは `Fin P`。プロセス `q` は `L q` 回クリティカルセクション(CS)を実行する。
* CS `(q, m)` の lock を局所時刻 `2m`、unlock を局所時刻 `2m+1` とする。
* 「読み出し元」`Src P := Option (Fin P × ℕ)`。`none` は初期状態 ⊥、
  `some (p, n)` はプロセス `p` の `n` 番目の unlock 状態。
-/

abbrev Src (P : ℕ) := Option (Fin P × ℕ)

/-- 自分の直前の状態(`m = 0` なら ⊥)。 -/
def own {P : ℕ} (q : Fin P) (m : ℕ) : Src P :=
  if m = 0 then none else some (q, m - 1)

/-! ## 1. ELDE その1 の lock 仕様 -/

/-- lock 仕様の一項 `P{p}U{n}->P{q}L{m}`: プロセス `p` の unlock `n` の状態を、
プロセス `q` の lock `m` に渡す(受け渡し)。 -/
@[ext]
structure Item (P : ℕ) where
  p : Fin P
  n : ℕ
  q : Fin P
  m : ℕ
  hpq : p ≠ q
deriving DecidableEq

namespace Item
variable {P : ℕ}

/-- 項 `e` がプロセス `r` の局所時刻をどこで占めるか。 -/
def time (e : Item P) (r : Fin P) : Option ℕ :=
  if r = e.p then some (2 * e.n + 1) else if r = e.q then some (2 * e.m) else none

/-- 列の中で `e` が `e'` より前にあってよい条件: 共有するどのプロセスでも局所時刻が狭義に増える。 -/
def Before (e e' : Item P) : Prop :=
  ∀ r t t', e.time r = some t → e'.time r = some t' → t < t'

theorem time_p (e : Item P) : e.time e.p = some (2 * e.n + 1) := by simp [time]
theorem time_q (e : Item P) : e.time e.q = some (2 * e.m) := by
  simp [time, Ne.symm e.hpq]

/-- JRF の `_make_lock_spec_tree` の四つの不等式(任意の j < k について)。 -/
theorem before_iff (e e' : Item P) :
    Before e e' ↔
      (e'.p = e.p → e'.n > e.n) ∧ (e'.p = e.q → e'.n ≥ e.m) ∧
      (e'.q = e.q → e'.m > e.m) ∧ (e'.q = e.p → e'.m > e.n) := by
  constructor
  · intro h
    refine ⟨fun hh => ?_, fun hh => ?_, fun hh => ?_, fun hh => ?_⟩
    · have := h e.p _ _ (time_p e) (by rw [← hh]; exact time_p e'); omega
    · have := h e.q _ _ (time_q e) (by rw [← hh]; exact time_p e'); omega
    · have := h e.q _ _ (time_q e) (by rw [← hh]; exact time_q e'); omega
    · have := h e.p _ _ (time_p e) (by rw [← hh]; exact time_q e'); omega
  · rintro ⟨a, b, c, d⟩ r t t' ht ht'
    unfold time at ht ht'
    by_cases r1 : r = e.p
    · rw [if_pos r1] at ht; cases ht
      by_cases r3 : r = e'.p
      · rw [if_pos r3] at ht'; cases ht'; have := a (r3.symm.trans r1); omega
      · rw [if_neg r3] at ht'
        by_cases r4 : r = e'.q
        · rw [if_pos r4] at ht'; cases ht'; have := d (r4.symm.trans r1); omega
        · rw [if_neg r4] at ht'; cases ht'
    · rw [if_neg r1] at ht
      by_cases r2 : r = e.q
      · rw [if_pos r2] at ht; cases ht
        by_cases r3 : r = e'.p
        · rw [if_pos r3] at ht'; cases ht'; have := b (r3.symm.trans r2); omega
        · rw [if_neg r3] at ht'
          by_cases r4 : r = e'.q
          · rw [if_pos r4] at ht'; cases ht'; have := c (r4.symm.trans r2); omega
          · rw [if_neg r4] at ht'; cases ht'
      · rw [if_neg r2] at ht; cases ht

theorem not_before_self (e : Item P) : ¬ Before e e := by
  intro h; have := h e.p _ _ (time_p e) (time_p e); omega

end Item

open Item

/-- 局所時刻を共有する(どちらの順にも並べられない)二項。 -/
def Prec {P : ℕ} (e e' : Item P) : Prop :=
  ∃ r t t', e.time r = some t ∧ e'.time r = some t' ∧ t < t'

/-- ELDE その1 が生成する(切られない)lock 仕様: 列が `Before` について pairwise で、
各項が lock 回数の範囲に収まる。 -/
def Valid {P : ℕ} (L : Fin P → ℕ) (l : List (Item P)) : Prop :=
  l.Pairwise Before ∧ ∀ e ∈ l, e.n < L e.p ∧ e.m < L e.q

/-- 定理 2 の条件(受け渡しの集合 `S` について):
(衝突なし)同じ局所時刻を二つの項が使わない、
(非巡回)局所時刻の先後から作るグラフが循環しない。 -/
def Cond {P : ℕ} (S : Finset (Item P)) : Prop :=
  (∀ e ∈ S, ∀ e' ∈ S, ∀ r t, e.time r = some t → e'.time r = some t → e = e') ∧
  (∀ e ∈ S, ¬ Relation.TransGen (fun a b => a ∈ S ∧ b ∈ S ∧ Prec a b) e e)

/-- lock 仕様から読み出し関係 rf を作る: `(q, m)` を lock 側に持つ項があればその unlock 状態、
なければ自分の直前の状態。 -/
def srcE {P : ℕ} (l : List (Item P)) (q : Fin P) (m : ℕ) : Src P :=
  match l.find? (fun e => decide (e.q = q ∧ e.m = m)) with
  | some e => some (e.p, e.n)
  | none => own q m

/-! ## 2. 定理 2 -/

section Thm2
variable {P : ℕ}

theorem valid_nodup_rel {L : Fin P → ℕ} {l : List (Item P)} (hl : Valid L l)
    {e e' : Item P} (he : e ∈ l) (he' : e' ∈ l) (hne : e ≠ e') :
    Before e e' ∨ Before e' e := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he'
  have hp := List.pairwise_iff_getElem.mp hl.1
  rcases lt_trichotomy i j with h | h | h
  · exact Or.inl (hp i j hi hj h)
  · subst h; exact absurd rfl hne
  · exact Or.inr (hp j i hj hi h)

/-- 定理 2(a) 前半: ELDE その1 の lock 仕様の受け渡しの集合は条件を満たす。 -/
theorem valid_cond {L : Fin P → ℕ} {l : List (Item P)} (hl : Valid L l) :
    Cond l.toFinset := by
  constructor
  · intro e he e' he' r t h1 h2
    simp only [List.mem_toFinset] at he he'
    by_contra hne
    rcases valid_nodup_rel hl he he' hne with h | h
    · have := h r t t h1 h2; omega
    · have := h r t t h2 h1; omega
  · -- 位置 idxOf が真に増える
    have key : ∀ a b, (a ∈ l.toFinset ∧ b ∈ l.toFinset ∧ Prec a b) →
        l.idxOf a < l.idxOf b := by
      rintro a b ⟨ha, hb, r, t, t', h1, h2, h3⟩
      simp only [List.mem_toFinset] at ha hb
      have hia := List.idxOf_lt_length_of_mem ha
      have hib := List.idxOf_lt_length_of_mem hb
      have ea : l[l.idxOf a] = a := List.getElem_idxOf hia
      have eb : l[l.idxOf b] = b := List.getElem_idxOf hib
      have hp := List.pairwise_iff_getElem.mp hl.1
      rcases lt_trichotomy (l.idxOf a) (l.idxOf b) with h | h | h
      · exact h
      · exfalso
        have : a = b := by rw [← ea, ← eb]; simp [h]
        subst this; rw [h1] at h2; cases h2; omega
      · exfalso
        have := hp _ _ hib hia h
        rw [ea, eb] at this
        have := this r t' t h2 h1; omega
    intro e _ h
    have : ∀ a b, Relation.TransGen
        (fun a b => a ∈ l.toFinset ∧ b ∈ l.toFinset ∧ Prec a b) a b →
        l.idxOf a < l.idxOf b := by
      intro a b hab
      induction hab with
      | single h => exact key _ _ h
      | tail _ h ih => exact lt_trans ih (key _ _ h)
    exact lt_irrefl _ (this e e h)

theorem cond_mono {S T : Finset (Item P)} (h : S ⊆ T) (hT : Cond T) : Cond S := by
  refine ⟨fun e he e' he' => hT.1 e (h he) e' (h he'), fun e he hc => hT.2 e (h he) ?_⟩
  exact Relation.TransGen.mono (p := fun a b => a ∈ T ∧ b ∈ T ∧ Prec a b)
    (fun _ _ hab => ⟨h hab.1, h hab.2.1, hab.2.2⟩) e e hc

/-- 有限で非巡回なら、前に何も来ない(極小な)項がある。 -/
theorem exists_minimal {S : Finset (Item P)} (hS : Cond S) (hne : S.Nonempty) :
    ∃ e ∈ S, ∀ e' ∈ S, ¬ Prec e' e := by
  classical
  let R : S → S → Prop := fun a b =>
    Relation.TransGen (fun a b => a ∈ S ∧ b ∈ S ∧ Prec a b) a.1 b.1
  have : IsTrans S R := ⟨fun _ _ _ h1 h2 => Relation.TransGen.trans h1 h2⟩
  have : Std.Irrefl R := ⟨fun a h => hS.2 a.1 a.2 h⟩
  have wf : WellFounded R := Finite.wellFounded_of_trans_of_irrefl R
  obtain ⟨x, hx⟩ := hne
  obtain ⟨m, -, hm⟩ := wf.has_min Set.univ ⟨⟨x, hx⟩, trivial⟩
  refine ⟨m.1, m.2, fun e' he' hp => hm ⟨e', he'⟩ trivial ?_⟩
  exact Relation.TransGen.single ⟨he', m.2, hp⟩

/-- 定理 2(a) 後半: 条件を満たす受け渡しの集合は、ELDE その1 の lock 仕様として並べられる
(位相的整列)。 -/
theorem cond_valid (L : Fin P → ℕ) (S : Finset (Item P)) (hS : Cond S)
    (hb : ∀ e ∈ S, e.n < L e.p ∧ e.m < L e.q) :
    ∃ l : List (Item P), Valid L l ∧ l.toFinset = S := by
  classical
  induction hc : S.card generalizing S with
  | zero =>
    refine ⟨[], ⟨List.Pairwise.nil, by simp⟩, ?_⟩
    rw [Finset.card_eq_zero] at hc; simp [hc]
  | succ k ih =>
    have hne : S.Nonempty := by
      rw [← Finset.card_pos]; omega
    obtain ⟨e, he, hmin⟩ := exists_minimal hS hne
    obtain ⟨l', ⟨hp', hb'⟩, hl'⟩ := ih (S.erase e) (cond_mono (Finset.erase_subset _ _) hS)
      (fun x hx => hb x (Finset.mem_of_mem_erase hx)) (by rw [Finset.card_erase_of_mem he]; omega)
    refine ⟨e :: l', ⟨?_, ?_⟩, ?_⟩
    · refine List.Pairwise.cons (fun x hx => ?_) hp'
      have hx' : x ∈ S.erase e := by rw [← hl']; simpa using hx
      have hxe : x ≠ e := Finset.ne_of_mem_erase hx'
      have hxS := Finset.mem_of_mem_erase hx'
      intro r t t' h1 h2
      rcases lt_trichotomy t t' with h | h | h
      · exact h
      · subst h; exact absurd (hS.1 e he x hxS r t h1 h2).symm hxe
      · exact absurd ⟨r, t', t, h2, h1, h⟩ (hmin x hxS)
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hb x he
      · exact hb' x hx
    · rw [List.toFinset_cons, hl', Finset.insert_erase he]

/-- `srcE` の性質: lock 側に `(q,m)` を持つ項があればその unlock 状態を読む。 -/
theorem srcE_of_mem {L : Fin P → ℕ} {l : List (Item P)} (hl : Valid L l) {e : Item P}
    (he : e ∈ l) : srcE l e.q e.m = some (e.p, e.n) := by
  unfold srcE
  cases hf : l.find? (fun x => decide (x.q = e.q ∧ x.m = e.m)) with
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd (by simp) (hf e he)
  | some x =>
    have hx := List.mem_of_find?_eq_some hf
    have hpx := List.find?_some hf
    simp only [decide_eq_true_eq] at hpx
    have : x = e := (valid_cond hl).1 x (by simpa using hx) e (by simpa using he) e.q (2 * e.m)
      (by rw [← hpx.1, ← hpx.2]; exact time_q x) (time_q e)
    subst this; rfl

theorem srcE_of_not_mem {l : List (Item P)} {q : Fin P} {m : ℕ}
    (h : ∀ e ∈ l, ¬ (e.q = q ∧ e.m = m)) : srcE l q m = own q m := by
  unfold srcE
  have : l.find? (fun e => decide (e.q = q ∧ e.m = m)) = none := by
    rw [List.find?_eq_none]; intro x hx; simpa using h x hx
  rw [this]

theorem own_ne_cross {q p : Fin P} {m n : ℕ} (h : p ≠ q) : own q m ≠ some (p, n) := by
  unfold own; split_ifs <;> simp [Ne.symm h]

/-- 定理 2(b): lock 仕様 → rf は、受け渡しの集合だけで決まり、集合が違えば rf も違う。 -/
theorem srcE_eq_iff {L : Fin P → ℕ} {l₁ l₂ : List (Item P)} (h₁ : Valid L l₁)
    (h₂ : Valid L l₂) : (∀ q m, srcE l₁ q m = srcE l₂ q m) ↔ (∀ e, e ∈ l₁ ↔ e ∈ l₂) := by
  have half : ∀ {l₁ l₂ : List (Item P)}, Valid L l₁ → Valid L l₂ →
      (∀ q m, srcE l₁ q m = srcE l₂ q m) → ∀ e, e ∈ l₁ → e ∈ l₂ := by
    intro l₁ l₂ h₁ h₂ H e he
    have h := H e.q e.m
    rw [srcE_of_mem h₁ he] at h
    by_cases hx : ∃ x ∈ l₂, x.q = e.q ∧ x.m = e.m
    · obtain ⟨x, hx, hq, hm⟩ := hx
      have h' := srcE_of_mem h₂ hx
      rw [hq, hm, ← h] at h'
      simp only [Option.some.injEq, Prod.mk.injEq] at h'
      have : x = e := Item.ext h'.1.symm h'.2.symm hq hm
      exact this ▸ hx
    · push Not at hx
      rw [srcE_of_not_mem (fun x hx' hh => hx x hx' hh.1 hh.2)] at h
      exact absurd h.symm (own_ne_cross e.hpq)
  constructor
  · intro H e
    exact ⟨half h₁ h₂ H e, half h₂ h₁ (fun q m => (H q m).symm) e⟩
  · intro H q m
    by_cases hx : ∃ x ∈ l₁, x.q = q ∧ x.m = m
    · obtain ⟨x, hx, rfl, rfl⟩ := hx
      rw [srcE_of_mem h₁ hx, srcE_of_mem h₂ ((H x).mp hx)]
    · push Not at hx
      rw [srcE_of_not_mem (fun x hx' hh => hx x hx' hh.1 hh.2),
        srcE_of_not_mem (fun x hx' hh => hx x ((H x).mpr hx') hh.1 hh.2)]

/-- 3 プロセス以下では、どの二項も必ずどこかのプロセスを共有する。 -/
theorem share_of_le_three (hP : P ≤ 3) (e e' : Item P) :
    ∃ r t t', e.time r = some t ∧ e'.time r = some t' := by
  have h1 := e.hpq; have h2 := e'.hpq
  have : e.p = e'.p ∨ e.p = e'.q ∨ e.q = e'.p ∨ e.q = e'.q := by
    rw [Fin.ext_iff, Fin.ext_iff, Fin.ext_iff, Fin.ext_iff]
    rw [Ne, Fin.ext_iff] at h1 h2
    have := e.p.2; have := e.q.2; have := e'.p.2; have := e'.q.2
    omega
  rcases this with h | h | h | h
  · exact ⟨e.p, _, _, time_p e, by rw [h]; exact time_p e'⟩
  · exact ⟨e.p, _, _, time_p e, by rw [h]; exact time_q e'⟩
  · exact ⟨e.q, _, _, time_q e, by rw [h]; exact time_p e'⟩
  · exact ⟨e.q, _, _, time_q e, by rw [h]; exact time_q e'⟩

/-- 定理 2(c): 3 プロセス以下では、受け渡しの集合が同じ lock 仕様は列として一つしかない。
したがって lock 仕様と rf は一対一に対応する。 -/
theorem valid_unique (hP : P ≤ 3) {L : Fin P → ℕ} :
    ∀ {l₁ l₂ : List (Item P)}, Valid L l₁ → Valid L l₂ → (∀ e, e ∈ l₁ ↔ e ∈ l₂) → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ _ _ H
    cases l₂ with
    | nil => rfl
    | cons b t => exact absurd ((H b).mpr (by simp)) (by simp)
  | cons a t₁ ih =>
    intro l₂ h₁ h₂ H
    cases l₂ with
    | nil => exact absurd ((H a).mp (by simp)) (by simp)
    | cons b t₂ =>
      have hp₁ := List.pairwise_cons.mp h₁.1
      have hp₂ := List.pairwise_cons.mp h₂.1
      have v₁ : Valid L t₁ := ⟨hp₁.2, fun e he => h₁.2 e (by simp [he])⟩
      have v₂ : Valid L t₂ := ⟨hp₂.2, fun e he => h₂.2 e (by simp [he])⟩
      have hab : a = b := by
        by_contra hne
        have hb : b ∈ t₁ := by
          have := (H b).mpr (by simp)
          rcases List.mem_cons.mp this with h | h
          · exact absurd h.symm hne
          · exact h
        have ha : a ∈ t₂ := by
          have := (H a).mp (by simp)
          rcases List.mem_cons.mp this with h | h
          · exact absurd h hne
          · exact h
        have x := hp₁.1 b hb
        have y := hp₂.1 a ha
        obtain ⟨r, t, t', h1, h2⟩ := share_of_le_three hP a b
        have := x r t t' h1 h2; have := y r t' t h2 h1; omega
      subst hab
      have na₁ : a ∉ t₁ := fun h => not_before_self a (hp₁.1 a h)
      have na₂ : a ∉ t₂ := fun h => not_before_self a (hp₂.1 a h)
      congr 1
      refine ih v₁ v₂ (fun e => ?_)
      constructor
      · intro he
        have hne : e ≠ a := fun h => na₁ (h ▸ he)
        have := (H e).mp (by simp [he])
        rcases List.mem_cons.mp this with h | h
        · exact absurd h hne
        · exact h
      · intro he
        have hne : e ≠ a := fun h => na₂ (h ▸ he)
        have := (H e).mpr (by simp [he])
        rcases List.mem_cons.mp this with h | h
        · exact absurd h hne
        · exact h

/-- 定理 2(c) の限界: 4 プロセスでは、共通のプロセスを持たない二項はどちらの順にも並べられ、
同じ rf を与える二つの lock 仕様ができる(report0 の「一対一」は 3 プロセスまで)。 -/
theorem not_unique_four :
    ∃ l₁ l₂ : List (Item 4), Valid (fun _ => 1) l₁ ∧ Valid (fun _ => 1) l₂ ∧
      l₁ ≠ l₂ ∧ ∀ q m, srcE l₁ q m = srcE l₂ q m := by
  let e₁ : Item 4 := ⟨0, 0, 1, 0, by decide⟩
  let e₂ : Item 4 := ⟨2, 0, 3, 0, by decide⟩
  have b₁ : Before e₁ e₂ := by
    intro r t t' h1 h2
    simp only [Item.time, e₁, e₂] at h1 h2
    fin_cases r <;> simp_all
  have b₂ : Before e₂ e₁ := by
    intro r t t' h1 h2
    simp only [Item.time, e₁, e₂] at h1 h2
    fin_cases r <;> simp_all
  have v₁ : Valid (fun _ => 1) [e₁, e₂] :=
    ⟨by simp [b₁], by intro e he; simp at he; rcases he with rfl | rfl <;> simp [e₁, e₂]⟩
  have v₂ : Valid (fun _ => 1) [e₂, e₁] :=
    ⟨by simp [b₂], by intro e he; simp at he; rcases he with rfl | rfl <;> simp [e₁, e₂]⟩
  refine ⟨[e₁, e₂], [e₂, e₁], v₁, v₂, by simp [e₁, e₂], ?_⟩
  exact (srcE_eq_iff v₁ v₂).mpr (fun e => by simp [or_comm])

end Thm2

/-! ## 3. 進行グラフ・トンネル意味論・実実行 -/

section Sched
variable {P : ℕ}

/-- 時刻 `x` の時点で「最も新しいもの」(時刻関数 `g`、各プロセスの個数 `K`)が `s` である。
`none` は「まだ何もない」(初期状態 ⊥)。 -/
def MostRecent (K : Fin P → ℕ) (g : Fin P × ℕ → ℕ) (x : ℕ) : Src P → Prop
  | none => ∀ p n, n < K p → ¬ g (p, n) < x
  | some (p, n) => n < K p ∧ g (p, n) < x ∧
      ∀ p' n', n' < K p' → g (p', n') < x → g (p', n') ≤ g (p, n)

/-- 範囲内で単射。 -/
def InjOn' (K : Fin P → ℕ) (g : Fin P × ℕ → ℕ) : Prop :=
  ∀ p n p' n', n < K p → n' < K p' → g (p, n) = g (p', n') → p = p' ∧ n = n'

theorem mostRecent_unique {K : Fin P → ℕ} {g : Fin P × ℕ → ℕ} (hg : InjOn' K g)
    {x y : ℕ} {s s' : Src P} (h : MostRecent K g x s) (h' : MostRecent K g y s')
    (hxy : ∀ p n, n < K p → (g (p, n) < x ↔ g (p, n) < y)) : s = s' := by
  match s, s', h, h' with
  | none, none, _, _ => rfl
  | none, some (a, b), h, ⟨hb, hl, _⟩ => exact absurd ((hxy a b hb).mpr hl) (h a b hb)
  | some (a, b), none, ⟨hb, hl, _⟩, h' => exact absurd ((hxy a b hb).mp hl) (h' a b hb)
  | some (a, b), some (a', b'), ⟨hb, hl, hm⟩, ⟨hb', hl', hm'⟩ =>
    have e1 := hm' a b hb ((hxy a b hb).mp hl)
    have e2 := hm a' b' hb' ((hxy a' b' hb').mpr hl')
    obtain ⟨rfl, rfl⟩ := hg a b a' b' hb hb' (le_antisymm e1 e2)
    rfl

/-- lock/unlock 事象の並べ方(進行グラフ上の単調な道)。事象 `(r, t)` はプロセス `r` の
局所時刻 `t`(`t < 2 L r`、偶数が lock、奇数が unlock)で、`τ` はその大域時刻。
排他は課さない。 -/
structure Arr (L : Fin P → ℕ) (τ : Fin P × ℕ → ℕ) : Prop where
  mono : ∀ r t t', t < t' → t' < 2 * L r → τ (r, t) < τ (r, t')
  inj : ∀ r t r' t', t < 2 * L r → t' < 2 * L r' → τ (r, t) = τ (r', t') → r = r' ∧ t = t'

/-- unlock 事象の時刻。 -/
def uT (τ : Fin P × ℕ → ℕ) : Fin P × ℕ → ℕ := fun x => τ (x.1, 2 * x.2 + 1)

/-- トンネル意味論: lock `(q, m)` は、その時点で最も新しい unlock 状態を読む。 -/
def TReads (L : Fin P → ℕ) (τ : Fin P × ℕ → ℕ) (q : Fin P) (m : ℕ) (s : Src P) : Prop :=
  MostRecent L (uT τ) (τ (q, 2 * m)) s

def IsTunnel (L : Fin P → ℕ) (rf : Fin P → ℕ → Src P) : Prop :=
  ∃ τ, Arr L τ ∧ ∀ q m, m < L q → TReads L τ q m (rf q m)

/-- 道が禁止領域(二つのプロセスが同時にロックを持つ点)を通らない。 -/
def Avoids (L : Fin P → ℕ) (τ : Fin P × ℕ → ℕ) : Prop :=
  ∀ p n q m, p ≠ q → n < L p → m < L q →
    τ (p, 2 * n + 1) < τ (q, 2 * m) ∨ τ (q, 2 * m + 1) < τ (p, 2 * n)

/-- 実実行: CS の全順序(時刻 `σ`)で、各 CS は直前の CS の結果を読む。 -/
structure RArr (L : Fin P → ℕ) (σ : Fin P × ℕ → ℕ) : Prop where
  mono : ∀ r m m', m < m' → m' < L r → σ (r, m) < σ (r, m')
  inj : InjOn' L σ

def IsReal (L : Fin P → ℕ) (rf : Fin P → ℕ → Src P) : Prop :=
  ∃ σ, RArr L σ ∧ ∀ q m, m < L q → MostRecent L σ (σ (q, m)) (rf q m)

variable {L : Fin P → ℕ}

theorem Arr.lt_of {τ : Fin P × ℕ → ℕ} (hA : Arr L τ) {r : Fin P} {t t' : ℕ}
    (ht : t < 2 * L r) (_ht' : t' < 2 * L r) (h : τ (r, t) < τ (r, t')) : t < t' := by
  by_contra hc
  rcases Nat.lt_or_eq_of_le (not_lt.mp hc) with h' | h'
  · exact absurd (hA.mono r t' t h' ht) (not_lt.mpr h.le)
  · subst h'; exact lt_irrefl _ h

theorem Arr.le_of_le {τ : Fin P × ℕ → ℕ} (hA : Arr L τ) {r : Fin P} {t t' : ℕ}
    (ht' : t' < 2 * L r) (h : t ≤ t') : τ (r, t) ≤ τ (r, t') := by
  rcases Nat.lt_or_eq_of_le h with h | h
  · exact (hA.mono r t t' h ht').le
  · rw [h]

theorem Arr.uinj {τ : Fin P × ℕ → ℕ} (hA : Arr L τ) : InjOn' L (uT τ) := by
  intro p n p' n' hn hn' h
  obtain ⟨h1, h2⟩ := hA.inj p _ p' _ (by omega) (by omega) h
  exact ⟨h1, by omega⟩

theorem Arr.ne {τ : Fin P × ℕ → ℕ} (hA : Arr L τ) {r r' : Fin P} {t t' : ℕ}
    (ht : t < 2 * L r) (ht' : t' < 2 * L r') (h : r ≠ r' ∨ t ≠ t') : τ (r, t) ≠ τ (r', t') := by
  intro he
  obtain ⟨h1, h2⟩ := hA.inj r t r' t' ht ht' he
  rcases h with h | h <;> contradiction

/-- 定理 3(ii) ⇒: 実実行は、禁止領域を避ける道として描ける(CS を lock・unlock の二事象に分ける)。 -/
theorem real_to_tunnel {rf : Fin P → ℕ → Src P} (h : IsReal L rf) :
    ∃ τ, Arr L τ ∧ Avoids L τ ∧ ∀ q m, m < L q → TReads L τ q m (rf q m) := by
  obtain ⟨σ, hσ, hr⟩ := h
  refine ⟨fun x => 2 * σ (x.1, x.2 / 2) + x.2 % 2, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro r t t' htt ht'
    dsimp only
    rcases Nat.lt_or_eq_of_le (Nat.div_le_div_right (c := 2) htt.le) with h | h
    · have := hσ.mono r _ _ h (by omega)
      omega
    · rw [h]; omega
  · intro r t r' t' ht ht' he
    simp only at he
    have hp : t % 2 = t' % 2 := by omega
    have hs : σ (r, t / 2) = σ (r', t' / 2) := by omega
    obtain ⟨h1, h2⟩ := hσ.inj r _ r' _ (by omega) (by omega) hs
    exact ⟨h1, by omega⟩
  · intro p n q m hpq hn hm
    have hne : σ (p, n) ≠ σ (q, m) := fun he => hpq (hσ.inj p n q m hn hm he).1
    simp only [show (2 * n + 1) / 2 = n by omega, show (2 * n + 1) % 2 = 1 by omega,
      show 2 * m / 2 = m by omega, show 2 * m % 2 = 0 by omega,
      show (2 * m + 1) / 2 = m by omega, show (2 * m + 1) % 2 = 1 by omega,
      show 2 * n / 2 = n by omega, show 2 * n % 2 = 0 by omega]
    omega
  · intro q m hm
    have key := hr q m hm
    unfold TReads uT
    simp only [show ∀ k, (2 * k + 1) / 2 = k by omega, show ∀ k, (2 * k + 1) % 2 = 1 by omega,
      show 2 * m / 2 = m by omega, show 2 * m % 2 = 0 by omega]
    match hrf : rf q m, key with
    | none, key => intro p n hn h; dsimp only at h; exact key p n hn (by omega)
    | some (p, n), ⟨hn, hl, hmx⟩ =>
      refine ⟨hn, ?_, fun p' n' hn' h => ?_⟩
      · dsimp only; omega
      · dsimp only at h ⊢; have := hmx p' n' hn' (by omega); omega

/-- 定理 3(ii) ⇐: 禁止領域を避ける道のトンネル意味論は実実行である。 -/
theorem avoid_to_real {rf : Fin P → ℕ → Src P} {τ : Fin P × ℕ → ℕ} (hA : Arr L τ)
    (hv : Avoids L τ) (hr : ∀ q m, m < L q → TReads L τ q m (rf q m)) : IsReal L rf := by
  -- lock より前に lock を取った CS は、その lock より前に unlock を済ませている
  have before : ∀ q m a b, m < L q → b < L a → τ (a, 2 * b) < τ (q, 2 * m) →
      τ (a, 2 * b + 1) < τ (q, 2 * m) := by
    intro q m a b hm hb h
    by_cases haq : a = q
    · subst haq
      have := hA.lt_of (by omega) (by omega) h
      exact hA.mono a _ _ (by omega) (by omega)
    · rcases hv a b q m haq hb hm with h' | h'
      · exact h'
      · exact absurd (lt_trans h' h) (not_lt.mpr (hA.mono q _ _ (by omega) (by omega)).le)
  refine ⟨fun x => τ (x.1, 2 * x.2), ⟨fun r m m' h h' => hA.mono r _ _ (by omega) (by omega),
    fun p n p' n' hn hn' he => ?_⟩, fun q m hm => ?_⟩
  · obtain ⟨h1, h2⟩ := hA.inj p _ p' _ (by omega) (by omega) he; exact ⟨h1, by omega⟩
  · have key := hr q m hm
    unfold TReads uT at key
    simp only
    match hrf : rf q m, key with
    | none, key => intro a b hb h; exact key a b hb (before q m a b hm hb h)
    | some (p, n), ⟨hn, hl, hmx⟩ =>
      refine ⟨hn, lt_trans (hA.mono p _ _ (by omega) (by omega)) hl, fun a b hb h => ?_⟩
      simp only at h ⊢
      by_contra hc
      push Not at hc
      have u := hmx a b hb (before q m a b hm hb h)
      simp only at u
      -- L(a,b) が CS (p,n) の内側にある
      have i1 : τ (a, 2 * b) < τ (p, 2 * n + 1) :=
        lt_of_lt_of_le (hA.mono a _ _ (by omega) (by omega)) u
      by_cases hap : a = p
      · subst hap
        have := hA.lt_of (by omega) (by omega) hc
        have := hA.lt_of (by omega) (by omega) i1
        omega
      · rcases hv a b p n hap hb hn with h' | h'
        · have := hA.mono a (2 * b) (2 * b + 1) (by omega) (by omega)
          exact absurd (lt_trans (lt_trans h' hc) this) (lt_irrefl _)
        · exact absurd (lt_trans h' i1) (lt_irrefl _)

/-- 実実行では、どの状態も高々一つの CS にしか読まれない(定理 1 の線形性)。 -/
theorem real_linear {rf : Fin P → ℕ → Src P} (h : IsReal L rf) {p q : Fin P} {n m : ℕ}
    (hn : n < L p) (hm : m < L q) (hne : (p, n) ≠ (q, m)) : rf p n ≠ rf q m := by
  obtain ⟨σ, hσ, hr⟩ := h
  intro he
  have hs : σ (p, n) ≠ σ (q, m) := by
    intro h'; obtain ⟨h1, h2⟩ := hσ.inj p n q m hn hm h'; exact hne (by rw [h1, h2])
  have side : ∀ (p q : Fin P) n m, n < L p → m < L q → σ (p, n) < σ (q, m) →
      ∀ s, MostRecent L σ (σ (p, n)) s → MostRecent L σ (σ (q, m)) s → False := by
    intro p q n m hn hm hlt s h1 h2
    match s, h1, h2 with
    | none, _, h2 => exact h2 p n hn hlt
    | some (a, b), ⟨_, hl, _⟩, ⟨_, _, hmx⟩ =>
      exact absurd (hmx p n hn hlt) (not_le.mpr hl)
  rcases lt_or_gt_of_ne hs with h' | h'
  · exact side p q n m hn hm h' _ (hr p n hn) (he ▸ hr q m hm)
  · exact side q p m n hm hn h' _ (hr q m hm) (he ▸ hr p n hn)

/-- 道が禁止点を通ると、二つの lock が同じ unlock 状態(または ⊥)を読む。
(最初に禁止領域に入る瞬間を取ると、二つの lock の間には unlock が一つもない。) -/
theorem cross_double_read {rf : Fin P → ℕ → Src P} {τ : Fin P × ℕ → ℕ} (hA : Arr L τ)
    (hv : ¬ Avoids L τ) (hr : ∀ q m, m < L q → TReads L τ q m (rf q m)) :
    ∃ p n q m, n < L p ∧ m < L q ∧ (p, n) ≠ (q, m) ∧ rf p n = rf q m := by
  classical
  let Ov : ℕ → Prop := fun t => ∃ p n q m, p ≠ q ∧ n < L p ∧ m < L q ∧
    τ (p, 2 * n) < τ (q, 2 * m) ∧ τ (q, 2 * m) < τ (p, 2 * n + 1) ∧ τ (q, 2 * m) = t
  have hex : ∃ t, Ov t := by
    unfold Avoids at hv
    push Not at hv
    obtain ⟨p, n, q, m, hpq, hn, hm, h1, h2⟩ := hv
    have d1 := hA.ne (r := p) (r' := q) (t := 2 * n) (t' := 2 * m) (by omega) (by omega)
      (Or.inl hpq)
    have d2 := hA.ne (r := p) (r' := q) (t := 2 * n + 1) (t' := 2 * m) (by omega) (by omega)
      (Or.inl hpq)
    have d3 := hA.ne (r := q) (r' := p) (t := 2 * m + 1) (t' := 2 * n) (by omega) (by omega)
      (Or.inl (Ne.symm hpq))
    rcases lt_or_gt_of_ne d1 with h | h
    · exact ⟨_, p, n, q, m, hpq, hn, hm, h, lt_of_le_of_ne h1 (Ne.symm d2), rfl⟩
    · exact ⟨_, q, m, p, n, Ne.symm hpq, hm, hn, h, lt_of_le_of_ne h2 (Ne.symm d3), rfl⟩
  obtain ⟨p, n, q, m, hpq, hn, hm, o1, o2, ho⟩ := Nat.find_spec hex
  have hmin := fun t (ht : t < Nat.find hex) => Nat.find_min hex ht
  refine ⟨p, n, q, m, hn, hm, fun h => hpq (Prod.mk.inj h).1, ?_⟩
  refine mostRecent_unique hA.uinj (hr p n hn) (hr q m hm) (fun a b hb => ?_)
  unfold uT
  simp only
  constructor
  · intro h; exact lt_trans h o1
  · intro h
    by_contra hc
    have hc' : τ (p, 2 * n) < τ (a, 2 * b + 1) := by
      have := hA.ne (r := p) (r' := a) (t := 2 * n) (t' := 2 * b + 1) (by omega) (by omega)
        (Or.inr (by omega))
      exact lt_of_le_of_ne (not_lt.mp hc) this
    by_cases hap : a = p
    · subst hap
      have := hA.lt_of (by omega) (by omega) hc'
      have := hA.le_of_le (r := a) (t := 2 * n + 1) (t' := 2 * b + 1) (by omega) (by omega)
      exact absurd (lt_of_le_of_lt this h) (not_lt.mpr o2.le)
    · have d := hA.ne (r := a) (r' := p) (t := 2 * b) (t' := 2 * n) (by omega) (by omega)
        (Or.inl hap)
      have ab := hA.mono a (2 * b) (2 * b + 1) (by omega) (by omega)
      rcases lt_or_gt_of_ne d with h' | h'
      · exact hmin _ (ho ▸ o1) ⟨a, b, p, n, hap, hb, hn, h', hc', rfl⟩
      · exact hmin _ (ho ▸ lt_trans ab h)
          ⟨p, n, a, b, Ne.symm hap, hn, hb, h', lt_trans (lt_trans ab h) o2, rfl⟩

/-- **定理 3(ii)**(任意のプロセス数). rf が実実行である ⇔ その rf を与える道のうちに
禁止点を通らないものがある。さらに強く、rf を与える道のどれか一つについて
「実 ⇔ その道が禁止点を通らない」(実の rf を与える道はすべて禁止点を避ける)。 -/
theorem thm3_ii (rf : Fin P → ℕ → Src P) :
    IsReal L rf ↔ ∃ τ, Arr L τ ∧ Avoids L τ ∧ ∀ q m, m < L q → TReads L τ q m (rf q m) :=
  ⟨real_to_tunnel, fun ⟨_, hA, hv, hr⟩ => avoid_to_real hA hv hr⟩

theorem thm3_ii_strong (rf : Fin P → ℕ → Src P) (τ : Fin P × ℕ → ℕ) (hA : Arr L τ)
    (hr : ∀ q m, m < L q → TReads L τ q m (rf q m)) : IsReal L rf ↔ Avoids L τ := by
  constructor
  · intro h
    by_contra hv
    obtain ⟨p, n, q, m, hn, hm, hne, he⟩ := cross_double_read hA hv hr
    exact real_linear h hn hm hne he
  · intro hv; exact avoid_to_real hA hv hr

end Sched

/-! ## 4. 定理 3(i): 2 プロセスでは トンネル意味論 = ELDE その1 -/

/-- ELDE その1 の実行(lock 仕様から作られる rf)。 -/
def IsE0 {P : ℕ} (L : Fin P → ℕ) (rf : Fin P → ℕ → Src P) : Prop :=
  ∃ l, Valid L l ∧ ∀ q m, m < L q → srcE l q m = rf q m

theorem srcE_bound {P : ℕ} {L : Fin P → ℕ} {l : List (Item P)} (hl : Valid L l) {q p : Fin P}
    {m n : ℕ} (hm : m < L q) (h : srcE l q m = some (p, n)) : n < L p := by
  by_cases hx : ∃ e ∈ l, e.q = q ∧ e.m = m
  · obtain ⟨e, he, rfl, rfl⟩ := hx
    rw [srcE_of_mem hl he] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (hl.2 e he).1
  · rw [srcE_of_not_mem (fun x hx' hh => hx ⟨x, hx', hh⟩)] at h
    unfold own at h
    split_ifs at h with hm0
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    omega

/-- トンネル意味論で他プロセスから読まないなら、自分の直前の状態を読んでいる。 -/
theorem tunnel_own {P : ℕ} {L : Fin P → ℕ} {τ : Fin P × ℕ → ℕ} (hA : Arr L τ) {q : Fin P}
    {m : ℕ} {s : Src P} (hm : m < L q) (h : TReads L τ q m s)
    (hs : ∀ p n, s = some (p, n) → p = q) : s = own q m := by
  unfold TReads uT at h
  match s, h with
  | none, h =>
    unfold own
    by_cases hm0 : m = 0
    · simp [hm0]
    · exact absurd (hA.mono q (2 * (m - 1) + 1) (2 * m) (by omega) (by omega))
        (h q (m - 1) (by omega))
  | some (p, n), ⟨hn, hl, hmx⟩ =>
    have := hs p n rfl
    subst this
    try dsimp only at hl hmx
    have h1 := hA.lt_of (by omega) (by omega) hl
    have hm0 : m ≠ 0 := by omega
    have h2 := hmx p (m - 1) (by omega) (hA.mono p _ _ (by omega) (by omega))
    try simp only [uT] at h2
    have h3 : 2 * (m - 1) + 1 ≤ 2 * n + 1 := by
      by_contra hc
      exact absurd (hA.mono p _ _ (not_le.mp hc) (by omega)) (not_lt.mpr h2)
    unfold own
    rw [if_neg hm0]
    congr 2
    omega

section Two

theorem fin2_other (a b c : Fin 2) (hab : a ≠ b) (hca : c ≠ a) : c = b := by
  revert a b c; decide

/-- 2 プロセスでは、どの項も両方のプロセスの局所時刻を占める。 -/
def tm (e : Item 2) (r : Fin 2) : ℕ := if r = e.p then 2 * e.n + 1 else 2 * e.m

theorem time_two (e : Item 2) (r : Fin 2) : e.time r = some (tm e r) := by
  unfold Item.time tm
  by_cases h : r = e.p
  · simp [h]
  · have := fin2_other e.p e.q r e.hpq h
    rw [if_neg h, if_neg h, if_pos this]

theorem tm_p (e : Item 2) : tm e e.p = 2 * e.n + 1 := by simp [tm]
theorem tm_q (e : Item 2) : tm e e.q = 2 * e.m := by simp [tm, Ne.symm e.hpq]

variable {L : Fin 2 → ℕ}

/-! ### トンネル ⊆ E0 -/

def crossItem (rf : Fin 2 → ℕ → Src 2) (q : Fin 2) (m : ℕ) : Option (Item 2) :=
  match rf q m with
  | some (p, n) => if h : p ≠ q then some ⟨p, n, q, m, h⟩ else none
  | none => none

/-- rf のうち他プロセスからの読み出し(受け渡し)の一覧。 -/
def crossList (L : Fin 2 → ℕ) (rf : Fin 2 → ℕ → Src 2) : List (Item 2) :=
  (List.finRange 2).flatMap (fun q => (List.range (L q)).filterMap (crossItem rf q))

theorem mem_crossList {rf : Fin 2 → ℕ → Src 2} {e : Item 2} :
    e ∈ crossList L rf ↔ e.m < L e.q ∧ rf e.q e.m = some (e.p, e.n) := by
  unfold crossList
  simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨q, m, hm, hc⟩
    unfold crossItem at hc
    split at hc
    · rename_i p n hpn
      split_ifs at hc with h
      cases hc
      exact ⟨hm, hpn⟩
    · cases hc
  · rintro ⟨hm, hr⟩
    exact ⟨e.q, e.m, hm, by simp [crossItem, hr, e.hpq]⟩

theorem tunnel_to_e0 {rf : Fin 2 → ℕ → Src 2} (h : IsTunnel L rf) : IsE0 L rf := by
  obtain ⟨τ, hA, hr⟩ := h
  set S := (crossList L rf).toFinset with hS
  have memS : ∀ e, e ∈ S ↔ e.m < L e.q ∧ rf e.q e.m = some (e.p, e.n) := by
    intro e; rw [hS, List.mem_toFinset, mem_crossList]
  have rd : ∀ e ∈ S, TReads L τ e.q e.m (some (e.p, e.n)) := by
    intro e he; obtain ⟨hm, h⟩ := (memS e).mp he; rw [← h]; exact hr _ _ hm
  have bnd : ∀ e ∈ S, e.n < L e.p ∧ e.m < L e.q :=
    fun e he => ⟨(rd e he).1, ((memS e).mp he).1⟩
  -- 同じ unlock 状態を、同じプロセスの二つの lock が読むことはない
  have twice : ∀ (p q : Fin 2) n m m', m < m' → m' < L q →
      TReads L τ q m (some (p, n)) → TReads L τ q m' (some (p, n)) → False := by
    intro p q n m m' hlt hm' h1 h2
    obtain ⟨hn, hl1, -⟩ := h1
    obtain ⟨-, -, hmx⟩ := h2
    try simp only [uT] at hl1 hmx
    have a1 := hA.mono q (2 * m) (2 * m + 1) (by omega) (by omega)
    have a2 := hA.mono q (2 * m + 1) (2 * m') (by omega) (by omega)
    have := hmx q m (by omega) a2
    try simp only [uT] at this
    omega
  -- 後の unlock を前の lock が、前の unlock を後の lock が読むことはない
  have cross_mono : ∀ (p q : Fin 2) n n' m m', n < n' → m' < m → m < L q →
      TReads L τ q m' (some (p, n')) → TReads L τ q m (some (p, n)) → False := by
    intro p q n n' m m' hn hm hmq h1 h2
    obtain ⟨hn', hl1, -⟩ := h1
    obtain ⟨-, -, hmx⟩ := h2
    try simp only [uT] at hl1 hmx
    have a1 := hA.mono q (2 * m') (2 * m) (by omega) (by omega)
    have := hmx p n' hn' (lt_trans hl1 a1)
    try simp only [uT] at this
    have := hA.mono p (2 * n + 1) (2 * n' + 1) (by omega) (by omega)
    omega
  have noColl : ∀ e ∈ S, ∀ e' ∈ S, ∀ r t, e.time r = some t → e'.time r = some t → e = e' := by
    intro e he e' he' r t h1 h2
    rw [time_two] at h1 h2
    have h1 := Option.some.inj h1
    have h2 := Option.some.inj h2
    unfold tm at h1 h2
    by_cases r1 : r = e.p
    · rw [if_pos r1] at h1
      by_cases r2 : r = e'.p
      · rw [if_pos r2] at h2
        have hp : e.p = e'.p := r1.symm.trans r2
        have hn : e.n = e'.n := by omega
        have hq : e.q = e'.q :=
          (fin2_other e'.p e'.q e.q e'.hpq (by rw [← hp]; exact Ne.symm e.hpq)).trans rfl
        have ra := rd e he
        have rb := rd e' he'
        rw [← hp, ← hn, ← hq] at rb
        rcases lt_trichotomy e.m e'.m with hm | hm | hm
        · exact absurd (twice _ _ _ _ _ hm (by rw [hq]; exact (bnd e' he').2) ra rb) id
        · exact Item.ext hp hn hq hm
        · exact absurd (twice _ _ _ _ _ hm (bnd e he).2 rb ra) id
      · rw [if_neg r2] at h2; omega
    · rw [if_neg r1] at h1
      by_cases r2 : r = e'.p
      · rw [if_pos r2] at h2; omega
      · rw [if_neg r2] at h2
        have hq : e.q = e'.q :=
          (fin2_other e.p e.q r e.hpq r1).symm.trans (fin2_other e'.p e'.q r e'.hpq r2)
        have hm : e.m = e'.m := by omega
        have e1 := ((memS e).mp he).2
        have e2 := ((memS e').mp he').2
        rw [hq, hm, e2] at e1
        simp only [Option.some.injEq, Prod.mk.injEq] at e1
        exact Item.ext e1.1.symm e1.2.symm hq hm
  have key : ∀ a b, a ∈ S → b ∈ S → Prec a b → τ (a.q, 2 * a.m) < τ (b.q, 2 * b.m) := by
    rintro a b ha hb ⟨r, t, t', h1, h2, h3⟩
    rw [time_two] at h1 h2
    have h1 := Option.some.inj h1
    have h2 := Option.some.inj h2
    unfold tm at h1 h2
    obtain ⟨ran, ram⟩ := bnd a ha
    obtain ⟨rbn, rbm⟩ := bnd b hb
    have ra := rd a ha
    have rb := rd b hb
    by_cases r1 : r = a.p
    · rw [if_pos r1] at h1
      by_cases r2 : r = b.p
      · -- 両方 unlock 側
        rw [if_pos r2] at h2
        have hp : a.p = b.p := r1.symm.trans r2
        have hq : a.q = b.q :=
          fin2_other b.p b.q a.q b.hpq (by rw [← hp]; exact Ne.symm a.hpq)
        have hn : a.n < b.n := by omega
        rcases lt_trichotomy a.m b.m with hm | hm | hm
        · rw [hq]; exact hA.mono _ _ _ (by omega) (by omega)
        · exfalso
          have e1 := ((memS a).mp ha).2
          have e2 := ((memS b).mp hb).2
          rw [hq, hm, e2] at e1
          simp only [Option.some.injEq, Prod.mk.injEq] at e1
          omega
        · exfalso
          rw [← hq, ← hp] at rb
          exact cross_mono a.p a.q a.n b.n a.m b.m hn hm ram rb ra
      · -- a は unlock 側、b は lock 側
        rw [if_neg r2] at h2
        have hbq : r = b.q := fin2_other b.p b.q r b.hpq r2
        have hbp : b.p = a.q := fin2_other a.p a.q b.p a.hpq (by
          intro hh; exact b.hpq (hh.trans (r1.symm.trans hbq)))
        have hqq : b.q ≠ a.q := by rw [← hbq, r1]; exact a.hpq
        by_contra hc
        push Not at hc
        have hne := hA.ne (r := b.q) (r' := a.q) (t := 2 * b.m) (t' := 2 * a.m)
          (by omega) (by omega) (Or.inl hqq)
        have hlt := lt_of_le_of_ne hc hne
        obtain ⟨-, hlb, hmb⟩ := rb
        obtain ⟨-, hla, hma⟩ := ra
        try simp only [uT] at hlb hmb hla hma
        have x1 : τ (a.p, 2 * a.n + 1) < τ (b.q, 2 * b.m) := by
          have : a.p = b.q := r1.symm.trans hbq
          rw [this]; exact hA.mono _ _ _ (by omega) (by omega)
        have u1 := hmb a.p a.n ran x1
        have u2 := hma b.p b.n rbn (lt_trans hlb hlt)
        try simp only [uT] at u1 u2
        have := (hA.uinj b.p b.n a.p a.n rbn ran (le_antisymm u2 u1)).1
        exact b.hpq (this.trans (r1.symm.trans hbq))
    · rw [if_neg r1] at h1
      have haq : r = a.q := fin2_other a.p a.q r a.hpq r1
      by_cases r2 : r = b.p
      · -- a は lock 側、b は unlock 側
        rw [if_pos r2] at h2
        have hab : a.q = b.p := haq.symm.trans r2
        have x1 : τ (a.q, 2 * a.m) < τ (b.p, 2 * b.n + 1) := by
          rw [hab]; exact hA.mono _ _ _ (by omega) (by omega)
        exact lt_trans x1 rb.2.1
      · -- 両方 lock 側
        rw [if_neg r2] at h2
        have hbq : r = b.q := fin2_other b.p b.q r b.hpq r2
        have hab : a.q = b.q := haq.symm.trans hbq
        rw [hab]
        exact hA.mono _ _ _ (by omega) (by omega)
  have acyc : ∀ e ∈ S, ¬ Relation.TransGen (fun a b => a ∈ S ∧ b ∈ S ∧ Prec a b) e e := by
    intro e _ hc
    have : ∀ a b, Relation.TransGen (fun a b => a ∈ S ∧ b ∈ S ∧ Prec a b) a b →
        τ (a.q, 2 * a.m) < τ (b.q, 2 * b.m) := by
      intro a b hab
      induction hab with
      | single h => exact key _ _ h.1 h.2.1 h.2.2
      | tail _ h ih => exact lt_trans ih (key _ _ h.1 h.2.1 h.2.2)
    exact lt_irrefl _ (this e e hc)
  obtain ⟨l, hl, hlS⟩ := cond_valid L S ⟨noColl, acyc⟩ bnd
  have memL : ∀ e, e ∈ l ↔ e ∈ S := fun e => by rw [← hlS, List.mem_toFinset]
  refine ⟨l, hl, fun q m hm => ?_⟩
  by_cases hc : ∃ p n, rf q m = some (p, n) ∧ p ≠ q
  · obtain ⟨p, n, hpn, hpq⟩ := hc
    have he : (⟨p, n, q, m, hpq⟩ : Item 2) ∈ l := (memL _).mpr ((memS _).mpr ⟨hm, hpn⟩)
    rw [hpn]
    exact srcE_of_mem hl he
  · rw [srcE_of_not_mem (fun x hx hh => by
      obtain ⟨hq, hm'⟩ := hh
      have := ((memS x).mp ((memL x).mp hx)).2
      rw [hq, hm'] at this
      exact hc ⟨x.p, x.n, this, hq ▸ x.hpq⟩)]
    refine (tunnel_own hA hm (hr q m hm) (fun p n h => ?_)).symm
    by_contra hpq
    exact hc ⟨p, n, h, hpq⟩

/-! ### E0 ⊆ トンネル: lock 仕様から道を作る

unlock 事象を「その unlock 以前に局所時刻を持つ項の数」`cnt` で並べ(同数なら受け渡しに
使われる unlock を先に)、各 lock はその読み出し元の unlock の直後に置く。 -/

section Constr
variable (L : Fin 2 → ℕ) (l : List (Item 2))

def cnt (r : Fin 2) (n : ℕ) : ℕ := l.countP (fun e => decide (tm e r ≤ 2 * n + 1))

def flag (r : Fin 2) (n : ℕ) : ℕ := if ∃ e ∈ l, e.p = r ∧ e.n = n then 0 else 1

def MM : ℕ := 2 * (L 0 + L 1) + 2

def code : Src 2 → ℕ
  | none => 0
  | some (r, n) => (2 * cnt l r n + flag l r n) * MM L + (2 * n + r.val + 1)

def tau (x : Fin 2 × ℕ) : ℕ :=
  if x.2 % 2 = 1 then 3 * code L l (some (x.1, x.2 / 2))
  else 3 * code L l (srcE l x.1 (x.2 / 2)) + 1 + x.1.val

end Constr

theorem count_ge {α : Type} (l : List α) (f : α → ℕ)
    (hs : ∀ i j (hi : i < l.length) (hj : j < l.length), i < j → f l[i] < f l[j])
    {x k : ℕ} (hk : k < l.length) (hx : f l[k] ≤ x) :
    k + 1 ≤ l.countP (fun a => decide (f a ≤ x)) := by
  have h1 : (l.take (k + 1)).countP (fun a => decide (f a ≤ x)) = k + 1 := by
    rw [List.countP_eq_length.mpr]
    · simp; omega
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp ha
    simp only [decide_eq_true_eq]
    rcases Nat.lt_or_eq_of_le (show j ≤ k by omega) with h | h
    · exact le_trans (hs j k _ hk h).le hx
    · subst h; exact hx
  have := List.countP_append (p := fun a => decide (f a ≤ x)) (l₁ := l.take (k + 1))
    (l₂ := l.drop (k + 1))
  rw [List.take_append_drop] at this
  omega

theorem count_le {α : Type} (l : List α) (f : α → ℕ)
    (hs : ∀ i j (hi : i < l.length) (hj : j < l.length), i < j → f l[i] < f l[j])
    {x k : ℕ} (hk : k < l.length) (hx : x < f l[k]) :
    l.countP (fun a => decide (f a ≤ x)) ≤ k := by
  have h1 : (l.drop k).countP (fun a => decide (f a ≤ x)) = 0 := by
    rw [List.countP_eq_zero]
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_drop_iff_getElem.mp ha
    simp only [decide_eq_true_eq, not_le]
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; simpa using hx
    · exact lt_trans hx (hs k (k + j) hk _ (by omega))
  have h2 := List.countP_le_length (p := fun a => decide (f a ≤ x)) (l := l.take k)
  have := List.countP_append (p := fun a => decide (f a ≤ x)) (l₁ := l.take k) (l₂ := l.drop k)
  rw [List.take_append_drop] at this
  simp at h2
  omega

section ConstrBasic
variable {l : List (Item 2)}

theorem flag_le (r : Fin 2) (n : ℕ) : flag l r n ≤ 1 := by unfold flag; split_ifs <;> omega

theorem b_lt {r : Fin 2} {n : ℕ} (hn : n < L r) : 2 * n + r.val + 1 < MM L := by
  unfold MM
  have : L r ≤ L 0 + L 1 := by fin_cases r <;> simp
  have := r.isLt
  omega

theorem code_pos (x : Fin 2 × ℕ) : 1 ≤ code L l (some x) := by
  obtain ⟨r, n⟩ := x; simp only [code]; omega

theorem code_none : code L l none = 0 := rfl

theorem lexA {A A' b b' M : ℕ} (h : A < A') (hb : b < M) : A * M + b < A' * M + b' := by
  have : (A + 1) * M ≤ A' * M := Nat.mul_le_mul_right M h
  nlinarith

theorem lexB {A A' b b' M : ℕ} (h : A ≤ A') (hb : b < b') : A * M + b < A' * M + b' := by
  have : A * M ≤ A' * M := Nat.mul_le_mul_right M h
  omega

theorem lexInj {A A' b b' M : ℕ} (h : A * M + b = A' * M + b') (hb : b < M) (hb' : b' < M) :
    b = b' := by
  have h1 : (b + A * M) % M = (b' + A' * M) % M := by rw [Nat.add_comm b, Nat.add_comm b', h]
  rwa [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt hb'] at h1

theorem tau_u (r : Fin 2) (n : ℕ) : tau L l (r, 2 * n + 1) = 3 * code L l (some (r, n)) := by
  unfold tau
  simp only [show (2 * n + 1) % 2 = 1 by omega, show (2 * n + 1) / 2 = n by omega, if_true]

theorem tau_l (r : Fin 2) (m : ℕ) :
    tau L l (r, 2 * m) = 3 * code L l (srcE l r m) + 1 + r.val := by
  unfold tau
  simp only [show 2 * m % 2 = 0 by omega, show 2 * m / 2 = m by omega]
  rfl

end ConstrBasic

section ConstrLemmas
variable {l : List (Item 2)} (hl : Valid L l)
include hl

theorem sorted_two (r : Fin 2) : ∀ i j (hi : i < l.length) (hj : j < l.length), i < j →
    tm l[i] r < tm l[j] r := by
  intro i j hi hj hij
  exact (List.pairwise_iff_getElem.mp hl.1 i j hi hj hij) r _ _ (time_two _ r) (time_two _ r)

theorem cnt_ge {r : Fin 2} {n k : ℕ} (hk : k < l.length) (hx : tm l[k] r ≤ 2 * n + 1) :
    k + 1 ≤ cnt l r n :=
  count_ge l (fun e => tm e r) (sorted_two hl r) hk hx

theorem cnt_le {r : Fin 2} {n k : ℕ} (hk : k < l.length) (hx : 2 * n + 1 < tm l[k] r) :
    cnt l r n ≤ k :=
  count_le l (fun e => tm e r) (sorted_two hl r) hk hx

theorem code_succ {r : Fin 2} {n : ℕ} :
    code L l (some (r, n)) < code L l (some (r, n + 1)) := by
  unfold code
  apply lexB _ (by omega)
  have f1 := flag_le (l := l) r n
  by_cases ht : ∃ e ∈ l, e.p = r ∧ e.n = n + 1
  · obtain ⟨e, he, hp, hn⟩ := ht
    have f0 : flag l r (n + 1) = 0 := by unfold flag; rw [if_pos ⟨e, he, hp, hn⟩]
    obtain ⟨j, hj, hje⟩ := List.getElem_of_mem he
    have tj : tm l[j] r = 2 * (n + 1) + 1 := by rw [hje, ← hp, tm_p, hn]
    have c1 := cnt_le hl (r := r) (n := n) hj (by rw [tj]; omega)
    have c2 := cnt_ge hl (r := r) (n := n + 1) hj (by rw [tj])
    omega
  · have f0 : flag l r (n + 1) = 1 := by unfold flag; rw [if_neg ht]
    have : cnt l r n ≤ cnt l r (n + 1) :=
      List.countP_mono_left (fun x _ h => by simp only [decide_eq_true_eq] at h ⊢; omega)
    omega

theorem code_mono {r : Fin 2} {n n' : ℕ} (h : n ≤ n') :
    code L l (some (r, n)) ≤ code L l (some (r, n')) := by
  induction n', h using Nat.le_induction with
  | base => exact le_refl _
  | succ k _ ih => exact le_trans ih (code_succ hl).le

/-- 読み出し元は、自分の unlock より前に並ぶ。 -/
theorem code_src_lt {q : Fin 2} {m : ℕ} (hm : m < L q) :
    code L l (srcE l q m) < code L l (some (q, m)) := by
  by_cases hx : ∃ e ∈ l, e.q = q ∧ e.m = m
  · obtain ⟨e, he, hq, hm'⟩ := hx
    subst hq hm'
    rw [srcE_of_mem hl he]
    obtain ⟨k, hk, hke⟩ := List.getElem_of_mem he
    unfold code
    apply lexA _ (b_lt (hl.2 e he).1)
    have f0 : flag l e.p e.n = 0 := by unfold flag; rw [if_pos ⟨e, he, rfl, rfl⟩]
    have c1 : cnt l e.p e.n ≤ k + 1 := by
      by_cases hk1 : k + 1 < l.length
      · apply cnt_le hl hk1
        have := sorted_two hl e.p k (k + 1) hk hk1 (by omega)
        rw [hke, tm_p] at this; exact this
      · have := List.countP_le_length (p := fun x => decide (tm x e.p ≤ 2 * e.n + 1)) (l := l)
        unfold cnt; omega
    have c2 : k + 1 ≤ cnt l e.q e.m := cnt_ge hl hk (by rw [hke, tm_q]; omega)
    have f1 := flag_le (l := l) e.q e.m
    by_cases ht : ∃ e' ∈ l, e'.p = e.q ∧ e'.n = e.m
    · obtain ⟨e', he', hp', hn'⟩ := ht
      obtain ⟨j, hj, hje⟩ := List.getElem_of_mem he'
      have tj : tm l[j] e.q = 2 * e.m + 1 := by rw [hje, ← hp', tm_p, hn']
      have hkj : k < j := by
        by_contra hc
        push Not at hc
        rcases Nat.lt_or_eq_of_le hc with h | h
        · have := sorted_two hl e.q j k hj hk h
          rw [tj, hke, tm_q] at this; omega
        · subst h
          have : e = e' := hke.symm.trans hje
          exact e.hpq (this ▸ hp')
      have c3 : j + 1 ≤ cnt l e.q e.m := cnt_ge hl hj (by rw [tj])
      omega
    · have f2 : flag l e.q e.m = 1 := by unfold flag; rw [if_neg ht]
      omega
  · rw [srcE_of_not_mem (fun x hx' h => hx ⟨x, hx', h⟩)]
    unfold own
    by_cases hm0 : m = 0
    · rw [if_pos hm0]; exact code_pos (l := l) _
    · rw [if_neg hm0]
      have := code_succ hl (r := q) (n := m - 1)
      rwa [show m - 1 + 1 = m by omega] at this

/-- 読み出し元は、自分の直前の unlock 以後に並ぶ。 -/
theorem code_le_src {q : Fin 2} {m : ℕ} (hm0 : 0 < m) (hm : m < L q) :
    code L l (some (q, m - 1)) ≤ code L l (srcE l q m) := by
  by_cases hx : ∃ e ∈ l, e.q = q ∧ e.m = m
  · obtain ⟨e, he, hq, hm'⟩ := hx
    subst hq hm'
    rw [srcE_of_mem hl he]
    obtain ⟨k, hk, hke⟩ := List.getElem_of_mem he
    unfold code
    apply le_of_lt
    apply lexA _ (b_lt (by omega))
    have f0 : flag l e.p e.n = 0 := by unfold flag; rw [if_pos ⟨e, he, rfl, rfl⟩]
    have c1 : cnt l e.q (e.m - 1) ≤ k := cnt_le hl hk (by rw [hke, tm_q]; omega)
    have c2 : k + 1 ≤ cnt l e.p e.n := cnt_ge hl hk (by rw [hke, tm_p])
    have f1 := flag_le (l := l) e.q (e.m - 1)
    omega
  · rw [srcE_of_not_mem (fun x hx' h => hx ⟨x, hx', h⟩)]
    unfold own
    rw [if_neg (by omega)]

theorem tau_step {r : Fin 2} {t : ℕ} (ht : t + 1 < 2 * L r) :
    tau L l (r, t) < tau L l (r, t + 1) := by
  have hr := r.isLt
  obtain ⟨m, rfl | rfl⟩ : ∃ m, t = 2 * m ∨ t = 2 * m + 1 := ⟨t / 2, by omega⟩
  · rw [tau_l, tau_u]
    have := code_src_lt hl (q := r) (m := m) (by omega)
    omega
  · rw [tau_u, show 2 * m + 1 + 1 = 2 * (m + 1) by ring, tau_l]
    have := code_le_src hl (q := r) (m := m + 1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at this
    omega

theorem tau_arr : Arr L (tau L l) := by
  constructor
  · intro r t t' htt ht'
    induction t', htt using Nat.le_induction with
    | base => exact tau_step hl ht'
    | succ k hk ih => exact lt_trans (ih (by omega)) (tau_step hl ht')
  · intro r t r' t' ht ht' he
    have hr := r.isLt
    have hr' := r'.isLt
    obtain ⟨m, rfl | rfl⟩ : ∃ m, t = 2 * m ∨ t = 2 * m + 1 := ⟨t / 2, by omega⟩ <;>
    obtain ⟨m', rfl | rfl⟩ : ∃ m, t' = 2 * m ∨ t' = 2 * m + 1 := ⟨t' / 2, by omega⟩
    · -- lock と lock
      rw [tau_l, tau_l] at he
      have hrr : r = r' := Fin.ext (by omega)
      subst hrr
      have hc : code L l (srcE l r m) = code L l (srcE l r m') := by omega
      refine ⟨rfl, ?_⟩
      by_contra hne
      have side : ∀ a b, a < b → b < L r → code L l (srcE l r a) = code L l (srcE l r b) →
          False := by
        intro a b hab hb hc
        have x1 := code_src_lt hl (q := r) (m := a) (by omega)
        have x2 := code_mono hl (r := r) (n := a) (n' := b - 1) (by omega)
        have x3 := code_le_src hl (q := r) (m := b) (by omega) hb
        omega
      rcases lt_or_gt_of_ne (show m ≠ m' by omega) with h | h
      · exact side m m' h (by omega) hc
      · exact side m' m h (by omega) hc.symm
    · rw [tau_l, tau_u] at he; omega
    · rw [tau_u, tau_l] at he; omega
    · -- unlock と unlock
      rw [tau_u, tau_u] at he
      have hc : code L l (some (r, m)) = code L l (some (r', m')) := by omega
      unfold code at hc
      have := lexInj hc (b_lt (by omega)) (b_lt (by omega))
      have hrr : r = r' := Fin.ext (by omega)
      exact ⟨hrr, by omega⟩

theorem tau_reads {q : Fin 2} {m : ℕ} (hm : m < L q) :
    TReads L (tau L l) q m (srcE l q m) := by
  unfold TReads
  rw [tau_l]
  have hq := q.isLt
  cases hs : srcE l q m with
  | none =>
    intro p n hn h
    have cp := code_pos (L := L) (l := l) (p, n)
    simp only [uT, tau_u, code_none] at h
    omega
  | some x =>
    obtain ⟨p, n⟩ := x
    have cp := code_pos (L := L) (l := l) (p, n)
    refine ⟨srcE_bound hl hm hs, ?_, fun p' n' _ h => ?_⟩
    · simp only [uT, tau_u]; omega
    · simp only [uT, tau_u] at h ⊢; omega

end ConstrLemmas

theorem e0_to_tunnel {rf : Fin 2 → ℕ → Src 2} (h : IsE0 L rf) : IsTunnel L rf := by
  obtain ⟨l, hl, hr⟩ := h
  exact ⟨tau L l, tau_arr hl, fun q m hm => hr q m hm ▸ tau_reads hl hm⟩

/-- **定理 3(i)**(2 プロセス). トンネル意味論の道から得られる rf の全体は、
ELDE その1 の lock 仕様が表す rf の全体 E0 にちょうど一致する。 -/
theorem thm3_i (rf : Fin 2 → ℕ → Src 2) : IsTunnel L rf ↔ IsE0 L rf :=
  ⟨tunnel_to_e0, e0_to_tunnel⟩

end Two

/-- 3 プロセスでは E0 ⊊ T: 一つの unlock 状態を二つの他プロセスが読むトンネル実行は、
ELDE その1 の lock 仕様では表せない(局所時刻が衝突する)。 -/
theorem tunnel_not_e0_three :
    ∃ rf : Fin 3 → ℕ → Src 3, IsTunnel (fun _ => 1) rf ∧ ¬ IsE0 (fun _ => 1) rf := by
  let rf : Fin 3 → ℕ → Src 3 := fun q _ => if q = 0 then none else some (0, 0)
  -- 道: L0 U0 L1 L2 U1 U2
  let τ : Fin 3 × ℕ → ℕ := fun x =>
    if x.1 = 0 then x.2 else if x.1 = 1 then (if x.2 = 0 then 2 else 4)
    else (if x.2 = 0 then 3 else 5)
  refine ⟨rf, ⟨τ, ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro r t t' h h'
    have : t = 0 ∧ t' = 1 := by omega
    obtain ⟨rfl, rfl⟩ := this
    fin_cases r <;> simp [τ]
  · intro r t r' t' h h' he
    have : t < 2 := by omega
    have : t' < 2 := by omega
    fin_cases r <;> fin_cases r' <;> interval_cases t <;> interval_cases t' <;> simp_all [τ]
  · intro q m hm
    simp only at hm
    have : m = 0 := by omega
    subst this
    fin_cases q
    · intro p n hn h
      simp only at hn
      have : n = 0 := by omega
      subst this
      fin_cases p <;> simp [τ, uT] at h
    · refine ⟨by omega, by simp [τ, uT], fun p' n' hn' h => ?_⟩
      simp only at hn'
      have : n' = 0 := by omega
      subst this
      fin_cases p' <;> simp [τ, uT] at h ⊢
    · refine ⟨by omega, by simp [τ, uT], fun p' n' hn' h => ?_⟩
      simp only at hn'
      have : n' = 0 := by omega
      subst this
      fin_cases p' <;> simp [τ, uT] at h ⊢
  · rintro ⟨l, hl, hr⟩
    have get : ∀ q : Fin 3, q ≠ 0 → ∃ e ∈ l, e.q = q ∧ e.m = 0 ∧ e.p = 0 ∧ e.n = 0 := by
      intro q hq
      have h := hr q 0 (by simp)
      by_cases hx : ∃ e ∈ l, e.q = q ∧ e.m = 0
      · obtain ⟨e, he, rfl, hm⟩ := hx
        have := srcE_of_mem hl he
        rw [hm, h] at this
        simp only [rf, hq, if_false, Option.some.injEq, Prod.mk.injEq] at this
        exact ⟨e, he, rfl, hm, this.1.symm, this.2.symm⟩
      · rw [srcE_of_not_mem (fun x hx' hh => hx ⟨x, hx', hh⟩)] at h
        simp [own, rf, hq] at h
    obtain ⟨e₁, he₁, hq₁, -, hp₁, hn₁⟩ := get 1 (by decide)
    obtain ⟨e₂, he₂, hq₂, -, hp₂, hn₂⟩ := get 2 (by decide)
    have := (valid_cond hl).1 e₁ (by simpa using he₁) e₂ (by simpa using he₂) 0 1
      (by rw [← hp₁, time_p, hn₁]) (by rw [← hp₂, time_p, hn₂])
    rw [this, hq₂] at hq₁
    exact absurd hq₁ (by decide)

end ImagExec

#print axioms ImagExec.valid_cond
#print axioms ImagExec.cond_valid
#print axioms ImagExec.srcE_eq_iff
#print axioms ImagExec.valid_unique
#print axioms ImagExec.not_unique_four
#print axioms ImagExec.thm3_ii
#print axioms ImagExec.thm3_ii_strong
#print axioms ImagExec.thm3_i
#print axioms ImagExec.tunnel_not_e0_three
