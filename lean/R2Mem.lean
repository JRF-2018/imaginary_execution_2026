/-
  report2 §4.5・§4.6: 記憶のある相手(スケジュールを選べない観測)と、補題 S・定理 K

  Author: JRF / 形式化: Claude Opus 5.5
  Lean 4 v4.34.1 + Mathlib v4.34.1
-/
import Mathlib

set_option autoImplicit false

namespace ImagExec.R2M

open Classical

variable {S : Type}

/-! ## 1. 記憶のある相手との実行

プロセス `X` は CS の関数の列(記憶なし)。相手 `Q` は、それまでに読んだ値の列(履歴)から書く値を決める
(記憶のある相手)。相手は `T` 回打つ。`Reach X Q T c h s z` は、`X` が `c` 個の CS を終え、
相手の履歴が `h`、状態が `s` のところから、あるスケジュールで最終状態 `z` に着くことを表す。 -/

/-- `seg X i j q`: `X` の `i` 番目から `j` 番目の手前までの CS を `q` に順に施す(0 始まり)。
`seg X j X.length` が §4.5 の接尾写像 `s_j` である。 -/
def seg (X : List (S → S)) (i : ℕ) : ℕ → S → S
  | 0, q => q
  | j + 1, q => if i ≤ j then X.getD j id (seg X i j q) else q

theorem seg_self (X : List (S → S)) (i : ℕ) (q : S) : seg X i i q = q := by
  cases i with
  | zero => rfl
  | succ j => simp [seg]

theorem seg_succ (X : List (S → S)) {i j : ℕ} (h : i ≤ j) (q : S) :
    seg X i (j + 1) q = X.getD j id (seg X i j q) := by
  simp [seg, h]

theorem seg_cons (X : List (S → S)) {i j : ℕ} (h : i < j) (q : S) :
    seg X i j q = seg X (i + 1) j (X.getD i id q) := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
    · rw [seg_succ X (by omega), seg_succ X (by omega), ih h']
    · subst h'
      rw [seg_succ X le_rfl, seg_self, seg_self]

inductive Reach (X : List (S → S)) (Q : List S → S) (T : ℕ) : ℕ → List S → S → S → Prop
  /-- `X` も相手も打ち終えた。 -/
  | done {c : ℕ} {h : List S} {s : S} : c = X.length → h.length = T → Reach X Q T c h s s
  /-- `X` が次の CS を実行する。 -/
  | stepX {c : ℕ} {h : List S} {s z : S} : c < X.length →
      Reach X Q T (c + 1) h (X.getD c id s) z → Reach X Q T c h s z
  /-- 相手が状態 `s` を読み(履歴に足し)、履歴から決めた値を書く。 -/
  | stepQ {c : ℕ} {h : List S} {s z : S} : h.length < T →
      Reach X Q T c (h ++ [s]) (Q (h ++ [s])) z → Reach X Q T c h s z

/-- 観測: 初期状態 `init` から着きうる最終状態の集合。 -/
def obs (X : List (S → S)) (Q : List S → S) (T : ℕ) (init : S) : Set S :=
  {z | Reach X Q T 0 [] init z}

/-- 相手が(ある履歴の集合 `D` の上で)読んだ値をそのまま書き戻すなら、
最終状態は今の状態から `X` を最後まで走らせたものになる。 -/
theorem reach_copy (X : List (S → S)) (Q : List S → S) (T : ℕ) (D : List S → Prop)
    (hD : ∀ h s, D h → D (h ++ [s])) (hQ : ∀ h s, D h → Q (h ++ [s]) = s)
    {c : ℕ} {h : List S} {s z : S} (hr : Reach X Q T c h s z) (hd : D h) :
    z = seg X c X.length s := by
  induction hr with
  | done hc _ => subst hc; rw [seg_self]
  | stepX hc _ ih => rw [ih hd, ← seg_cons X hc]
  | @stepQ c h s z _ _ ih =>
    have := ih (hD h s hd)
    rwa [hQ h s hd] at this

/-- 相手が打ち終えていれば、`X` は最後まで走る。 -/
theorem reach_runX (X : List (S → S)) (Q : List S → S) (T : ℕ) {h : List S}
    (hT : h.length = T) : ∀ (k c : ℕ) (s : S), X.length - c = k → c ≤ X.length →
      Reach X Q T c h s (seg X c X.length s) := by
  intro k
  induction k with
  | zero =>
    intro c s hk hc
    have : c = X.length := by omega
    subst this
    rw [seg_self]
    exact Reach.done rfl hT
  | succ k ih =>
    intro c s hk hc
    have hlt : c < X.length := by omega
    rw [seg_cons X hlt]
    exact Reach.stepX hlt (ih (c + 1) _ (by omega) (by omega))

/-- 相手が残りの `n` 手を続けて打つ(自分の書いた値だけを読む)とき、最後に書く値。 -/
def lastW (Q : List S → S) : ℕ → List S → S → S
  | 0, _, s => s
  | n + 1, h, s => lastW Q n (h ++ [s]) (Q (h ++ [s]))

/-- `X` が止まったまま相手が打ち切り、その後で `X` が最後まで走るスケジュール。 -/
theorem reach_freeze (X : List (S → S)) (Q : List S → S) (T : ℕ) :
    ∀ (n c : ℕ) (h : List S) (s : S), T - h.length = n → h.length ≤ T → c ≤ X.length →
      Reach X Q T c h s (seg X c X.length (lastW Q n h s)) := by
  intro n
  induction n with
  | zero =>
    intro c h s hn hT hc
    exact reach_runX X Q T (by omega) _ c s rfl hc
  | succ n ih =>
    intro c h s hn hT hc
    exact Reach.stepQ (by omega) (ih c _ _ (by simp; omega) (by simp; omega) hc)

/-! ## 2. 補題 S: 避けさせることは、一手で潰すことに尽きる

相手がある手番で書いた直後(履歴 `h`、書いた値 `q`)、`X` の位置の可能性が `B` だとする。
どの位置から続けても `X` が `v` に着かないなら、`B` を `v` について潰す値 `w` がある。
逆に、潰す値を書いてあとは読んだ値を写すだけの相手なら、`X` は `v` に着かない。 -/

/-- **補題 S(⇒).** -/
theorem lemmaS (X : List (S → S)) (Q : List S → S) (T : ℕ) (h : List S) (q v : S)
    (B : Set ℕ) (hB : ∀ j ∈ B, j ≤ X.length) (hT : h.length ≤ T)
    (havoid : ∀ j ∈ B, ∀ z, Reach X Q T j h q z → z ≠ v) :
    ∃ w, ∀ j ∈ B, seg X j X.length w ≠ v :=
  ⟨lastW Q (T - h.length) h q, fun j hj =>
    havoid j hj _ (reach_freeze X Q T _ j h q rfl hT (hB j hj))⟩

/-- **補題 S(⇐).** 潰す値 `w` を書いた後、相手が読んだ値を写すだけなら、`X` は `v` に着かない。 -/
theorem lemmaS_conv (X : List (S → S)) (Q : List S → S) (T : ℕ) (D : List S → Prop)
    (hD : ∀ h s, D h → D (h ++ [s])) (hQ : ∀ h s, D h → Q (h ++ [s]) = s)
    (B : Set ℕ) (w v : S) (hw : ∀ j ∈ B, seg X j X.length w ≠ v)
    {j : ℕ} (hj : j ∈ B) {h : List S} (hd : D h) {z : S} (hr : Reach X Q T j h w z) : z ≠ v := by
  rw [reach_copy X Q T D hD hQ hr hd]
  exact hw j hj

/-! ## 2′. 定理 J の必要の向き: 避けさせる相手のもとでは、どの信念も潰せる

`Arr X Q T c h s` は、初期状態から(あるスケジュールで)`X` が `c` 個の CS を終え、相手の履歴が `h`、
状態が `s` という場面に来られることを表す。履歴 `h` で相手が書いた直後に `X` がいうる位置の集合
`{c | Arr X Q T c h (Q h)}` が、§4.5 の「信念」である。 -/

inductive Arr (X : List (S → S)) (Q : List S → S) (T : ℕ) (init : S) : ℕ → List S → S → Prop
  | start : Arr X Q T init 0 [] init
  | stepX {c : ℕ} {h : List S} {s : S} : Arr X Q T init c h s → c < X.length →
      Arr X Q T init (c + 1) h (X.getD c id s)
  | stepQ {c : ℕ} {h : List S} {s : S} : Arr X Q T init c h s → h.length < T →
      Arr X Q T init c (h ++ [s]) (Q (h ++ [s]))

theorem arr_le {X : List (S → S)} {Q : List S → S} {T : ℕ} {init : S} {c : ℕ} {h : List S} {s : S}
    (ha : Arr X Q T init c h s) : c ≤ X.length ∧ h.length ≤ T := by
  induction ha with
  | start => simp
  | stepX _ hc ih => exact ⟨hc, ih.2⟩
  | stepQ _ hT ih => exact ⟨ih.1, by simp; omega⟩

/-- 来られる場面からの実行は、初期状態からの実行につながる。 -/
theorem arr_reach {X : List (S → S)} {Q : List S → S} {T : ℕ} {init : S} {c : ℕ} {h : List S}
    {s : S} (ha : Arr X Q T init c h s) {z : S} (hr : Reach X Q T c h s z) : z ∈ obs X Q T init := by
  induction ha generalizing z with
  | start => exact hr
  | stepX _ hc ih => exact ih (Reach.stepX hc hr)
  | stepQ _ hT ih => exact ih (Reach.stepQ hT hr)

/-- **定理 J(必要の向き).** 相手 `Q` と組んだ `X` が決して `v` を出さないなら、どの履歴 `h` についても、
`Q` が書いた直後の `X` の信念は `v` について潰せる。 -/
theorem thmJ_nec (X : List (S → S)) (Q : List S → S) (T : ℕ) (init v : S)
    (hv : v ∉ obs X Q T init) (h : List S) (hT : h.length ≤ T) :
    ∃ w, ∀ c, Arr X Q T init c h (Q h) → seg X c X.length w ≠ v :=
  lemmaS X Q T h (Q h) v {c | Arr X Q T init c h (Q h)} (fun _ hc => (arr_le hc).1) hT
    (fun _ hc _ hr e => hv (e ▸ arr_reach hc hr))

/-- **定理 J の条件 1.** 最後の手番では、相手が実際に書いた値が信念を潰している
(`X` は、同じ読みの列のあとで `v` にならない)。 -/
theorem thmJ_last (X : List (S → S)) (Q : List S → S) (T : ℕ) (init v : S)
    (hv : v ∉ obs X Q T init) (h : List S) (hT : h.length = T) :
    ∀ c, Arr X Q T init c h (Q h) → seg X c X.length (Q h) ≠ v := by
  intro c hc e
  exact hv (e ▸ arr_reach hc (reach_runX X Q T hT _ c _ rfl (arr_le hc).1))

/-- 実行の終わりの場面(`X` も相手も打ち終えた)。 -/
theorem reach_arr {X : List (S → S)} {Q : List S → S} {T : ℕ} {init : S} {c : ℕ} {h : List S}
    {s z : S} (hr : Reach X Q T c h s z) (ha : Arr X Q T init c h s) :
    ∃ H, H.length = T ∧ Arr X Q T init X.length H z := by
  induction hr with
  | @done c h s hc hT => exact ⟨h, hT, hc ▸ ha⟩
  | stepX hc _ ih => exact ih (Arr.stepX ha hc)
  | stepQ hT _ ih => exact ih (Arr.stepQ ha hT)

theorem arr_seg {X : List (S → S)} {Q : List S → S} {T : ℕ} {init : S} {c' : ℕ} {h : List S}
    {q : S} (ha : Arr X Q T init c' h q) : ∀ k c, c = c' + k → c ≤ X.length →
      Arr X Q T init c h (seg X c' c q) := by
  intro k
  induction k with
  | zero =>
    intro c hc _
    obtain rfl : c = c' := by omega
    rw [seg_self]
    exact ha
  | succ k ih =>
    intro c hc hcl
    subst hc
    rw [← Nat.add_assoc, seg_succ X (by omega)]
    exact Arr.stepX (ih _ rfl (by omega)) (by omega)

/-- **定理 J(十分の向き).** `P` の実行が履歴 `H` のあとで `v` に着き、(1) `X` は同じ履歴のあとで `v` にならず、
(2) `H` から外れたどの読みでも `X` の信念が潰せるなら、`H` に従い、外れたら潰して写すだけの相手 `Q'` で区別できる。 -/
theorem thmJ_suff (P X : List (S → S)) (Q : List S → S) (T : ℕ) (init v : S) (H : List S)
    (hH : H.length = T) (hT : 1 ≤ T)
    (hP : Arr P Q T init P.length H v)
    (h1 : ∀ c, Arr X Q T init c H (Q H) → seg X c X.length (Q H) ≠ v)
    (h2 : ∀ h x, h <+: H → ¬ (h ++ [x]) <+: H → h.length < T →
      ∃ w, ∀ c, Arr X Q T init c h x → seg X c X.length w ≠ v) :
    ∃ Q' : List S → S, v ∈ obs P Q' T init ∧ v ∉ obs X Q' T init := by
  let K : List S → S := fun g =>
    if hk : ∃ w, ∀ c, Arr X Q T init c g.dropLast (g.getLastD init) → seg X c X.length w ≠ v
    then Classical.choose hk else init
  let Q' : List S → S := fun g =>
    if g <+: H then Q g else if g.dropLast <+: H then K g else g.getLastD init
  have pre_of : ∀ (g : List S) (x : S), (g ++ [x]) <+: H → g <+: H :=
    fun g x hg => (List.prefix_append g [x]).trans hg
  refine ⟨Q', ?_, ?_⟩
  · -- P の実行は Q' でもそのまま走る
    have transfer : ∀ {c h s}, Arr P Q T init c h s → h <+: H → Arr P Q' T init c h s := by
      intro c h s ha
      induction ha with
      | start => intro _; exact Arr.start
      | stepX _ hc ih => intro hp; exact Arr.stepX (ih hp) hc
      | @stepQ c h s _ hT' ih =>
        intro hp
        have := Arr.stepQ (ih (pre_of h s hp)) hT'
        simpa [Q', hp] using this
    exact arr_reach (transfer hP (List.prefix_refl H)) (Reach.done rfl hH)
  · intro hz
    -- 予想どおり(H の接頭辞)の履歴にいる間の不変条件
    have key : ∀ {c h s z}, Reach X Q' T c h s z → h <+: H →
        ((h = [] ∧ s = seg X 0 c init) ∨
          (h ≠ [] ∧ ∃ c', c' ≤ c ∧ Arr X Q T init c' h (Q h) ∧ s = seg X c' c (Q h))) →
        c ≤ X.length → z ≠ v := by
      intro c h s z hr
      induction hr with
      | @done c h s hc hT' =>
        intro hp hinv _
        have hhH : h = H := hp.eq_of_length (by rw [hT', hH])
        subst hhH
        rcases hinv with ⟨e, _⟩ | ⟨_, c', hc', ha, hs⟩
        · subst e; simp at hH; omega
        · rw [hs, hc]
          exact h1 c' ha
      | @stepX c h s z hc _ ih =>
        intro hp hinv _
        refine ih hp ?_ hc
        rcases hinv with ⟨e, hs⟩ | ⟨e, c', hc', ha, hs⟩
        · exact Or.inl ⟨e, by rw [hs, seg_succ X (Nat.zero_le _)]⟩
        · exact Or.inr ⟨e, c', by omega, ha, by rw [hs, seg_succ X hc']⟩
      | @stepQ c h s z hT' hr' ih =>
        intro hp hinv hcl
        -- 今の場面に Q のもとで来られる
        have hArr : Arr X Q T init c h s := by
          rcases hinv with ⟨e, hs⟩ | ⟨_, c', hc', ha, hs⟩
          · subst e; rw [hs]; exact arr_seg Arr.start c c (by omega) hcl
          · rw [hs]; exact arr_seg ha (c - c') c (by omega) hcl
        by_cases hp' : (h ++ [s]) <+: H
        · have hq : Q' (h ++ [s]) = Q (h ++ [s]) := by simp [Q', hp']
          rw [hq] at hr' ih
          exact ih hp' (Or.inr ⟨by simp, c, le_rfl, Arr.stepQ hArr hT', by rw [seg_self]⟩) hcl
        · -- 外れた: 潰す値を書き、あとは写すだけ
          have hz' := reach_copy X Q' T (fun g => ¬ g <+: H)
            (fun g t hg H' => hg (pre_of g t H'))
            (fun g t hg => by
              have : ¬ (g ++ [t]) <+: H := fun H' => hg (pre_of g t H')
              simp [Q', this, hg]) hr' hp'
          obtain ⟨w, hw⟩ := h2 h s hp hp' hT'
          have hk : ∃ w, ∀ c, Arr X Q T init c (h ++ [s]).dropLast ((h ++ [s]).getLastD init) →
              seg X c X.length w ≠ v := ⟨w, by
                rw [List.dropLast_concat, show (h ++ [s]).getLastD init = s by simp]
                exact hw⟩
          have e1 : (h ++ [s]).dropLast = h := List.dropLast_concat
          have e2 : (h ++ [s]).getLastD init = s := by simp
          have hq1 : Q' (h ++ [s]) = K (h ++ [s]) := by
            have hd : (h ++ [s]).dropLast <+: H := by rw [e1]; exact hp
            simp only [Q']
            rw [ite_eq_right_of_eq_false _ _ (eq_false hp'), ite_eq_left_of_eq_true _ _ (eq_true hd)]
          have hq2 : K (h ++ [s]) = Classical.choose hk := by
            simp only [K]
            rw [dite_eq_left_of_eq_true (eq_true hk)]
          rw [hz', hq1, hq2]
          have hArr' : Arr X Q T init c (h ++ [s]).dropLast ((h ++ [s]).getLastD init) := by
            rw [e1, e2]
            exact hArr
          exact Classical.choose_spec hk c hArr'
    exact key hz (List.nil_prefix) (Or.inl ⟨rfl, (seg_self X 0 init).symm⟩) (Nat.zero_le _) rfl

/-- **定理 J.** 記憶のある相手(少なくとも一手打つ)で「`P` は `v` を出しうるが `X` は出さない」ようにできる
⇔ ある相手 `Q` のもとで、`P` が履歴 `H` のあとで `v` に着き、(1)(2) が成り立つ。 -/
theorem thmJ (P X : List (S → S)) (init v : S) :
    (∃ (Q : List S → S) (T : ℕ), 1 ≤ T ∧ v ∈ obs P Q T init ∧ v ∉ obs X Q T init) ↔
    (∃ (Q : List S → S) (T : ℕ) (H : List S), 1 ≤ T ∧ H.length = T ∧
      Arr P Q T init P.length H v ∧
      (∀ c, Arr X Q T init c H (Q H) → seg X c X.length (Q H) ≠ v) ∧
      (∀ h x, h <+: H → ¬ (h ++ [x]) <+: H → h.length < T →
        ∃ w, ∀ c, Arr X Q T init c h x → seg X c X.length w ≠ v)) := by
  constructor
  · rintro ⟨Q, T, hT, hP, hX⟩
    obtain ⟨H, hH, hA⟩ := reach_arr hP Arr.start
    refine ⟨Q, T, H, hT, hH, hA, thmJ_last X Q T init v hX H hH, ?_⟩
    intro h x _ _ hl
    exact lemmaS X Q T h x v {c | Arr X Q T init c h x} (fun _ hc => (arr_le hc).1) hl.le
      (fun _ hc _ hr e => hX (e ▸ arr_reach hc hr))
  · rintro ⟨Q, T, H, hT, hH, hA, h1, h2⟩
    obtain ⟨Q', h3, h4⟩ := thmJ_suff P X Q T init v H hH hT hA h1 h2
    exact ⟨Q', T, hT, h3, h4⟩

/-! ## 3. 一歩ずつ付いていく相手(定理 K の相手)

値を出す側 `P`、避ける側 `X`。相手は `P.length + 1` 回打つ。1 回目は初期値を読むと予想し、
`t+1` 回目(`t < P.length`)には `y t` を書き、次に `P` の `t` 番目の CS の結果 `ev (t+1)` を読むと予想する。
最後に `v` を書く。予想と違う値を読んだら `kill`(履歴から決める潰す値)を書き、あとは読んだ値を写す。 -/

section Core

variable (P X : List (S → S)) (init : S) (y : ℕ → S) (v : S) (kill : List S → S)
  (probe : Option ℕ)

/-- 予想される読みの値。 -/
def ev : ℕ → S
  | 0 => init
  | t + 1 => P.getD t id (y t)

/-- 履歴が予想どおりである。 -/
def onPath (h : List S) : Prop :=
  h.length ≤ P.length + 1 ∧ ∀ i < h.length, h.getD i init = ev P init y i

/-- 一歩ずつ付いていく相手。 -/
noncomputable def partner (h : List S) : S :=
  if onPath P init y h then (if h.length ≤ P.length then y (h.length - 1) else v)
  else if onPath P init y h.dropLast then kill h else h.getLastD init

theorem onPath_nil : onPath P init y [] := ⟨by simp, fun i hi => by simp at hi⟩

theorem onPath_append (h : List S) (s : S) :
    onPath P init y (h ++ [s]) ↔
      onPath P init y h ∧ h.length + 1 ≤ P.length + 1 ∧ s = ev P init y h.length := by
  unfold onPath
  constructor
  · rintro ⟨hl, hi⟩
    simp only [List.length_append, List.length_singleton] at hl
    refine ⟨⟨by omega, fun i hi' => ?_⟩, by omega, ?_⟩
    · have := hi i (by simp; omega)
      rwa [List.getD_append _ _ _ _ hi'] at this
    · have := hi h.length (by simp)
      simpa using this
  · rintro ⟨⟨hl, hi⟩, hl2, hs⟩
    refine ⟨by simp; omega, fun i hi' => ?_⟩
    simp only [List.length_append, List.length_singleton] at hi'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with h1 | h1
    · rw [List.getD_append _ _ _ _ h1]
      exact hi i h1
    · subst h1
      simpa using hs

theorem partner_copy (h : List S) (s : S) (hn : ¬ onPath P init y h) :
    partner P init y v kill (h ++ [s]) = s := by
  have : ¬ onPath P init y (h ++ [s]) := fun H => hn ((onPath_append P init y h s).mp H).1
  simp [partner, this, hn]

theorem partner_kill (h : List S) (s : S) (hon : onPath P init y h)
    (hn : ¬ onPath P init y (h ++ [s])) :
    partner P init y v kill (h ++ [s]) = kill (h ++ [s]) := by
  simp [partner, hn, hon]

theorem partner_on (h : List S) (hon : onPath P init y h) (hl : h.length ≤ P.length) :
    partner P init y v kill h = y (h.length - 1) := by
  simp [partner, hon, hl]

theorem partner_last (h : List S) (hon : onPath P init y h) (hl : ¬ h.length ≤ P.length) :
    partner P init y v kill h = v := by
  simp [partner, hon, hl]

/-- 長さが同じ場合の探りの位置 `t0` を越えると、必要な CS が一つ増える。 -/
def bonus (k : ℕ) : ℕ :=
  match probe with
  | some t0 => if t0 + 1 < k then 1 else 0
  | none => 0

/-- `k` 回目の読みが予想どおりなら、`X` は少なくとも `need k` 個の CS を終えている。 -/
def need (k : ℕ) : ℕ := (k - 1) + bonus probe k

/-- 予想どおりに進んでいる間の不変条件。`cw` は最後に相手が書いたときの `X` の位置。 -/
def Inv (cw c : ℕ) (h : List S) (s : S) : Prop :=
  onPath P init y h ∧ c ≤ X.length ∧ (h = [] → s = seg X 0 c init) ∧
  (h ≠ [] → need probe h.length ≤ cw ∧ cw ≤ c ∧ s = seg X cw c (partner P init y v kill h) ∧
    (h.length = 1 → seg X 0 cw init = init))

theorem avoid
    (hmove : ∀ t < P.length, P.getD t id (y t) ≠ y t)
    (hprobe : ∀ t0, probe = some t0 →
      t0 < P.length ∧ X.getD t0 id (y t0) ≠ P.getD t0 id (y t0))
    (hfin : X.length < need probe (P.length + 1))
    (hk : ∀ cw c h s, Inv P X init y v kill probe cw c h s → ¬ onPath P init y (h ++ [s]) →
      seg X c X.length (kill (h ++ [s])) ≠ v)
    {c : ℕ} {h : List S} {s z : S}
    (hr : Reach X (partner P init y v kill) (P.length + 1) c h s z) :
    ∀ cw, Inv P X init y v kill probe cw c h s → z ≠ v := by
  induction hr with
  | @done c h s hc hT =>
    intro cw ⟨_, _, _, h4⟩
    have hne : h ≠ [] := by
      intro e
      subst e
      simp at hT
    obtain ⟨a, b, -⟩ := h4 hne
    rw [hT] at a
    omega
  | @stepX c h s z hc _ ih =>
    intro cw ⟨h1, h2, h3, h4⟩
    apply ih cw
    refine ⟨h1, by omega, fun e => by rw [h3 e, seg_succ X (Nat.zero_le _)], fun e => ?_⟩
    obtain ⟨a, b, d, f⟩ := h4 e
    exact ⟨a, by omega, by rw [d, seg_succ X b], f⟩
  | @stepQ c h s z hT hr' ih =>
    intro cw ⟨h1, h2, h3, h4⟩
    by_cases hon : onPath P init y (h ++ [s])
    · obtain ⟨-, hlen, hs⟩ := (onPath_append P init y h s).mp hon
      apply ih c
      refine ⟨hon, h2, fun e => by simp at e, fun _ => ⟨?_, le_rfl, by rw [seg_self], fun hl => ?_⟩⟩
      · simp only [List.length_append, List.length_singleton]
        by_cases hh : h = []
        · subst hh
          simp only [need, bonus, List.length_nil]
          cases probe <;> simp
        · obtain ⟨a, b, d, -⟩ := h4 hh
          have hk1 : 1 ≤ h.length := List.length_pos_iff.mpr hh
          rw [partner_on P init y v kill h h1 (by omega)] at d
          obtain ⟨k, hk⟩ : ∃ k, h.length = k + 1 := ⟨h.length - 1, by omega⟩
          rw [hk] at hs d a
          simp only [Nat.add_sub_cancel] at d
          have hev : ev P init y (k + 1) = P.getD k id (y k) := rfl
          rw [hev] at hs
          have hmv := hmove k (by omega)
          have hcw : cw ≠ c := by
            intro e
            subst e
            rw [seg_self] at d
            exact hmv (hs ▸ d)
          simp only [need, bonus] at a ⊢
          rw [hk]
          cases hp : probe with
          | none => simp only [hp] at a ⊢; omega
          | some t0 =>
            simp only [hp] at a ⊢
            by_cases e1 : t0 + 1 < k + 1
            · simp only [e1, ite_true] at a
              have : t0 + 1 < k + 1 + 1 := by omega
              simp only [this, ite_true]
              omega
            · simp only [e1, ite_false] at a
              by_cases e2 : t0 + 1 < k + 1 + 1
              · simp only [e2, ite_true]
                have ht0 : t0 = k := by omega
                rw [ht0] at hp
                by_contra hlt
                have hc' : c = cw + 1 := by omega
                have hcw' : cw = k := by omega
                subst hc' hcw'
                rw [seg_succ X le_rfl, seg_self] at d
                exact (hprobe _ hp).2 (d ▸ hs)
              · simp only [e2, ite_false]
                omega
      · have hh : h = [] := by
          simp only [List.length_append, List.length_singleton] at hl
          exact List.length_eq_zero_iff.mp (by omega)
        subst hh
        rw [← h3 rfl]
        simpa [ev] using hs
    · have hz := reach_copy X _ _ (fun g => ¬ onPath P init y g)
        (fun g t hg H => hg ((onPath_append P init y g t).mp H).1)
        (fun g t hg => partner_copy P init y v kill g t hg) hr' hon
      rw [hz, partner_kill P init y v kill h s h1 hon]
      exact hk cw c h s ⟨h1, h2, h3, h4⟩ hon

/-- 予想どおりの読みの列。 -/
def pre (k : ℕ) : List S := (List.range k).map (ev P init y)

theorem pre_succ (k : ℕ) : pre P init y (k + 1) = pre P init y k ++ [ev P init y k] := by
  simp [pre, List.range_succ]

theorem onPath_pre (k : ℕ) (hk : k ≤ P.length + 1) : onPath P init y (pre P init y k) := by
  refine ⟨by simpa [pre] using hk, fun i hi => ?_⟩
  simp only [pre, List.length_map, List.length_range] at hi
  simp [pre, List.getD_eq_getElem?_getD, hi]

theorem produce : ∀ n t, P.length - t = n → t ≤ P.length →
    Reach P (partner P init y v kill) (P.length + 1) t (pre P init y (t + 1))
      (partner P init y v kill (pre P init y (t + 1))) v := by
  intro n
  induction n with
  | zero =>
    intro t hn ht
    have htl : t = P.length := by omega
    subst htl
    rw [partner_last P init y v kill _ (onPath_pre P init y _ le_rfl) (by simp [pre])]
    exact Reach.done rfl (by simp [pre])
  | succ n ih =>
    intro t hn ht
    have htl : t < P.length := by omega
    rw [partner_on P init y v kill _ (onPath_pre P init y _ (by omega)) (by simp [pre]; omega)]
    simp only [pre, List.length_map, List.length_range, Nat.add_sub_cancel]
    refine Reach.stepX htl (Reach.stepQ (by simp; omega) ?_)
    have := ih (t + 1) (by omega) (by omega)
    rw [pre_succ] at this
    exact this

/-- **定理 K の核.** 条件のもとで、一歩ずつ付いていく相手と組むと、`P` は `v` を出しうるが、`X` は出さない。 -/
theorem core
    (hmove : ∀ t < P.length, P.getD t id (y t) ≠ y t)
    (hprobe : ∀ t0, probe = some t0 →
      t0 < P.length ∧ X.getD t0 id (y t0) ≠ P.getD t0 id (y t0))
    (hfin : X.length < need probe (P.length + 1))
    (hk : ∀ cw c h s, Inv P X init y v kill probe cw c h s → ¬ onPath P init y (h ++ [s]) →
      seg X c X.length (kill (h ++ [s])) ≠ v) :
    v ∈ obs P (partner P init y v kill) (P.length + 1) init ∧
      v ∉ obs X (partner P init y v kill) (P.length + 1) init := by
  constructor
  · show Reach _ _ _ 0 [] init v
    refine Reach.stepQ (by simp) ?_
    have := produce P init y v kill _ 0 rfl (Nat.zero_le _)
    simpa [pre, ev] using this
  · intro hz
    exact avoid P X init y v kill probe hmove hprobe hfin hk hz 0
      ⟨onPath_nil P init y, Nat.zero_le _, fun _ => (seg_self X 0 init).symm, fun e => absurd rfl e⟩ rfl

end Core

/-! ## 4. 定理 K

避ける側 `X` について、二つの場合に潰す値を用意する。

* **満ちていない**: ある `w` と `v` について、`w` を書いて手を引けば `X` はどこから走っても `v` にならない。
  このときはいつも `w` を書けばよい。CS が `|S| − 2` 個以下ならいつもこうなる。
* **軌跡がすべて異なる**: どの `w` についても `s_0(w), …, s_M(w)` がすべて違う(CS が `|S| − 1` 個で満ちた形)。
  `v = s_0(init)` とし、2 回目に最初に書いた値を読んで外れたときは `v` を、それ以外で外れたときは `init` を書く。 -/

/-- 満ちていない。 -/
def NotFull (X : List (S → S)) : Prop := ∃ w v : S, ∀ j ≤ X.length, seg X j X.length w ≠ v

/-- 軌跡がすべて異なる。 -/
def Distinct (X : List (S → S)) : Prop :=
  1 ≤ X.length ∧ ∀ (w : S) (i j : ℕ), i ≤ X.length → j ≤ X.length → i ≠ j →
    seg X i X.length w ≠ seg X j X.length w

theorem core_dir (P X : List (S → S)) (init : S) (y : ℕ → S) (probe : Option ℕ)
    (hL : 1 ≤ P.length)
    (hmove : ∀ t < P.length, P.getD t id (y t) ≠ y t)
    (hprobe : ∀ t0, probe = some t0 →
      t0 < P.length ∧ X.getD t0 id (y t0) ≠ P.getD t0 id (y t0))
    (hfin : X.length < need probe (P.length + 1))
    (hX : NotFull X ∨ Distinct X) :
    ∃ (Q : List S → S) (T : ℕ), obs P Q T init ≠ obs X Q T init := by
  rcases hX with ⟨w, v, hw⟩ | hd
  · obtain ⟨h1, h2⟩ := core P X init y v (fun _ => w) probe hmove hprobe hfin
      (fun cw c h s hinv _ => hw c hinv.2.1)
    exact ⟨_, _, fun e => h2 (e ▸ h1)⟩
  · set V := seg X 0 X.length init with hV
    let kill : List S → S := fun h => if h.length = 2 ∧ h.getD 1 init = y 0 then V else init
    have hk : ∀ cw c h s, Inv P X init y V kill probe cw c h s →
        ¬ onPath P init y (h ++ [s]) → seg X c X.length (kill (h ++ [s])) ≠ V := by
      intro cw c h s ⟨i1, i2, i3, i4⟩ hn
      simp only [kill]
      split_ifs with hc
      · obtain ⟨hl2, hs1⟩ := hc
        simp only [List.length_append, List.length_singleton] at hl2
        have hl1 : h.length = 1 := by omega
        have hget : (h ++ [s]).getD h.length init = s := by simp
        rw [hl1] at hget
        rw [hget] at hs1
        have hne : h ≠ [] := by
          intro e
          subst e
          simp at hl1
        obtain ⟨-, b, d, f⟩ := i4 hne
        rw [partner_on P init y V kill h i1 (by omega), hl1] at d
        simp only [Nat.sub_self] at d
        intro e
        have hcM : c = X.length := by
          by_contra hcM
          exact hd.2 V c X.length i2 le_rfl hcM (e.trans (seg_self X _ V).symm)
        rw [hcM] at d b
        by_cases hcw : cw = X.length
        · rw [hcw] at f
          exact hd.2 init 0 X.length (Nat.zero_le _) le_rfl (by have := hd.1; omega)
            ((f hl1).trans (seg_self X _ init).symm)
        · exact hd.2 (y 0) cw X.length b le_rfl hcw
            ((d.symm.trans hs1).trans (seg_self X _ (y 0)).symm)
      · suffices hc0 : c ≠ 0 from hd.2 init c 0 i2 (Nat.zero_le _) hc0
        intro hc0
        subst hc0
        by_cases hh : h = []
        · subst hh
          apply hn
          rw [onPath_append]
          refine ⟨onPath_nil P init y, by simp, ?_⟩
          rw [i3 rfl, seg_self]
          rfl
        · obtain ⟨a, b, d, -⟩ := i4 hh
          have hk1 : 1 ≤ h.length := List.length_pos_iff.mpr hh
          simp only [need] at a
          have hl1 : h.length = 1 := by omega
          have hcw : cw = 0 := by omega
          subst hcw
          rw [seg_self, partner_on P init y V kill h i1 (by omega), hl1] at d
          apply hc
          refine ⟨by simp [hl1], ?_⟩
          have hget : (h ++ [s]).getD h.length init = s := by simp
          rw [hl1] at hget
          rw [hget, d]
    obtain ⟨h1, h2⟩ := core P X init y V kill probe hmove hprobe hfin hk
    exact ⟨_, _, fun e => h2 (e ▸ h1)⟩

theorem exists_mover (P : List (S → S)) (hP : ∀ f ∈ P, f ≠ id) (d : S) :
    ∃ y : ℕ → S, ∀ t < P.length, P.getD t id (y t) ≠ y t := by
  have : ∀ t, ∃ x : S, t < P.length → P.getD t id x ≠ x := by
    intro t
    by_cases ht : t < P.length
    · obtain ⟨x, hx⟩ := Function.ne_iff.mp (hP _ (List.getElem_mem ht))
      exact ⟨x, fun _ => by rwa [List.getD_eq_getElem _ _ ht]⟩
    · exact ⟨d, fun h => absurd h ht⟩
  choose y hy using this
  exact ⟨y, fun t ht => hy t ht⟩

/-- 長い方が値を出す側になる場合。 -/
theorem dir_long (P X : List (S → S)) (init : S) (hP : ∀ f ∈ P, f ≠ id)
    (hlt : X.length < P.length) (hX : NotFull X ∨ Distinct X) :
    ∃ (Q : List S → S) (T : ℕ), obs P Q T init ≠ obs X Q T init := by
  obtain ⟨y, hy⟩ := exists_mover P hP init
  exact core_dir P X init y none (by omega) hy (fun t0 h => by cases h)
    (by simp [need, bonus]; omega) hX

/-- 長さが同じで、`t0` 番目の CS が `b` で違い、`P` の側が `b` を動かす場合。 -/
theorem dir_probe (P X : List (S → S)) (init : S) (hP : ∀ f ∈ P, f ≠ id)
    (hlen : X.length = P.length) (t0 : ℕ) (ht0 : t0 < P.length) (b : S)
    (hb : P.getD t0 id b ≠ b) (hdiff : X.getD t0 id b ≠ P.getD t0 id b)
    (hX : NotFull X ∨ Distinct X) :
    ∃ (Q : List S → S) (T : ℕ), obs P Q T init ≠ obs X Q T init := by
  obtain ⟨y, hy⟩ := exists_mover P hP init
  let y' : ℕ → S := fun t => if t = t0 then b else y t
  refine core_dir P X init y' (some t0) (by omega) ?_ ?_ ?_ hX
  · intro t ht
    by_cases e : t = t0
    · subst e
      simpa [y'] using hb
    · simpa [y', e] using hy t ht
  · intro t h
    cases h
    exact ⟨ht0, by simpa [y'] using hdiff⟩
  · have : t0 + 1 < P.length + 1 := by omega
    simp [need, bonus, this]
    omega

/-- **定理 K.** 恒等写像の CS を含まない異なる二つのプロセスが、それぞれ「満ちていない」か
「軌跡がすべて異なる」なら、記憶のある相手で区別できる。 -/
theorem thmK (P X : List (S → S)) (init : S) (hP : ∀ f ∈ P, f ≠ id) (hX : ∀ f ∈ X, f ≠ id)
    (hne : P ≠ X) (hPc : NotFull P ∨ Distinct P) (hXc : NotFull X ∨ Distinct X) :
    ∃ (Q : List S → S) (T : ℕ), obs P Q T init ≠ obs X Q T init := by
  rcases lt_trichotomy X.length P.length with hlt | heq | hgt
  · exact dir_long P X init hP hlt hXc
  · have : ∃ t0 < P.length, P.getD t0 id ≠ X.getD t0 id := by
      by_contra hall
      push Not at hall
      apply hne
      apply List.ext_getElem heq.symm
      intro i h1 h2
      have := hall i h1
      rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this
    obtain ⟨t0, ht0, hd⟩ := this
    obtain ⟨b, hb⟩ := Function.ne_iff.mp hd
    by_cases hPb : P.getD t0 id b ≠ b
    · exact dir_probe P X init hP heq t0 ht0 b hPb (Ne.symm hb) hXc
    · push Not at hPb
      obtain ⟨Q, T, hQ⟩ := dir_probe X P init hX heq.symm t0 (by omega) b
        (fun e => hb (hPb.trans e.symm)) hb hPc
      exact ⟨Q, T, Ne.symm hQ⟩
  · obtain ⟨Q, T, hQ⟩ := dir_long X P init hX hgt hPc
    exact ⟨Q, T, Ne.symm hQ⟩

/-- CS が `|S| − 1` 個以下なら、「満ちていない」か「軌跡がすべて異なる」。 -/
theorem notFull_or_distinct [Fintype S] [Nontrivial S] (X : List (S → S))
    (hlen : X.length + 1 ≤ Fintype.card S) : NotFull X ∨ Distinct X := by
  by_cases hnf : NotFull X
  · exact Or.inl hnf
  right
  simp only [NotFull, not_exists, not_forall, not_not] at hnf
  by_cases hM : X.length = 0
  · exfalso
    obtain ⟨a, c, hac⟩ := exists_pair_ne S
    obtain ⟨j, hj, e⟩ := hnf a c
    have : j = X.length := by omega
    rw [this, seg_self] at e
    exact hac e
  refine ⟨by omega, fun w i j hi hj hij heq => hij ?_⟩
  let f : ℕ → S := fun j => seg X j X.length w
  have hsurj : (Finset.range (X.length + 1)).image f = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro v
    obtain ⟨j, hj, e⟩ := hnf w v
    exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), e⟩
  have hcard : ((Finset.range (X.length + 1)).image f).card = (Finset.range (X.length + 1)).card := by
    apply le_antisymm Finset.card_image_le
    rw [hsurj, Finset.card_univ, Finset.card_range]
    exact hlen
  exact Finset.card_image_iff.mp hcard (by simp; omega) (by simp; omega) heq

/-- **系(予想 2″ の CS ≦ |S| − 1 の部分).** 恒等写像の CS を含まない二つのプロセスの CS がどちらも
`|S| − 1` 個以下なら、異なるプロセスは記憶のある相手で区別できる。 -/
theorem thmK_card [Fintype S] (P X : List (S → S)) (init : S) (hP : ∀ f ∈ P, f ≠ id)
    (hX : ∀ f ∈ X, f ≠ id) (hne : P ≠ X)
    (hPl : P.length + 1 ≤ Fintype.card S) (hXl : X.length + 1 ≤ Fintype.card S) :
    ∃ (Q : List S → S) (T : ℕ), obs P Q T init ≠ obs X Q T init := by
  have : Nontrivial S := by
    have : ∃ f, f ∈ P ∨ f ∈ X := by
      rcases P with _ | ⟨f, _⟩
      · rcases X with _ | ⟨g, _⟩
        · exact absurd rfl hne
        · exact ⟨g, Or.inr (by simp)⟩
      · exact ⟨f, Or.inl (by simp)⟩
    obtain ⟨f, hf⟩ := this
    obtain ⟨x, hx⟩ := Function.ne_iff.mp (hf.elim (hP f) (hX f))
    exact ⟨⟨f x, x, hx⟩⟩
  exact thmK P X init hP hX hne (notFull_or_distinct P hPl) (notFull_or_distinct X hXl)

/-- **系.** 長さが違うとき、短い方の CS が `|S| − 1` 個以下なら、長い方がどれほど長くても区別できる。 -/
theorem thmK_long [Fintype S] (P X : List (S → S)) (init : S) (hP : ∀ f ∈ P, f ≠ id)
    (hlt : X.length < P.length) (hXl : X.length + 1 ≤ Fintype.card S) :
    ∃ (Q : List S → S) (T : ℕ), obs P Q T init ≠ obs X Q T init := by
  have : Nontrivial S := by
    obtain ⟨x, hx⟩ := Function.ne_iff.mp (hP _ (List.getElem_mem (by omega : 0 < P.length)))
    exact ⟨⟨_, x, hx⟩⟩
  exact dir_long P X init hP hlt (notFull_or_distinct X hXl)

end ImagExec.R2M

#print axioms ImagExec.R2M.lemmaS
#print axioms ImagExec.R2M.lemmaS_conv
#print axioms ImagExec.R2M.thmJ_nec
#print axioms ImagExec.R2M.thmJ_last
#print axioms ImagExec.R2M.thmJ_suff
#print axioms ImagExec.R2M.thmJ
#print axioms ImagExec.R2M.thmK
#print axioms ImagExec.R2M.thmK_card
#print axioms ImagExec.R2M.thmK_long
