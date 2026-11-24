/-
  report2 の中心問題: 部品の意味に必要な虚の入力(スケジュールを選べる検査者のもとで)

  Author: JRF / 形式化: Claude Opus 5.5
  Lean 4 v4.34.1 + Mathlib v4.34.1
-/
import Mathlib

set_option autoImplicit false

namespace ImagExec.R2H

variable {S : Type}

/-! ## 1. インタリーブは「ブロックの割り込み」に分解できる

プロセス `P` は CS の関数の列(記憶なし)。相手 `Q` も関数の列。
`P` と `Q` のインタリーブを実行した結果は、`Q` を `P.length + 1` 個の連続したブロックに分け、
`P` の各 CS の前(と最後)にブロックの合成を割り込ませた結果に等しい。 -/

/-- 関数の列を順に施す。 -/
def runSeq (fs : List (S → S)) (x : S) : S := fs.foldl (fun s f => f s) x

/-- 二つの列のインタリーブをすべて並べる。 -/
def inter {α : Type} : List α → List α → List (List α)
  | [], ys => [ys]
  | xs, [] => [xs]
  | x :: xs, y :: ys => (inter xs (y :: ys)).map (x :: ·) ++ (inter (x :: xs) ys).map (y :: ·)

/-- ブロック `B = [b₀, b₁, …, b_L]` を `P` の各 CS の前と最後に割り込ませて実行する。 -/
def runB : List (S → S) → List (List (S → S)) → S → S
  | [], [b], x => runSeq b x
  | f :: fs, b :: bs, x => runB fs bs (f (runSeq b x))
  | _, _, x => x

theorem runSeq_cons (f : S → S) (fs : List (S → S)) (x : S) :
    runSeq (f :: fs) x = runSeq fs (f x) := rfl

theorem runSeq_nil (x : S) : runSeq ([] : List (S → S)) x = x := rfl

/-- 空のブロックだけを割り込ませると、`P` をそのまま走らせたのと同じ。 -/
theorem runB_empty (fs : List (S → S)) (x : S) :
    runB fs (List.replicate (fs.length + 1) []) x = runSeq fs x := by
  induction fs generalizing x with
  | nil => rfl
  | cons f fs ih =>
    show runB fs (List.replicate (fs.length + 1) []) (f (runSeq [] x)) = runSeq (f :: fs) x
    rw [ih]; rfl

/-- **分解の補題.** `P` と `Q` のどのインタリーブも、`Q` を `P.length + 1` 個の連続ブロックに
分けて割り込ませた実行に等しい。 -/
theorem inter_blocks (fs qs : List (S → S)) :
    ∀ seq ∈ inter fs qs, ∃ B : List (List (S → S)),
      B.flatten = qs ∧ B.length = fs.length + 1 ∧ ∀ x, runSeq seq x = runB fs B x := by
  induction fs generalizing qs with
  | nil =>
    intro seq hseq
    cases qs <;> simp [inter] at hseq <;> subst hseq
    · exact ⟨[[]], by simp, by simp, fun x => rfl⟩
    · rename_i q qs
      exact ⟨[q :: qs], by simp, by simp, fun x => rfl⟩
  | cons f fs ihf =>
    induction qs with
    | nil =>
      intro seq hseq
      simp [inter] at hseq; subst hseq
      refine ⟨List.replicate (fs.length + 2) [], by simp, by simp, fun x => ?_⟩
      show runSeq (f :: fs) x = runB fs (List.replicate (fs.length + 1) []) (f (runSeq [] x))
      rw [runB_empty]; rfl
    | cons q qs ihq =>
      intro seq hseq
      simp only [inter, List.mem_append, List.mem_map] at hseq
      rcases hseq with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
      · -- f が先
        obtain ⟨B, hB1, hB2, hB3⟩ := ihf (q :: qs) s hs
        refine ⟨[] :: B, by simp [hB1], by simp [hB2], fun x => ?_⟩
        rw [runSeq_cons, hB3]; rfl
      · -- q が先
        obtain ⟨B, hB1, hB2, hB3⟩ := ihq s hs
        cases B with
        | nil => simp at hB2
        | cons b B =>
          refine ⟨(q :: b) :: B, by simp [← hB1], by simp at hB2 ⊢; omega, fun x => ?_⟩
          rw [runSeq_cons, hB3]; rfl

/-- 逆に、どんなブロックの組も、適当な `Q` とインタリーブで実現できる(検査者はスケジュールを選べる)。 -/
theorem blocks_realizable (fs : List (S → S)) (B : List (List (S → S)))
    (hB : B.length = fs.length + 1) :
    ∃ seq ∈ inter fs B.flatten, ∀ x, runSeq seq x = runB fs B x := by
  induction fs generalizing B with
  | nil =>
    match B, hB with
    | [b], _ =>
      refine ⟨b, ?_, fun x => rfl⟩
      cases b <;> simp [inter]
  | cons f fs ih =>
    match B, hB with
    | b :: B', hB' =>
      have hB'' : B'.length = fs.length + 1 := by simp at hB'; omega
      obtain ⟨s, hs, hrun⟩ := ih B' hB''
      -- まず b を全部先に、次に f、残りは s
      have key : ∀ (b : List (S → S)), ∃ seq ∈ inter (f :: fs) (b ++ B'.flatten),
          ∀ x, runSeq seq x = runB fs B' (f (runSeq b x)) := by
        intro b
        induction b with
        | nil =>
          refine ⟨f :: s, ?_, fun x => ?_⟩
          · cases hfl : B'.flatten with
            | nil =>
              rw [hfl] at hs
              simp only [List.nil_append, inter]
              cases fs <;> simp_all [inter]
            | cons y ys =>
              rw [hfl] at hs
              simp only [List.nil_append, inter, List.mem_append, List.mem_map]
              exact Or.inl ⟨s, hs, rfl⟩
          · rw [runSeq_cons, hrun]; rfl
        | cons q b ihb =>
          obtain ⟨s', hs', hrun'⟩ := ihb
          refine ⟨q :: s', ?_, fun x => ?_⟩
          · simp only [List.cons_append, inter, List.mem_append, List.mem_map]
            exact Or.inr ⟨s', hs', rfl⟩
          · rw [runSeq_cons, hrun']; rfl
      obtain ⟨seq, hseq, hr⟩ := key b
      exact ⟨seq, by simpa using hseq, fun x => by rw [hr]; rfl⟩

/-! ## 2. 定理 H: 完全抽象な意味 = 各 lock での一回の割り込み

検査者は相手 `Q` とスケジュールを選び、初期状態 `init` から最終状態を観測する。
二つのプロセスが **検査で区別できない** とは、どんな `Q` とスケジュールでも観測が同じこと。
分解の補題と実現可能性から、それはブロックの組 `B` ごとに `runB` が同じことと同値で、
さらに **各 CS の前に一つずつ任意の関数を割り込ませた実行** が同じことと同値になる。 -/

/-- 各 CS の前に関数 `h` を一つずつ割り込ませ、最後に `hL` を施す(割り込みの意味)。 -/
def runI : List (S → S) → List (S → S) → S → S
  | f :: fs, h :: hs, x => runI fs hs (f (h x))
  | _, _, x => x

/-- 検査で区別できない(同じ長さのプロセスについて、同じスケジュールの形で比べる)。 -/
def TestEq (init : S) (P P' : List (S → S)) : Prop :=
  ∀ B : List (List (S → S)), B.length = P.length + 1 → runB P B init = runB P' B init

theorem runB_singletons (fs hs : List (S → S)) (hL : S → S) (hlen : hs.length = fs.length) (x : S) :
    runB fs ((hs ++ [hL]).map (fun h => [h])) x = hL (runI fs hs x) := by
  induction fs generalizing hs x with
  | nil =>
    cases hs with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons f fs ih =>
    cases hs with
    | nil => simp at hlen
    | cons h hs =>
      simp at hlen
      show runB fs ((hs ++ [hL]).map (fun h => [h])) (f (runSeq [h] x)) = hL (runI fs hs (f (h x)))
      rw [ih hs hlen]; rfl

/-- 一般のブロックの実行は、ブロックを合成した関数を一つずつ割り込ませた実行に等しい。 -/
theorem runB_eq_runI (fs : List (S → S)) (B : List (List (S → S)))
    (hB : B.length = fs.length + 1) (x : S) :
    runB fs B x = runSeq (B.getLast (by intro h; rw [h] at hB; simp at hB))
      (runI fs ((B.dropLast).map runSeq) x) := by
  induction fs generalizing B x with
  | nil =>
    match B, hB with
    | [b], _ => rfl
  | cons f fs ih =>
    match B, hB with
    | b :: B', hB' =>
      have hB'' : B'.length = fs.length + 1 := by simp at hB'; omega
      have hne : B' ≠ [] := by intro h; rw [h] at hB''; simp at hB''
      show runB fs B' (f (runSeq b x)) = _
      rw [ih B' hB'']
      have : (b :: B').dropLast = b :: B'.dropLast := List.dropLast_cons_of_ne_nil hne
      simp only [this, List.map_cons, runI, List.getLast_cons hne]

/-- **定理 H.** 同じ長さの二つのプロセスについて、次は同値:
(1) どんな相手とスケジュールで検査しても区別できない、
(2) どの CS の前にも任意の関数を一つずつ割り込ませた実行が、どの状態から始めても一致する。 -/
theorem thmH (init : S) (P P' : List (S → S)) (hlen : P'.length = P.length) :
    TestEq init P P' ↔ ∀ (hs : List (S → S)) (x : S), hs.length = P.length →
      runI P hs x = runI P' hs x := by
  constructor
  · intro h hs x hhs
    -- 最初の割り込みを「x を書く」にすれば、初期状態によらず x から始められる
    cases hs with
    | nil =>
      cases P with
      | nil => cases P' with
        | nil => rfl
        | cons _ _ => simp at hlen
      | cons _ _ => simp at hhs
    | cons h₀ hs =>
      have hhs' : hs.length + 1 = P.length := by simpa using hhs
      have e := h ((((fun _ => h₀ x) :: hs) ++ [id]).map (fun g => [g])) (by simp; omega)
      rw [runB_singletons _ _ _ (by simp; omega), runB_singletons _ _ _ (by simp; omega)] at e
      cases P with
      | nil => simp at hhs
      | cons f fs =>
        cases P' with
        | nil => simp at hlen
        | cons f' fs' => simpa [runI] using e
  · intro h B hB
    rw [runB_eq_runI P B hB, runB_eq_runI P' B (by rw [hlen]; exact hB)]
    congr 1
    exact h _ _ (by simp [hB])

/-! ## 2′. 定理 H (3): どの lock の割り込みも省けない

各 lock `i` について、`i` 番目の CS の前で割り込まない検査では区別できないが、そこで割り込めば区別できる
二つのプロセスがある。`i ≥ 1` では、`P` の `i−1` 番目の CS が「`a` を書く」でほかは何もしない、`P'` はさらに
`i` 番目の CS も「`a` を書く」。`i = 0` では、初期状態でだけ一致する二つの関数(定数 `init` と恒等写像)。 -/

theorem runI_append (A B hs₁ hs₂ : List (S → S)) (h : hs₁.length = A.length) (x : S) :
    runI (A ++ B) (hs₁ ++ hs₂) x = runI B hs₂ (runI A hs₁ x) := by
  induction A generalizing hs₁ x with
  | nil =>
    cases hs₁ with
    | nil => rfl
    | cons _ _ => simp at h
  | cons f A ih =>
    cases hs₁ with
    | nil => simp at h
    | cons g hs₁ =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      exact ih hs₁ h (f (g x))

theorem runI_ids (n : ℕ) (x : S) :
    runI (List.replicate n id) (List.replicate n id) x = x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact ih x

/-- 長さ `L` の列を、`i` 番目の要素とその前後に分ける。 -/
theorem split_at (hs : List (S → S)) (i : ℕ) (hi : i < hs.length) :
    hs = hs.take i ++ hs.getD i id :: hs.drop (i + 1) := by
  rw [List.getD_eq_getElem _ _ hi]
  simp

/-- **定理 H (3).** どの lock `i` についても、そこでの割り込みを省いた検査では区別できないが、
そこで割り込めば区別できる二つのプロセスがある。 -/
theorem thmH3 [Nontrivial S] (init : S) (L i : ℕ) (hi : i < L) :
    ∃ P P' : List (S → S), P.length = L ∧ P'.length = L ∧
      (∀ hs : List (S → S), hs.length = L → hs.getD i id = id →
        runI P hs init = runI P' hs init) ∧
      ∃ hs : List (S → S), hs.length = L ∧ runI P hs init ≠ runI P' hs init := by
  obtain ⟨b, hb⟩ := exists_ne init
  cases i with
  | zero =>
    -- 定数 init と恒等写像: 初期状態でだけ一致する
    refine ⟨(fun _ => init) :: List.replicate (L - 1) id, id :: List.replicate (L - 1) id,
      by simp; omega, by simp; omega, ?_, ?_⟩
    · intro hs hlen h0
      obtain ⟨g, hs', rfl⟩ : ∃ g hs', hs = g :: hs' := by
        cases hs with
        | nil => simp at hlen; omega
        | cons g hs' => exact ⟨g, hs', rfl⟩
      simp only [List.getD_cons_zero] at h0
      subst h0
      rfl
    · refine ⟨(fun _ => b) :: List.replicate (L - 1) id, by simp; omega, ?_⟩
      show runI (List.replicate (L - 1) id) (List.replicate (L - 1) id) init ≠
        runI (List.replicate (L - 1) id) (List.replicate (L - 1) id) b
      rw [runI_ids, runI_ids]
      exact hb.symm
  | succ k =>
    let A : List (S → S) := List.replicate k id
    let C : List (S → S) := List.replicate (L - k - 2) id
    refine ⟨A ++ (fun _ => init) :: id :: C, A ++ (fun _ => init) :: (fun _ => init) :: C,
      by simp [A, C]; omega, by simp [A, C]; omega, ?_, ?_⟩
    · intro hs hlen hi'
      have hk : k < hs.length := by omega
      have hk1 : k + 1 < hs.length := by omega
      obtain ⟨T, h0, h1, R, rfl, hT⟩ : ∃ T h0 h1 R, hs = T ++ h0 :: h1 :: R ∧ T.length = k := by
        refine ⟨hs.take k, hs[k], hs[k + 1], hs.drop (k + 2), ?_, by simp; omega⟩
        conv_lhs => rw [← List.take_append_drop k hs]
        rw [List.drop_eq_getElem_cons hk, List.drop_eq_getElem_cons hk1]
      have h1id : h1 = id := by
        have e : (T ++ h0 :: h1 :: R).getD (k + 1) id = h1 := by
          rw [List.getD_eq_getElem _ _ (by simp; omega)]
          rw [List.getElem_append_right (by omega)]
          simp [hT]
        rw [← e, hi']
      subst h1id
      have hA : T.length = A.length := by simp [A, hT]
      rw [runI_append _ _ _ _ hA, runI_append _ _ _ _ hA]
      rfl
    · refine ⟨A ++ id :: (fun _ => b) :: C, by simp [A, C]; omega, ?_⟩
      have hA : A.length = A.length := rfl
      rw [runI_append _ _ _ _ hA, runI_append _ _ _ _ hA]
      show runI C C (id ((fun _ => b) init)) ≠ runI C C ((fun _ => init) ((fun _ => b) init))
      simp only [id, C, runI_ids]
      exact hb

/-! ## 3. 定理 H′(予想 1): スケジュールを選べない観測でも、相手は P と同じ長さで足りる

観測は「すべてのインタリーブの最終状態の集合」。二つのプロセスが長さ `L` 以下のどの相手でも
同じ集合を出すなら、どんな長さの相手でも同じ集合を出す。

証明: 長い相手 `Q` のあるスケジュールで `P` だけが値 `v` を出すとする。分解の補題でそのスケジュールを
ブロック `B₀ … B_L` に分け、各ブロックを一つの関数にまとめた短い相手 `Q'' = (B₀, …, B_{L-1})` を作る。
`P` は `Q''` と組んで `w`(`v = B_L(w)`)を出す。もし `P'` も `Q''` と組んで `w` を出せるなら、
そのスケジュールの各関数をもとのブロックに展開し、最後に `B_L` を足せば、`P'` と `Q` のスケジュールで
`v` が出てしまう。 -/

theorem runSeq_append (a b : List (S → S)) (x : S) :
    runSeq (a ++ b) x = runSeq b (runSeq a x) := by
  simp [runSeq, List.foldl_append]

theorem runSeq_flatten (bs : List (List (S → S))) (x : S) :
    runSeq bs.flatten x = runSeq (bs.map runSeq) x := by
  induction bs generalizing x with
  | nil => rfl
  | cons b bs ih => rw [List.flatten_cons, runSeq_append, ih]; rfl

/-- 先頭に `P` 側の要素を足す。 -/
theorem inter_cons_left {α : Type} (x : α) (xs ys s : List α) (h : s ∈ inter xs ys) :
    x :: s ∈ inter (x :: xs) ys := by
  cases ys with
  | nil =>
    cases xs with
    | nil => simp [inter] at h ⊢; exact h
    | cons _ _ => simp [inter] at h ⊢; exact h
  | cons y ys => simp only [inter, List.mem_append, List.mem_map]; exact Or.inl ⟨s, h, rfl⟩

/-- 先頭に `Q` 側の要素を足す。 -/
theorem inter_cons_right {α : Type} (q : α) (xs zs t : List α) (h : t ∈ inter xs zs) :
    q :: t ∈ inter xs (q :: zs) := by
  cases xs with
  | nil => simp [inter] at h ⊢; exact h
  | cons x xs => simp only [inter, List.mem_append, List.mem_map]; exact Or.inr ⟨t, h, rfl⟩

theorem inter_prepend_right {α : Type} (b xs ys s : List α) (h : s ∈ inter xs ys) :
    b ++ s ∈ inter xs (b ++ ys) := by
  induction b with
  | nil => exact h
  | cons q b ih => exact inter_cons_right q xs (b ++ ys) (b ++ s) ih

theorem append_mem_inter {α : Type} (xs zs : List α) : xs ++ zs ∈ inter xs zs := by
  induction xs with
  | nil => simp [inter]
  | cons x xs ih => exact inter_cons_left x xs zs (xs ++ zs) ih

/-- 末尾に `Q` 側の要素をまとめて足す。 -/
theorem inter_append_right {α : Type} (xs : List α) :
    ∀ (ys zs s : List α), s ∈ inter xs ys → s ++ zs ∈ inter xs (ys ++ zs) := by
  induction xs with
  | nil => intro ys zs s h; simp [inter] at h; subst h; simp [inter]
  | cons x xs ihx =>
    intro ys
    induction ys with
    | nil => intro zs s h; simp [inter] at h; subst h; exact append_mem_inter _ _
    | cons y ys ihy =>
      intro zs s h
      simp only [inter, List.mem_append, List.mem_map] at h
      rcases h with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
      · exact inter_cons_left x xs _ _ (ihx (y :: ys) zs t ht)
      · exact inter_cons_right y (x :: xs) _ _ (ihy zs t ht)

/-- 合成した関数を、もとのブロックに展開しても、インタリーブのままで結果は変わらない。 -/
theorem expand (fs : List (S → S)) :
    ∀ (bs : List (List (S → S))) (seq : List (S → S)), seq ∈ inter fs (bs.map runSeq) →
      ∃ seq₂ ∈ inter fs bs.flatten, ∀ x, runSeq seq₂ x = runSeq seq x := by
  induction fs with
  | nil =>
    intro bs seq h
    simp [inter] at h; subst h
    exact ⟨bs.flatten, by simp [inter], fun x => runSeq_flatten bs x⟩
  | cons f fs ihf =>
    intro bs
    induction bs with
    | nil =>
      intro seq h
      simp [inter] at h; subst h
      exact ⟨f :: fs, by simp [inter], fun x => rfl⟩
    | cons b bs ihb =>
      intro seq h
      simp only [List.map_cons, inter, List.mem_append, List.mem_map] at h
      rcases h with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
      · obtain ⟨t₂, ht₂, hr⟩ := ihf (b :: bs) t (by simpa using ht)
        refine ⟨f :: t₂, inter_cons_left f fs _ t₂ (by simpa using ht₂), fun x => ?_⟩
        rw [runSeq_cons, runSeq_cons, hr]
      · obtain ⟨t₂, ht₂, hr⟩ := ihb t ht
        refine ⟨b ++ t₂, ?_, fun x => ?_⟩
        · rw [List.flatten_cons]; exact inter_prepend_right b _ _ t₂ ht₂
        · rw [runSeq_append, hr, runSeq_cons]

/-- スケジュールを選べない観測: すべてのインタリーブの最終状態の集合。 -/
def obs (init : S) (P Q : List (S → S)) : Set S := {v | ∃ seq ∈ inter P Q, runSeq seq init = v}

theorem runSeq_singleton (g : S → S) : runSeq [g] = g := by funext x; rfl

theorem obs_sub (init : S) (P P' : List (S → S))
    (h : ∀ Q : List (S → S), Q.length ≤ P.length → obs init P Q ⊆ obs init P' Q)
    (Q : List (S → S)) : obs init P Q ⊆ obs init P' Q := by
  rintro v ⟨seq, hseq, rfl⟩
  obtain ⟨B, hB1, hB2, hB3⟩ := inter_blocks P Q seq hseq
  have hne : B ≠ [] := by intro h; rw [h] at hB2; simp at hB2
  set Bd := B.dropLast with hBd
  set bl := B.getLast hne with hbl
  have hsplit : B = Bd ++ [bl] := (List.dropLast_append_getLast hne).symm
  set Q'' := Bd.map runSeq with hQ''
  have hQlen : Q''.length = P.length := by
    simp [hQ'', hBd, List.length_dropLast, hB2]
  -- P は Q'' と組んで w を出す
  set w := runI P Q'' init with hw
  have hv : runSeq seq init = runSeq bl w := by
    rw [hB3 init, runB_eq_runI P B hB2 init]
  have hwP : w ∈ obs init P Q'' := by
    set B'' := Q''.map (fun g => [g]) ++ [[]] with hB''
    have hB''len : B''.length = P.length + 1 := by simp [hB'', hQlen]
    obtain ⟨s, hs, hr⟩ := blocks_realizable P B'' hB''len
    have hsing : ∀ l : List (S → S), (l.map (fun g => [g])).flatten = l := by
      intro l; induction l with
      | nil => rfl
      | cons g l ih => simp [ih]
    have hflat : B''.flatten = Q'' := by simp [hB'', hsing]
    refine ⟨s, by rw [← hflat]; exact hs, ?_⟩
    rw [hr, runB_eq_runI P B'' hB''len]
    have hd : B''.dropLast = Q''.map (fun g => [g]) := by simp [hB'']
    have hl : B''.getLast (by intro h; rw [h] at hB''len; simp at hB''len) = [] := by simp [hB'']
    rw [hl, runSeq_nil, hd]
    simp [Function.comp_def, runSeq_singleton, hw]
  -- P' も w を出すなら、展開して最後に bl を足すと v が出る
  obtain ⟨s', hs', hr'⟩ := h Q'' (le_of_eq hQlen) hwP
  obtain ⟨s₂, hs₂, hr₂⟩ := expand P' Bd s' (by rw [← hQ'']; exact hs')
  refine ⟨s₂ ++ bl, ?_, ?_⟩
  · have := inter_append_right P' Bd.flatten bl s₂ hs₂
    rwa [← List.flatten_concat, ← hsplit, hB1] at this
  · rw [runSeq_append, hr₂, hr', hv]

/-- **定理 H′(予想 1).** 同じ長さの二つのプロセスが、長さ `L` 以下のどの相手に対しても
同じ観測(最終状態の集合)を出すなら、どんな相手に対しても同じ観測を出す。 -/
theorem thmH' (init : S) (P P' : List (S → S)) (hlen : P'.length = P.length)
    (h : ∀ Q : List (S → S), Q.length ≤ P.length → obs init P Q = obs init P' Q)
    (Q : List (S → S)) : obs init P Q = obs init P' Q := by
  apply Set.Subset.antisymm
  · exact obs_sub init P P' (fun Q hQ => (h Q hQ).le) Q
  · exact obs_sub init P' P (fun Q hQ => (h Q (hlen ▸ hQ)).ge) Q

/-! ## 4. 定理 I: 何もしない CS は見えない(stuttering)

観測は、ブロックの組 `B` ごとの `runB` の値の集合として書ける。何もしない CS(恒等写像)を
一つ挟んでも、その前後のブロックをつなげれば同じ実行になり、逆に空のブロックを足せば元に戻る。
したがって、恒等写像の CS を足しても消しても、どの相手に対する観測も変わらない。 -/

theorem obs_iff_blocks (init : S) (P Q : List (S → S)) (v : S) :
    v ∈ obs init P Q ↔ ∃ B : List (List (S → S)),
      B.flatten = Q ∧ B.length = P.length + 1 ∧ runB P B init = v := by
  constructor
  · rintro ⟨seq, hseq, rfl⟩
    obtain ⟨B, h1, h2, h3⟩ := inter_blocks P Q seq hseq
    exact ⟨B, h1, h2, (h3 init).symm⟩
  · rintro ⟨B, h1, h2, rfl⟩
    obtain ⟨seq, hs, hr⟩ := blocks_realizable P B h2
    exact ⟨seq, h1 ▸ hs, hr init⟩

/-- 恒等写像の CS を挟んだ実行は、前後のブロックをつないだ実行に等しい。 -/
theorem runB_id (A Bs : List (S → S)) :
    ∀ (C : List (List (S → S))) (b₁ b₂ : List (S → S)) (D : List (List (S → S))) (x : S),
      C.length = A.length → D.length = Bs.length →
      runB (A ++ id :: Bs) (C ++ b₁ :: b₂ :: D) x = runB (A ++ Bs) (C ++ (b₁ ++ b₂) :: D) x := by
  induction A with
  | nil =>
    intro C b₁ b₂ D x hC hD
    cases C with
    | nil =>
      simp only [List.nil_append]
      show runB Bs (b₂ :: D) (id (runSeq b₁ x)) = runB Bs ((b₁ ++ b₂) :: D) x
      cases Bs with
      | nil =>
        cases D with
        | nil => show runSeq b₂ (runSeq b₁ x) = runSeq (b₁ ++ b₂) x; rw [runSeq_append]
        | cons _ _ => simp at hD
      | cons f Bs =>
        cases D with
        | nil => simp at hD
        | cons d D =>
          show runB Bs (d :: D) (f (runSeq b₂ (id (runSeq b₁ x)))) =
            runB Bs (d :: D) (f (runSeq (b₁ ++ b₂) x))
          rw [runSeq_append]; rfl
    | cons _ _ => simp at hC
  | cons a A ih =>
    intro C b₁ b₂ D x hC hD
    cases C with
    | nil => simp at hC
    | cons c C =>
      simp only [List.cons_append]
      show runB (A ++ id :: Bs) (C ++ b₁ :: b₂ :: D) (a (runSeq c x)) =
        runB (A ++ Bs) (C ++ (b₁ ++ b₂) :: D) (a (runSeq c x))
      exact ih C b₁ b₂ D _ (by simpa using hC) hD

/-- **定理 I(stuttering).** 恒等写像の CS を一つ挟んでも、どの相手に対する観測も変わらない。 -/
theorem thmI (init : S) (A Bs Q : List (S → S)) :
    obs init (A ++ id :: Bs) Q = obs init (A ++ Bs) Q := by
  ext v
  rw [obs_iff_blocks, obs_iff_blocks]
  constructor
  · rintro ⟨B, h1, h2, rfl⟩
    -- B を A の長さで切り、恒等写像の前後のブロックをつなぐ
    have hdl : (B.drop A.length).length = Bs.length + 2 := by simp at h2 ⊢; omega
    obtain ⟨b₁, b₂, D, hdeq⟩ : ∃ b₁ b₂ D, B.drop A.length = b₁ :: b₂ :: D := by
      rcases hx : B.drop A.length with _ | ⟨b₁, _ | ⟨b₂, D⟩⟩
      · rw [hx] at hdl; simp at hdl
      · rw [hx] at hdl; simp at hdl
      · exact ⟨b₁, b₂, D, rfl⟩
    have hD : D.length = Bs.length := by rw [hdeq] at hdl; simp at hdl; omega
    have hB : B = B.take A.length ++ b₁ :: b₂ :: D := by
      rw [← hdeq, List.take_append_drop]
    have hC : (B.take A.length).length = A.length := by simp at h2 ⊢; omega
    refine ⟨B.take A.length ++ (b₁ ++ b₂) :: D, ?_, ?_, ?_⟩
    · rw [← h1]; conv_rhs => rw [hB]
      simp
    · simp [hC, hD]; omega
    · rw [← runB_id A Bs _ b₁ b₂ D init hC hD, ← hB]
  · rintro ⟨B, h1, h2, rfl⟩
    have hdl : (B.drop A.length).length = Bs.length + 1 := by simp at h2 ⊢; omega
    obtain ⟨b, D, hdeq⟩ : ∃ b D, B.drop A.length = b :: D := by
      rcases hx : B.drop A.length with _ | ⟨b, D⟩
      · rw [hx] at hdl; simp at hdl
      · exact ⟨b, D, rfl⟩
    have hD : D.length = Bs.length := by rw [hdeq] at hdl; simp at hdl; omega
    have hB : B = B.take A.length ++ b :: D := by
      rw [← hdeq, List.take_append_drop]
    have hC : (B.take A.length).length = A.length := by simp at h2 ⊢; omega
    refine ⟨B.take A.length ++ b :: [] :: D, ?_, ?_, ?_⟩
    · rw [← h1]; conv_rhs => rw [hB]
      simp
    · simp [hC, hD]; omega
    · rw [runB_id A Bs _ b [] D init hC hD, List.append_nil, ← hB]

/-! ## 5. 予想 2′ の一部: 何かをする CS が高々一つなら、区別できる

恒等写像を消した形が `[g]` と `[h]`(`g ≠ h`)、または `[g]` と `[]`(`g ≠ id`)なら、
定数を書く一つの CS だけの相手で区別できる(状態の数によらない)。 -/

theorem obs_single_const (init z : S) (g : S → S) :
    obs init [g] [fun _ => z] = {g z, z} := by
  ext v
  constructor
  · rintro ⟨seq, hseq, hv⟩
    simp only [inter, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hseq
    rcases hseq with rfl | rfl
    · simp only [runSeq, List.foldl] at hv; simp [← hv]
    · simp only [runSeq, List.foldl] at hv; simp [← hv]
  · intro hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with hv | hv
    · exact ⟨[fun _ => z, g], by simp [inter], by simp [runSeq, hv]⟩
    · exact ⟨[g, fun _ => z], by simp [inter], by simp [runSeq, hv]⟩

theorem obs_nil_const (init z : S) : obs init [] [fun _ => z] = {z} := by
  ext v; simp [obs, inter, runSeq]

/-- 二つの異なる関数 `g`, `h` は、一つの CS の相手で区別できる。 -/
theorem sep_single (init : S) (g h : S → S) (hgh : g ≠ h) :
    ∃ Q : List (S → S), obs init [g] Q ≠ obs init [h] Q := by
  obtain ⟨z, hz⟩ : ∃ z, g z ≠ h z := by
    by_contra hc; push Not at hc; exact hgh (funext hc)
  refine ⟨[fun _ => z], ?_⟩
  rw [obs_single_const, obs_single_const]
  intro he
  have : g z ∈ ({h z, z} : Set S) := he ▸ (by simp)
  have : h z ∈ ({g z, z} : Set S) := he.symm ▸ (by simp)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at *
  rcases ‹g z = h z ∨ g z = z› with h1 | h1
  · exact hz h1
  rcases ‹h z = g z ∨ h z = z› with h2 | h2
  · exact hz h2.symm
  · exact hz (h1.trans h2.symm)

/-- 恒等写像でない関数 `g` の CS は、一つの CS の相手で、何もしないプロセスと区別できる。 -/
theorem sep_single_nil (init : S) (g : S → S) (hg : g ≠ id) :
    ∃ Q : List (S → S), obs init [g] Q ≠ obs init [] Q := by
  obtain ⟨z, hz⟩ : ∃ z, g z ≠ z := by
    by_contra hc; push Not at hc; exact hg (funext hc)
  refine ⟨[fun _ => z], ?_⟩
  rw [obs_single_const, obs_nil_const]
  intro he
  have : g z ∈ ({z} : Set S) := he ▸ (by simp)
  exact hz (by simpa using this)

end ImagExec.R2H

#print axioms ImagExec.R2H.inter_blocks
#print axioms ImagExec.R2H.blocks_realizable
#print axioms ImagExec.R2H.thmH
#print axioms ImagExec.R2H.thmH3
#print axioms ImagExec.R2H.thmH'
#print axioms ImagExec.R2H.thmI
#print axioms ImagExec.R2H.sep_single
#print axioms ImagExec.R2H.sep_single_nil
