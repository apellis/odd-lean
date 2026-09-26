import OddMath.Frontier.EKClassicalPlactic

/-!
# Growth of row insertion and the symmetry of the insertion shapes

List-level row insertion (`EKClassicalPlactic.ins`, Fulton, *Young Tableaux*, §1.1).
For an ℕ-matrix `A` (labels `p ≥ 1`, letters `q ≥ 1`) let `G A i j` be the shape of the
insertion tableau of the two-line array of the submatrix with labels `≤ i` and letters `≤ j`.
We prove Fomin's local rule for `G` (`local_G`) and deduce `G Aᵀ j i = G A i j`
(`G_transpose`). This is the combinatorial core of the RSK symmetry theorem
(Fulton, §4.1, Symmetry Theorem), used for the Littlewood–Richardson rule of
Ellis, arXiv:1111.3932v1, Theorem 4.8, whose proof cites Fulton §5.2.

Rows are compared up to trailing empty rows (`Eqv`); shapes are functions `ℕ → ℕ`.
-/

namespace OddMath.Frontier.OddLRRule

open EKClassicalPlactic

/-! ## Rows up to trailing empty rows -/

/-- The `k`-th row, empty beyond the last row. -/
def rowAt (rs : List (List ℕ)) (k : ℕ) : List ℕ := rs.getD k []

/-- Equality of all rows (trailing empty rows are ignored). -/
def Eqv (rs rs' : List (List ℕ)) : Prop := ∀ k, rowAt rs k = rowAt rs' k

/-- Restriction to letters `≤ j`. -/
def res (j : ℕ) (rs : List (List ℕ)) : List (List ℕ) := rs.map (List.filter (fun x => decide (x ≤ j)))

/-- Row lengths. -/
def sh (rs : List (List ℕ)) (k : ℕ) : ℕ := (rowAt rs k).length

@[simp] theorem rowAt_nil (k : ℕ) : rowAt [] k = [] := by simp [rowAt]
@[simp] theorem rowAt_cons_zero (R : List ℕ) (rs : List (List ℕ)) : rowAt (R :: rs) 0 = R := by
  simp [rowAt]
@[simp] theorem rowAt_cons_succ (R : List ℕ) (rs : List (List ℕ)) (k : ℕ) :
    rowAt (R :: rs) (k + 1) = rowAt rs k := by simp [rowAt]

theorem rowAt_res (j : ℕ) (rs : List (List ℕ)) (k : ℕ) :
    rowAt (res j rs) k = (rowAt rs k).filter (fun x => decide (x ≤ j)) := by
  induction rs generalizing k with
  | nil => simp [res]
  | cons R rs ih =>
    cases k with
    | zero => simp [res]
    | succ k => simpa [res] using ih k

theorem Eqv.refl (rs : List (List ℕ)) : Eqv rs rs := fun _ => rfl
theorem Eqv.symm {rs rs' : List (List ℕ)} (h : Eqv rs rs') : Eqv rs' rs := fun k => (h k).symm
theorem Eqv.trans {a b c : List (List ℕ)} (h : Eqv a b) (h' : Eqv b c) : Eqv a c :=
  fun k => (h k).trans (h' k)

theorem eqv_cons_iff {R R' : List ℕ} {rs rs' : List (List ℕ)} :
    Eqv (R :: rs) (R' :: rs') ↔ R = R' ∧ Eqv rs rs' := by
  constructor
  · intro h
    exact ⟨by simpa using h 0, fun k => by simpa using h (k + 1)⟩
  · rintro ⟨rfl, h⟩ k
    cases k with
    | zero => rfl
    | succ k => simpa using h k

theorem eqv_nil_cons_iff {R : List ℕ} {rs : List (List ℕ)} :
    Eqv [] (R :: rs) ↔ R = [] ∧ Eqv [] rs := by
  constructor
  · intro h
    exact ⟨by simpa using (h 0).symm, fun k => by simpa using h (k + 1)⟩
  · rintro ⟨rfl, h⟩ k
    cases k with
    | zero => rfl
    | succ k => simpa using h k

theorem sh_eqv {rs rs' : List (List ℕ)} (h : Eqv rs rs') (k : ℕ) : sh rs k = sh rs' k := by
  simp only [sh, h k]

theorem res_eqv {rs rs' : List (List ℕ)} (h : Eqv rs rs') (j : ℕ) : Eqv (res j rs) (res j rs') := by
  intro k; rw [rowAt_res, rowAt_res, h k]

theorem res_nil (j : ℕ) : res j [] = [] := rfl

/-! ## Insertion respects `Eqv` -/

theorem ins_nil (a : ℕ) : ins [] a = [[a]] := rfl

theorem ins_cons_none {R : List ℕ} {rs : List (List ℕ)} {a : ℕ} {R' : List ℕ}
    (h : bump1 R a = (R', none)) : ins (R :: rs) a = R' :: rs := by
  simp [ins, h]

theorem ins_cons_some {R : List ℕ} {rs : List (List ℕ)} {a b : ℕ} {R' : List ℕ}
    (h : bump1 R a = (R', some b)) : ins (R :: rs) a = R' :: ins rs b := by
  simp [ins, h]

theorem ins_eqv {rs rs' : List (List ℕ)} (h : Eqv rs rs') (a : ℕ) :
    Eqv (ins rs a) (ins rs' a) := by
  induction rs generalizing rs' a with
  | nil =>
    induction rs' with
    | nil => exact Eqv.refl _
    | cons R' rs' _ =>
      obtain ⟨rfl, h'⟩ := eqv_nil_cons_iff.mp h
      rw [ins_nil, ins_cons_none (bump1_nil a)]
      exact eqv_cons_iff.mpr ⟨rfl, h'⟩
  | cons R rs ih =>
    cases rs' with
    | nil =>
      obtain ⟨rfl, h'⟩ := eqv_nil_cons_iff.mp h.symm
      rw [ins_nil, ins_cons_none (bump1_nil a)]
      exact eqv_cons_iff.mpr ⟨rfl, h'.symm⟩
    | cons R' rs' =>
      obtain ⟨rfl, h'⟩ := eqv_cons_iff.mp h
      rcases hb : bump1 R a with ⟨R₁, _ | b⟩
      · rw [ins_cons_none hb, ins_cons_none hb]
        exact eqv_cons_iff.mpr ⟨rfl, h'⟩
      · rw [ins_cons_some hb, ins_cons_some hb]
        exact eqv_cons_iff.mpr ⟨rfl, ih h' b⟩

theorem insW_eqv {rs rs' : List (List ℕ)} (h : Eqv rs rs') (w : List ℕ) :
    Eqv (insW rs w) (insW rs' w) := by
  induction w generalizing rs rs' with
  | nil => exact h
  | cons a w ih => exact ih (ins_eqv h a)

theorem insW_cons (rs : List (List ℕ)) (a : ℕ) (w : List ℕ) :
    insW rs (a :: w) = insW (ins rs a) w := rfl

/-! ## Restriction to an initial interval of letters -/

theorem filter_le_of_gt {j : ℕ} (l : List ℕ) (h : ∀ x ∈ l, j < x) :
    l.filter (fun x => decide (x ≤ j)) = [] := by
  rw [List.filter_eq_nil_iff]
  intro x hx
  have := h x hx
  simp only [decide_eq_true_eq]
  omega

theorem filter_le_of_le {j : ℕ} (l : List ℕ) (h : ∀ x ∈ l, x ≤ j) :
    l.filter (fun x => decide (x ≤ j)) = l := by
  rw [List.filter_eq_self]
  intro x hx
  simpa using h x hx

theorem res_ins_gt (j : ℕ) : ∀ (rs : List (List ℕ)) (a : ℕ), j < a →
    Eqv (res j (ins rs a)) (res j rs)
  | [], a, ha => by
    intro k
    cases k with
    | zero => simp [ins_nil, res, rowAt, ha]
    | succ k => simp [ins_nil, res, rowAt]
  | R :: rs, a, ha => by
    rcases bump1_spec R a with ⟨_, he⟩ | ⟨u, b, v, hR, _, hab, he⟩
    · rw [ins_cons_none he]
      refine eqv_cons_iff.mpr ⟨?_, Eqv.refl _⟩
      simp [List.filter_append, ha]
    · rw [ins_cons_some he]
      refine eqv_cons_iff.mpr ⟨?_, res_ins_gt j rs b (by omega)⟩
      subst hR
      simp [List.filter_append, List.filter_cons, show ¬ a ≤ j by omega, show ¬ b ≤ j by omega]

theorem res_ins_le (j : ℕ) : ∀ (rs : List (List ℕ)) (a : ℕ), RowsSorted rs → a ≤ j →
    Eqv (res j (ins rs a)) (ins (res j rs) a)
  | [], a, _, ha => by
    rw [ins_nil, res_nil, ins_nil]
    simp [res, ha]
    exact Eqv.refl _
  | R :: rs, a, hs, ha => by
    have hR : R.Sorted (· ≤ ·) := hs R List.mem_cons_self
    have hrs : RowsSorted rs := fun S hS => hs S (List.mem_cons_of_mem _ hS)
    have hres : res j (R :: rs) = R.filter (fun x => decide (x ≤ j)) :: res j rs := rfl
    rcases bump1_spec R a with ⟨hall, he⟩ | ⟨u, b, v, hR', hu, hab, he⟩
    · rw [ins_cons_none he, hres]
      have hall' : ∀ p ∈ R.filter (fun x => decide (x ≤ j)), p ≤ a :=
        fun p hp => hall p (List.mem_filter.mp hp).1
      rw [ins_cons_none (bump1_le_all _ hall')]
      refine eqv_cons_iff.mpr ⟨?_, Eqv.refl _⟩
      simp [List.filter_append, ha]
    · rw [ins_cons_some he, hres]
      have huj : ∀ p ∈ u, p ≤ j := fun p hp => by have := hu p hp; omega
      subst hR'
      by_cases hbj : b ≤ j
      · have hf : (u ++ b :: v).filter (fun x => decide (x ≤ j)) =
            u ++ b :: v.filter (fun x => decide (x ≤ j)) := by
          simp [List.filter_append, filter_le_of_le u huj, hbj]
        rw [hf, ins_cons_some (by rw [bump1_append_le u _ hu, bump1_cons_lt _ hab])]
        refine eqv_cons_iff.mpr ⟨?_, res_ins_le j rs b hrs hbj⟩
        simp [List.filter_append, filter_le_of_le u huj, ha]
      · have hv : ∀ x ∈ v, j < x := by
          intro x hx
          have := List.pairwise_append.mp hR
          have h2 := (List.sorted_cons.mp this.2.1).1 x hx
          omega
        have hf : (u ++ b :: v).filter (fun x => decide (x ≤ j)) = u := by
          simp [List.filter_append, filter_le_of_le u huj, hbj, filter_le_of_gt v hv]
        rw [hf, ins_cons_none (bump1_le_all u hu)]
        refine eqv_cons_iff.mpr ⟨?_, res_ins_gt j rs b (by omega)⟩
        simp [List.filter_append, filter_le_of_le u huj, ha, filter_le_of_gt v hv]

theorem res_sorted (j : ℕ) {rs : List (List ℕ)} (h : RowsSorted rs) : RowsSorted (res j rs) := by
  intro R hR
  obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hR
  exact (h S hS).filter _

theorem res_insW (j : ℕ) (w : List ℕ) : ∀ rs : List (List ℕ), RowsSorted rs →
    Eqv (res j (insW rs w)) (insW (res j rs) (w.filter (fun x => decide (x ≤ j)))) := by
  induction w with
  | nil => intro rs _; exact Eqv.refl _
  | cons a w ih =>
    intro rs hs
    rw [insW_cons]
    refine (ih _ (ins_sorted rs hs a)).trans ?_
    by_cases ha : a ≤ j
    · rw [List.filter_cons_of_pos (by simpa using ha), insW_cons]
      exact insW_eqv (res_ins_le j rs a hs ha) _
    · rw [List.filter_cons_of_neg (by simpa using ha)]
      exact insW_eqv (res_ins_gt j rs a (by omega)) _

theorem res_P (j : ℕ) (w : List ℕ) :
    Eqv (res j (P w)) (P (w.filter (fun x => decide (x ≤ j)))) :=
  res_insW j w [] (by simp [RowsSorted])

/-! ## The row in which an insertion ends -/

/-- Index of the row that grows when `a` is inserted. -/
def newRow : List (List ℕ) → ℕ → ℕ
  | [], _ => 0
  | R :: rs, a => match (bump1 R a).2 with
    | none => 0
    | some b => newRow rs b + 1

theorem newRow_cons_none {R : List ℕ} {rs : List (List ℕ)} {a : ℕ} {R' : List ℕ}
    (h : bump1 R a = (R', none)) : newRow (R :: rs) a = 0 := by
  simp [newRow, h]

theorem newRow_cons_some {R : List ℕ} {rs : List (List ℕ)} {a b : ℕ} {R' : List ℕ}
    (h : bump1 R a = (R', some b)) : newRow (R :: rs) a = newRow rs b + 1 := by
  simp [newRow, h]

theorem sh_ins : ∀ (rs : List (List ℕ)) (a k : ℕ),
    sh (ins rs a) k = sh rs k + if k = newRow rs a then 1 else 0
  | [], a, k => by cases k <;> simp [sh, ins_nil, newRow]
  | R :: rs, a, k => by
    rcases bump1_spec R a with ⟨_, he⟩ | ⟨u, b, v, hR, _, _, he⟩
    · rw [ins_cons_none he, newRow_cons_none he]
      cases k <;> simp [sh]
    · rw [ins_cons_some he, newRow_cons_some he]
      cases k with
      | zero => subst hR; simp [sh]
      | succ k =>
        have := sh_ins rs b k
        simp only [sh, rowAt_cons_succ] at this ⊢
        rw [this]
        simp

theorem newRow_eqv {rs rs' : List (List ℕ)} (h : Eqv rs rs') (a : ℕ) :
    newRow rs a = newRow rs' a := by
  induction rs generalizing rs' a with
  | nil =>
    induction rs' with
    | nil => rfl
    | cons R' rs' _ =>
      obtain ⟨rfl, -⟩ := eqv_nil_cons_iff.mp h
      rw [newRow_cons_none (bump1_nil a)]; rfl
  | cons R rs ih =>
    cases rs' with
    | nil =>
      obtain ⟨rfl, -⟩ := eqv_nil_cons_iff.mp h.symm
      rw [newRow_cons_none (bump1_nil a)]; rfl
    | cons R' rs' =>
      obtain ⟨rfl, h'⟩ := eqv_cons_iff.mp h
      rcases hb : bump1 R a with ⟨R₁, _ | b⟩
      · rw [newRow_cons_none hb, newRow_cons_none hb]
      · rw [newRow_cons_some hb, newRow_cons_some hb, ih h' b]

/-- Row Bumping Lemma (Fulton §1.1): a weakly larger second letter ends weakly higher. -/
theorem newRow_ins_le : ∀ (rs : List (List ℕ)) (a b : ℕ), RowsSorted rs → a ≤ b →
    newRow (ins rs a) b ≤ newRow rs a
  | [], a, b, _, hab => by
    rw [ins_nil, newRow_cons_none (bump1_le_all [a] (by simpa using hab))]
    simp
  | R :: rs, a, b, hs, hab => by
    have hR : R.Sorted (· ≤ ·) := hs R List.mem_cons_self
    have hrs : RowsSorted rs := fun S hS => hs S (List.mem_cons_of_mem _ hS)
    rcases bump1_spec R a with ⟨hall, he⟩ | ⟨u, c, v, hR', hu, hac, he⟩
    · rw [ins_cons_none he, newRow_cons_none he]
      have : ∀ p ∈ R ++ [a], p ≤ b := by
        intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · have := hall p hp; omega
        · rw [List.mem_singleton.mp hp]; exact hab
      rw [newRow_cons_none (bump1_le_all _ this)]
    · rw [ins_cons_some he, newRow_cons_some he]
      have hub : ∀ p ∈ u ++ [a], p ≤ b := by
        intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · have := hu p hp; omega
        · rw [List.mem_singleton.mp hp]; exact hab
      have hsplit : u ++ a :: v = (u ++ [a]) ++ v := by simp
      rcases hbv : bump1 v b with ⟨v', _ | d⟩
      · rw [newRow_cons_none (show bump1 (u ++ a :: v) b = ((u ++ [a]) ++ v', none) by
          rw [hsplit, bump1_append_le _ _ hub, hbv])]
        omega
      · rw [newRow_cons_some (show bump1 (u ++ a :: v) b = ((u ++ [a]) ++ v', some d) by
          rw [hsplit, bump1_append_le _ _ hub, hbv])]
        have hcd : c ≤ d := by
          subst hR'
          have hv : ∀ x ∈ v, c ≤ x := by
            have := List.pairwise_append.mp hR
            exact (List.sorted_cons.mp this.2.1).1
          rcases bump1_spec v b with ⟨_, he'⟩ | ⟨u', d', v'', hv', _, _, he'⟩
          · rw [hbv] at he'; simp at he'
          · rw [hbv] at he'
            simp only [Prod.mk.injEq, Option.some.injEq] at he'
            rw [he'.2]
            exact hv d' (by rw [hv']; simp)
        have := newRow_ins_le rs c d hrs hcd
        omega

/-! ## Letters bounded by `J + 1`, and the count of the letter `J + 1` -/

/-- All entries are `≤ N`. -/
def Bnd (N : ℕ) (rs : List (List ℕ)) : Prop := ∀ R ∈ rs, ∀ y ∈ R, y ≤ N

theorem bnd_ins {N : ℕ} : ∀ (rs : List (List ℕ)) (a : ℕ), Bnd N rs → a ≤ N → Bnd N (ins rs a)
  | [], a, _, ha => by
    intro R hR y hy
    simp [ins_nil] at hR; subst hR; simp at hy; omega
  | R :: rs, a, hb, ha => by
    have hR : ∀ y ∈ R, y ≤ N := hb R List.mem_cons_self
    have hrs : Bnd N rs := fun S hS => hb S (List.mem_cons_of_mem _ hS)
    rcases bump1_spec R a with ⟨_, he⟩ | ⟨u, c, v, hR', _, _, he⟩
    · rw [ins_cons_none he]
      intro S hS y hy
      rcases List.mem_cons.mp hS with rfl | hS
      · rcases List.mem_append.mp hy with hy | hy
        · exact hR y hy
        · rw [List.mem_singleton.mp hy]; exact ha
      · exact hrs S hS y hy
    · rw [ins_cons_some he]
      subst hR'
      intro S hS y hy
      rcases List.mem_cons.mp hS with rfl | hS
      · simp only [List.mem_append, List.mem_cons] at hy
        rcases hy with hy | rfl | hy
        · exact hR y (by simp [hy])
        · exact ha
        · exact hR y (by simp [hy])
      · exact bnd_ins rs c hrs (hR c (by simp)) S hS y hy

theorem bnd_insW {N : ℕ} (w : List ℕ) (hw : ∀ a ∈ w, a ≤ N) :
    ∀ rs : List (List ℕ), Bnd N rs → Bnd N (insW rs w) := by
  induction w with
  | nil => intro rs h; exact h
  | cons a w ih =>
    intro rs h
    exact ih (fun b hb => hw b (List.mem_cons_of_mem _ hb)) _
      (bnd_ins rs a h (hw a List.mem_cons_self))

theorem bnd_rowAt {N : ℕ} {rs : List (List ℕ)} (h : Bnd N rs) (k : ℕ) :
    ∀ y ∈ rowAt rs k, y ≤ N := by
  induction rs generalizing k with
  | nil => simp
  | cons R rs ih =>
    cases k with
    | zero => exact h R List.mem_cons_self
    | succ k => exact ih (fun S hS => h S (List.mem_cons_of_mem _ hS)) k

/-- Multiplicity of the top letter `J + 1` in row `k`. -/
def cnt (J : ℕ) (rs : List (List ℕ)) (k : ℕ) : ℕ := (rowAt rs k).count (J + 1)

theorem count_top_zero {J : ℕ} (L : List ℕ) (h : ∀ y ∈ L, y ≤ J) : L.count (J + 1) = 0 :=
  List.count_eq_zero_of_not_mem (fun hm => by have := h _ hm; omega)

theorem length_split (J : ℕ) (L : List ℕ) (h : ∀ y ∈ L, y ≤ J + 1) :
    L.length = (L.filter (fun x => decide (x ≤ J))).length + L.count (J + 1) := by
  induction L with
  | nil => rfl
  | cons y L ih =>
    have hy := h y List.mem_cons_self
    have := ih (fun z hz => h z (List.mem_cons_of_mem _ hz))
    by_cases hyJ : y ≤ J
    · rw [List.filter_cons_of_pos (by simpa using hyJ), List.count_cons_of_ne (by omega)]
      simp only [List.length_cons]; omega
    · have : y = J + 1 := by omega
      subst this
      rw [List.filter_cons_of_neg (by simp), List.count_cons_self]
      simp only [List.length_cons]; omega

theorem sh_split (J : ℕ) {rs : List (List ℕ)} (h : Bnd (J + 1) rs) (k : ℕ) :
    sh rs k = sh (res J rs) k + cnt J rs k := by
  simp only [sh, cnt, rowAt_res]
  exact length_split J _ (bnd_rowAt h k)

/-- A weakly increasing row with entries `≤ J + 1` is its `≤ J` part followed by `J + 1`s. -/
theorem row_split (J : ℕ) (R : List ℕ) (hR : R.Sorted (· ≤ ·)) (h : ∀ y ∈ R, y ≤ J + 1) :
    R = R.filter (fun x => decide (x ≤ J)) ++ List.replicate (R.count (J + 1)) (J + 1) := by
  obtain ⟨L, G, rfl, hL, hG, _, _⟩ := sorted_split R hR J
  have hG' : G = List.replicate G.length (J + 1) := by
    rw [List.eq_replicate_iff]
    refine ⟨rfl, fun b hb => ?_⟩
    have := hG b hb; have := h b (by simp [hb]); omega
  rw [List.filter_append, filter_le_of_le L hL, filter_le_of_gt G hG, List.count_append,
    count_top_zero L hL, List.append_nil, zero_add]
  conv_lhs => rw [hG']
  congr 2
  rw [hG', List.count_replicate_self, List.length_replicate]

/-- Inserting the top letter appends it to the first row. -/
theorem cnt_ins_top (J : ℕ) (rs : List (List ℕ)) (h : Bnd (J + 1) rs) (k : ℕ) :
    cnt J (ins rs (J + 1)) k = cnt J rs k + if k = 0 then 1 else 0 := by
  cases rs with
  | nil => cases k <;> simp [cnt, ins_nil]
  | cons R rs =>
    rw [ins_cons_none (bump1_le_all R (h R List.mem_cons_self))]
    cases k <;> simp [cnt, List.count_append]

/-- The top-letter bookkeeping of one insertion of a letter `x ≤ J` (Fomin's local rule). -/
theorem cnt_ins (J : ℕ) : ∀ (rs : List (List ℕ)) (x : ℕ), RowsSorted rs → Bnd (J + 1) rs →
    x ≤ J → ∀ k, cnt J (ins rs x) k +
      (if k = newRow (res J rs) x ∧ 0 < cnt J rs k then 1 else 0) =
      cnt J rs k +
      (if k = newRow (res J rs) x + 1 ∧ 0 < cnt J rs (newRow (res J rs) x) then 1 else 0)
  | [], x, _, _, hx, k => by
    cases k <;> simp [cnt, ins_nil, newRow, res_nil, List.count_singleton', show x ≠ J + 1 by omega]
  | R :: rs, x, hs, hb, hx, k => by
    have hR : R.Sorted (· ≤ ·) := hs R List.mem_cons_self
    have hRb : ∀ y ∈ R, y ≤ J + 1 := hb R List.mem_cons_self
    have hrs : RowsSorted rs := fun S hS => hs S (List.mem_cons_of_mem _ hS)
    have hrb : Bnd (J + 1) rs := fun S hS => hb S (List.mem_cons_of_mem _ hS)
    set R' := R.filter (fun x => decide (x ≤ J)) with hR'def
    set c := R.count (J + 1) with hc
    have hsplit := row_split J R hR hRb
    rw [← hR'def, ← hc] at hsplit
    have hR'J : ∀ y ∈ R', y ≤ J := fun y hy => by simpa using (List.mem_filter.mp hy).2
    have hres : res J (R :: rs) = R' :: res J rs := rfl
    have hnot : J + 1 ∉ R' := fun hm => by have := hR'J _ hm; omega
    rw [hres]
    rcases bump1_spec R' x with ⟨hall, he⟩ | ⟨u, b, v, hR'', hu, hxb, he⟩
    · rw [newRow_cons_none he]
      rcases hcz : c with _ | c'
      · rw [hcz] at hsplit
        rw [hsplit, List.replicate_zero, List.append_nil,
          ins_cons_none (bump1_le_all R' hall)]
        cases k with
        | zero =>
          simp [cnt, List.count_append, count_top_zero R' hR'J, show x ≠ J + 1 by omega]
        | succ k => simp [cnt, hsplit, hnot]
      · rw [hcz] at hsplit
        have hbump : bump1 R x = (R' ++ x :: List.replicate c' (J + 1), some (J + 1)) := by
          rw [hsplit, bump1_append_le _ _ hall, List.replicate_succ, bump1_cons_lt _ (by omega)]
        rw [ins_cons_some hbump]
        have hcR : cnt J (R :: rs) 0 = c' + 1 := by
          simp [cnt, ← hc, hcz]
        cases k with
        | zero =>
          simp only [cnt, rowAt_cons_zero] at hcR ⊢
          simp [List.count_append, count_top_zero R' hR'J, show x ≠ J + 1 by omega,
            List.count_replicate_self, hcR]
        | succ k =>
          have := cnt_ins_top J rs hrb k
          simp only [cnt, rowAt_cons_succ, rowAt_cons_zero] at this hcR ⊢
          rw [this, hcR]
          cases k <;> simp
    · rw [newRow_cons_some he]
      have hbJ : b ≤ J := hR'J b (by rw [hR'']; simp)
      have hbump : bump1 R x = (u ++ x :: (v ++ List.replicate c (J + 1)), some b) := by
        rw [hsplit, hR'', List.append_assoc, List.cons_append, bump1_append_le _ _ hu,
          bump1_cons_lt _ hxb]
      rw [ins_cons_some hbump]
      have hrsR : RowsSorted rs := hrs
      cases k with
      | zero =>
        have hu' : J + 1 ∉ u := fun hm => hnot (by rw [hR'']; simp [hm])
        have hv' : J + 1 ∉ v := fun hm => hnot (by rw [hR'']; simp [hm])
        simp [cnt, List.count_append, List.count_eq_zero_of_not_mem hu',
          List.count_eq_zero_of_not_mem hv', List.count_cons, show x ≠ J + 1 by omega, ← hc]
      | succ k =>
        have := cnt_ins J rs b hrsR hrb hbJ k
        simp only [cnt, rowAt_cons_succ] at this ⊢
        simpa using this

/-! ## Inserting a weakly increasing word of small letters -/

/-- Closed form of the top-letter counts relative to a starting state (`c0` counts, `ρ` shape
of the small letters): row `k` keeps `c0 k - min (c0 k) g_k` and receives
`min (c0 (k-1)) g_{k-1}`, where `g` is the growth of the small letters. -/
def Inv (J : ℕ) (c0 ρ : ℕ → ℕ) (rs : List (List ℕ)) : Prop :=
  ∀ k, cnt J rs k + min (c0 k) (sh (res J rs) k - ρ k) =
    c0 k + if k = 0 then 0 else min (c0 (k - 1)) (sh (res J rs) (k - 1) - ρ (k - 1))

theorem sh_res_ins (J : ℕ) (rs : List (List ℕ)) (x : ℕ) (hs : RowsSorted rs) (hx : x ≤ J)
    (k : ℕ) : sh (res J (ins rs x)) k = sh (res J rs) k + if k = newRow (res J rs) x then 1 else 0 := by
  rw [sh_eqv (res_ins_le J rs x hs hx) k, sh_ins]

theorem inv_step (J : ℕ) (c0 ρ : ℕ → ℕ) (rs : List (List ℕ)) (x : ℕ) (hs : RowsSorted rs)
    (hb : Bnd (J + 1) rs) (hx : x ≤ J) (hI : Inv J c0 ρ rs) (hρ : ∀ k, ρ k ≤ sh (res J rs) k)
    (htop : ∀ k < newRow (res J rs) x, sh (res J rs) k = ρ k) :
    Inv J c0 ρ (ins rs x) ∧ ∀ k, ρ k ≤ sh (res J (ins rs x)) k := by
  have hsh := sh_res_ins J rs x hs hx
  refine ⟨fun k => ?_, fun k => by rw [hsh]; have := hρ k; omega⟩
  obtain ⟨q, hq⟩ : ∃ q, newRow (res J rs) x = q := ⟨_, rfl⟩
  rw [hq] at hsh htop
  have hc := cnt_ins J rs x hs hb hx k
  rw [hq] at hc
  have hq1 : q ≠ 0 → sh (res J rs) (q - 1) = ρ (q - 1) := fun h => htop _ (by omega)
  have hρk := hρ k
  have hρk1 := hρ (k - 1)
  have hρq := hρ q
  rw [hsh k, hsh (k - 1)]
  by_cases hkq : k = q
  · subst hkq
    have hIk := hI k
    by_cases hk0 : k = 0
    · rw [if_pos hk0] at hIk ⊢
      split_ifs at hc ⊢ <;> omega
    · rw [if_neg hk0] at hIk ⊢
      rw [hq1 hk0] at hIk
      split_ifs at hc ⊢ <;> omega
  · by_cases hkq1 : k = q + 1
    · subst hkq1
      have hIk := hI (q + 1)
      have hIq := hI q
      simp only [Nat.add_sub_cancel, show q + 1 ≠ 0 by omega, show q + 1 ≠ q by omega, if_false,
        if_true, add_zero, false_and, true_and] at hIk hc hρk1 ⊢
      by_cases hq0 : q = 0
      · rw [if_pos hq0] at hIq
        split_ifs at hc ⊢ <;> omega
      · rw [if_neg hq0, hq1 hq0] at hIq
        split_ifs at hc ⊢ <;> omega
    · have hIk := hI k
      by_cases hk0 : k = 0
      · rw [if_pos hk0] at hIk ⊢
        split_ifs at hc ⊢ <;> omega
      · rw [if_neg hk0] at hIk ⊢
        split_ifs at hc ⊢ <;> omega

theorem inv_iter (J : ℕ) (c0 ρ : ℕ → ℕ) : ∀ (w : List ℕ) (rs : List (List ℕ)) (r : ℕ),
    RowsSorted rs → Bnd (J + 1) rs → w.Sorted (· ≤ ·) → (∀ x ∈ w, x ≤ J) →
    (∀ x ∈ w.head?, newRow (res J rs) x ≤ r) → Inv J c0 ρ rs →
    (∀ k, ρ k ≤ sh (res J rs) k) → (∀ k < r, sh (res J rs) k = ρ k) →
    Inv J c0 ρ (insW rs w) ∧ ∀ k, ρ k ≤ sh (res J (insW rs w)) k
  | [], rs, _, _, _, _, _, _, hI, hρ, _ => ⟨hI, hρ⟩
  | x :: w, rs, r, hs, hb, hw, hwJ, hhead, hI, hρ, htop => by
    have hxJ := hwJ x List.mem_cons_self
    have hqr : newRow (res J rs) x ≤ r := hhead x rfl
    obtain ⟨hI', hρ'⟩ := inv_step J c0 ρ rs x hs hb hxJ hI hρ
      (fun k hk => htop k (by omega))
    obtain ⟨hxw, hw'⟩ := List.sorted_cons.mp hw
    refine inv_iter J c0 ρ w (ins rs x) (newRow (res J rs) x) (ins_sorted rs hs x)
      (bnd_ins rs x hb (by omega)) hw' (fun y hy => hwJ y (List.mem_cons_of_mem _ hy)) ?_ hI' hρ' ?_
    · intro y hy
      have hyw : y ∈ w := List.mem_of_mem_head? hy
      rw [newRow_eqv (res_ins_le J rs x hs hxJ)]
      exact newRow_ins_le _ x y (res_sorted J hs) (hxw y hyw)
    · intro k hk
      rw [sh_res_ins J rs x hs hxJ, if_neg (by omega)]
      exact htop k (by omega)

theorem cnt_insW_top (J : ℕ) (a : ℕ) : ∀ rs : List (List ℕ), Bnd (J + 1) rs →
    (∀ k, cnt J (insW rs (List.replicate a (J + 1))) k = cnt J rs k + if k = 0 then a else 0) ∧
      Eqv (res J (insW rs (List.replicate a (J + 1)))) (res J rs) := by
  induction a with
  | zero => intro rs _; exact ⟨fun k => by simp [insW], Eqv.refl _⟩
  | succ a ih =>
    intro rs hb
    rw [List.replicate_succ, insW_cons]
    have hb' := bnd_ins rs (J + 1) hb le_rfl
    obtain ⟨h1, h2⟩ := ih _ hb'
    refine ⟨fun k => ?_, h2.trans (res_ins_gt J rs (J + 1) (by omega))⟩
    rw [h1, cnt_ins_top J rs hb]
    split_ifs <;> omega

/-- Fomin's local rule for row insertion (growth diagrams). -/
def Fsh (ρ μ ν : ℕ → ℕ) (a k : ℕ) : ℕ :=
  if k = 0 then max (μ 0) (ν 0) + a else max (μ k) (ν k) + min (μ (k - 1)) (ν (k - 1)) - ρ (k - 1)

theorem Fsh_comm (ρ μ ν : ℕ → ℕ) (a k : ℕ) : Fsh ρ μ ν a k = Fsh ρ ν μ a k := by
  unfold Fsh; split_ifs <;> omega

/-- The local rule: inserting `x` (weakly increasing, letters `≤ J`) and then `a` copies of
`J + 1` into a tableau with letters `≤ J + 1`. -/
theorem local_rule (J : ℕ) (T : List (List ℕ)) (hs : RowsSorted T) (hb : Bnd (J + 1) T)
    (x : List ℕ) (hx : x.Sorted (· ≤ ·)) (hxJ : ∀ y ∈ x, y ≤ J) (a k : ℕ) :
    sh (insW T (x ++ List.replicate a (J + 1))) k =
      Fsh (sh (res J T)) (sh T) (sh (insW (res J T) x)) a k := by
  set ρ := sh (res J T)
  set c0 := cnt J T
  have hI0 : Inv J c0 ρ T := fun k => by simp [c0, ρ]
  obtain ⟨hI, hρ⟩ := inv_iter J c0 ρ x T ((x.head?.map (newRow (res J T))).getD 0) hs hb hx hxJ
    (by intro y hy; rw [Option.mem_def] at hy; simp [hy]) hI0 (fun _ => le_rfl) (fun _ _ => rfl)
  set T1 := insW T x
  have hs1 : RowsSorted T1 := insW_sorted T hs x
  have hb1 : Bnd (J + 1) T1 := bnd_insW x (fun y hy => by have := hxJ y hy; omega) T hb
  obtain ⟨hc2, hr2⟩ := cnt_insW_top J a T1 hb1
  rw [insW_append]
  have hb2 := bnd_insW (List.replicate a (J + 1)) (fun y hy => by
    rw [List.eq_of_mem_replicate hy]) T1 hb1
  have hν : ∀ k, sh (res J T1) k = sh (insW (res J T) x) k := fun k => by
    rw [sh_eqv (res_insW J x T hs) k, filter_le_of_le x hxJ]
  have hsplitT : ∀ k, sh T k = ρ k + c0 k := fun k => sh_split J hb k
  rw [sh_split J hb2 k, sh_eqv hr2 k, hc2 k]
  have hIk := hI k
  have hIk1 := hI (k - 1)
  have hρk := hρ k
  have hρk1 := hρ (k - 1)
  rw [hν] at hIk hρk hρk1
  rw [hν (k - 1)] at hIk
  rw [hν k]
  unfold Fsh
  have h0 := hsplitT k
  have h1 := hsplitT (k - 1)
  have h00 := hsplitT 0
  split_ifs at hIk ⊢ with hk
  · subst hk; omega
  · omega

/-! ## The growth diagram of an ℕ-matrix -/

/-- Letters `q ≤ j` of label `p`, each `q` repeated `A p q` times (a weakly increasing word). -/
def rowW (A : ℕ → ℕ → ℕ) (p j : ℕ) : List ℕ :=
  (List.range j).flatMap (fun q => List.replicate (A p (q + 1)) (q + 1))

/-- The two-line array of labels `≤ i`, letters `≤ j`, read in lexicographic order. -/
def word (A : ℕ → ℕ → ℕ) (i j : ℕ) : List ℕ := (List.range i).flatMap (fun p => rowW A (p + 1) j)

/-- Shape of the insertion tableau of the submatrix with labels `≤ i` and letters `≤ j`. -/
def G (A : ℕ → ℕ → ℕ) (i j : ℕ) : ℕ → ℕ := sh (P (word A i j))

theorem rowW_succ (A : ℕ → ℕ → ℕ) (p j : ℕ) :
    rowW A p (j + 1) = rowW A p j ++ List.replicate (A p (j + 1)) (j + 1) := by
  simp [rowW, List.range_succ, List.flatMap_append]

theorem word_succ (A : ℕ → ℕ → ℕ) (i j : ℕ) : word A (i + 1) j = word A i j ++ rowW A (i + 1) j := by
  simp [word, List.range_succ, List.flatMap_append]

theorem mem_rowW {A : ℕ → ℕ → ℕ} {p j y : ℕ} (hy : y ∈ rowW A p j) : 1 ≤ y ∧ y ≤ j := by
  simp only [rowW, List.mem_flatMap, List.mem_range] at hy
  obtain ⟨q, hq, hy⟩ := hy
  rw [List.eq_of_mem_replicate hy]; omega

theorem mem_word {A : ℕ → ℕ → ℕ} {i j y : ℕ} (hy : y ∈ word A i j) : 1 ≤ y ∧ y ≤ j := by
  simp only [word, List.mem_flatMap] at hy
  obtain ⟨p, _, hy⟩ := hy
  exact mem_rowW hy

theorem rowW_sorted (A : ℕ → ℕ → ℕ) (p : ℕ) : ∀ j, (rowW A p j).Sorted (· ≤ ·)
  | 0 => by simp [rowW]
  | j + 1 => by
    rw [rowW_succ]
    refine List.pairwise_append.mpr ⟨rowW_sorted A p j, ?_, ?_⟩
    · exact List.pairwise_replicate.mpr (Or.inr le_rfl)
    · intro a ha b hb
      rw [List.eq_of_mem_replicate hb]
      have := (mem_rowW ha).2; omega

theorem rowW_filter (A : ℕ → ℕ → ℕ) (p j : ℕ) :
    (rowW A p (j + 1)).filter (fun x => decide (x ≤ j)) = rowW A p j := by
  rw [rowW_succ, List.filter_append, filter_le_of_le _ (fun y hy => (mem_rowW hy).2),
    filter_le_of_gt _ (fun y hy => by rw [List.eq_of_mem_replicate hy]; omega), List.append_nil]

theorem word_filter (A : ℕ → ℕ → ℕ) (j : ℕ) : ∀ i,
    (word A i (j + 1)).filter (fun x => decide (x ≤ j)) = word A i j
  | 0 => by simp [word]
  | i + 1 => by rw [word_succ, word_succ, List.filter_append, word_filter A j i, rowW_filter]

theorem G_zero_left (A : ℕ → ℕ → ℕ) (j : ℕ) : G A 0 j = fun _ => 0 := by
  funext k; simp [G, word, P, insW, sh]

theorem G_zero_right (A : ℕ → ℕ → ℕ) (i : ℕ) : G A i 0 = fun _ => 0 := by
  funext k
  have : word A i 0 = [] := by simp [word, rowW]
  simp [G, this, P, insW, sh]

theorem P_append (u v : List ℕ) : P (u ++ v) = insW (P u) v := by
  simp [P, insW_append]

/-- Fomin's local rule for the insertion shapes. -/
theorem local_G (A : ℕ → ℕ → ℕ) (i j : ℕ) :
    G A (i + 1) (j + 1) = fun k => Fsh (G A i j) (G A (i + 1) j) (G A i (j + 1)) (A (i + 1) (j + 1)) k := by
  funext k
  have hT : RowsSorted (P (word A i (j + 1))) := P_sorted _
  have hb : Bnd (j + 1) (P (word A i (j + 1))) :=
    bnd_insW _ (fun y hy => (mem_word hy).2) [] (by simp [Bnd])
  have h := local_rule j (P (word A i (j + 1))) hT hb (rowW A (i + 1) j) (rowW_sorted A _ j)
    (fun y hy => (mem_rowW hy).2) (A (i + 1) (j + 1)) k
  rw [← rowW_succ, ← P_append, ← word_succ] at h
  have hρ : sh (res j (P (word A i (j + 1)))) = G A i j := by
    funext k'
    rw [sh_eqv (res_P j _) k', word_filter]; rfl
  have hν : sh (insW (res j (P (word A i (j + 1)))) (rowW A (i + 1) j)) = G A (i + 1) j := by
    funext k'
    rw [sh_eqv (insW_eqv (res_P j _) _) k', word_filter, ← P_append, ← word_succ]; rfl
  rw [hρ, hν] at h
  rw [Fsh_comm]
  exact h

/-- Symmetry of the growth diagram: `G Aᵀ j i = G A i j`. -/
theorem G_transpose (A : ℕ → ℕ → ℕ) : ∀ i j, G (fun p q => A q p) j i = G A i j
  | 0, j => by rw [G_zero_left, G_zero_right]
  | i + 1, 0 => by rw [G_zero_left, G_zero_right]
  | i + 1, j + 1 => by
    rw [local_G, local_G, G_transpose A i j, G_transpose A (i + 1) j, G_transpose A i (j + 1)]
    funext k
    exact Fsh_comm _ _ _ _ _
termination_by i j => (i, j)

/-! ## A row-sorted tableau is determined by its restriction shapes -/

theorem rowAt_sorted {rs : List (List ℕ)} (h : RowsSorted rs) (k : ℕ) :
    (rowAt rs k).Sorted (· ≤ ·) := by
  induction rs generalizing k with
  | nil => simp
  | cons R rs ih =>
    cases k with
    | zero => exact h R List.mem_cons_self
    | succ k => exact ih (fun S hS => h S (List.mem_cons_of_mem _ hS)) k

theorem length_filter_le_succ (L : List ℕ) (y : ℕ) :
    (L.filter (fun x => decide (x ≤ y + 1))).length =
      (L.filter (fun x => decide (x ≤ y))).length + L.count (y + 1) := by
  induction L with
  | nil => rfl
  | cons z L ih =>
    by_cases h1 : z ≤ y
    · rw [List.filter_cons_of_pos (by simp; omega), List.filter_cons_of_pos (by simpa using h1),
        List.count_cons_of_ne (by omega)]
      simp only [List.length_cons]; omega
    · by_cases h2 : z = y + 1
      · subst h2
        rw [List.filter_cons_of_pos (by simp), List.filter_cons_of_neg (by simp),
          List.count_cons_self]
        simp only [List.length_cons]; omega
      · rw [List.filter_cons_of_neg (by simp; omega), List.filter_cons_of_neg (by simpa using h1),
          List.count_cons_of_ne (by omega)]
        exact ih

theorem length_filter_le_zero (L : List ℕ) :
    (L.filter (fun x => decide (x ≤ 0))).length = L.count 0 := by
  induction L with
  | nil => rfl
  | cons z L ih =>
    by_cases h : z = 0
    · subst h; rw [List.filter_cons_of_pos (by simp), List.count_cons_self, List.length_cons, ih]
    · rw [List.filter_cons_of_neg (by simp; omega), List.count_cons_of_ne (by omega)]; exact ih

theorem eqv_of_sh_res {rs rs' : List (List ℕ)} (hs : RowsSorted rs) (hs' : RowsSorted rs')
    (h : ∀ j k, sh (res j rs) k = sh (res j rs') k) : Eqv rs rs' := by
  intro k
  have hl : ∀ j, ((rowAt rs k).filter (fun x => decide (x ≤ j))).length =
      ((rowAt rs' k).filter (fun x => decide (x ≤ j))).length := by
    intro j; have := h j k; simpa only [sh, rowAt_res] using this
  apply List.eq_of_perm_of_sorted _ (rowAt_sorted hs k) (rowAt_sorted hs' k)
  rw [List.perm_iff_count]
  intro y
  cases y with
  | zero => rw [← length_filter_le_zero, ← length_filter_le_zero, hl]
  | succ y =>
    have h1 := length_filter_le_succ (rowAt rs k) y
    have h2 := length_filter_le_succ (rowAt rs' k) y
    rw [hl, hl] at h1
    omega

end OddMath.Frontier.OddLRRule
