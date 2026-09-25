import OddMath.Frontier.TableauReverseBoundary

/-!
Finite upward reverse row insertion, top-first input/output rows and path columns.
Fulton, Young Tableaux §1.1, printed p.8 / frozen preview PDF20, lines700–709:
remove the outside corner; in each preceding row replace the rightmost entry
strictly smaller than the incoming letter. The displaced entry is carried up.
Only existence and geometry are proved here, not either full-tableau inverse law.
-/
namespace OddMath.Frontier.TableauReverseRun
open TableauSign TableauEvaluation TableauRowStep TableauRowRecursion
  TableauReverseRow TableauBumpBoundary TableauReverseBoundary TableauCorner

structure ReverseRun (n : ℕ) where
  output : List (List (Fin n))
  letter : Fin n
  columns : List ℕ

-- On valid inputs the bottom case deletes a last entry. The raw function
-- does not validate corner predicates. It visits the selected row first and
-- then performs one installed reverseStep on each preceding row.
def reverseRows (n : ℕ) (rs : List (List (Fin n))) (r c : ℕ) : Option (ReverseRun n) :=
  match rs, r with
  | [], _ => none
  | w :: ws, 0 =>
    match w[c]? with
    | none => none
    | some b => some ⟨if c = 0 then ws else w.take c :: ws, b, [c]⟩
  | w :: ws, r+1 => do
    let q ← reverseRows n ws r c
    let (v,a,k) ← reverseStep n w q.letter
    pure ⟨v :: q.output, a, k :: q.columns⟩
termination_by structural rs

private def Geometry {n : ℕ} (rs : List (List (Fin n))) (r c : ℕ)
    (q : ReverseRun n) : Prop :=
  (∀ w ∈ q.output, w.Sorted (· ≤ ·)) ∧
  (∀ j : ℕ, ColumnBelow (q.output[j]?.getD []) (q.output[j+1]?.getD [])) ∧
  (∀ w ∈ q.output, w ≠ []) ∧
  (∀ j : ℕ, (q.output[j]?.getD []).length =
    if j = r then c else (rs[j]?.getD []).length) ∧
  q.columns.length = r+1 ∧ q.columns.Sorted (· ≥ ·) ∧
  q.columns.getLast? = some c ∧ q.output.drop (r+1) = rs.drop (r+1)

-- Information needed by the immediately preceding row, proved from execution.
private def HeadWitness {n : ℕ} (rs : List (List (Fin n))) (r c : ℕ)
    (q : ReverseRun n) : Prop :=
  match r with
  | 0 => (rs[0]?.getD []) = (rs[0]?.getD []).take c ++ [q.letter] ∧
      q.output[0]?.getD [] = (rs[0]?.getD []).take c ∧ q.columns = [c]
  | _+1 => ∃ d k, reverseStep n (rs[0]?.getD []) d =
      some (q.output[0]?.getD [],q.letter,k) ∧ q.columns.head? = some k

private theorem below_nil {n : ℕ} (w : List (Fin n)) : ColumnBelow w [] :=
  ⟨by simp, by simp⟩

private theorem take_below {n : ℕ} (w v : List (Fin n)) (c : ℕ)
    (h : ColumnBelow w v) (hb : v.length ≤ c) : ColumnBelow (w.take c) v := by
  obtain ⟨hl,hp⟩ := h
  refine ⟨by simp; omega, ?_⟩
  intro j hj
  simpa using hp j hj

private theorem split_last {n : ℕ} (w : List (Fin n)) (c : ℕ)
    (he : w.length = c+1) : ∃ b, w[c]? = some b ∧ w = w.take c ++ [b] := by
  have hc : c < w.length := by omega
  refine ⟨w[c], by simp [hc], ?_⟩
  rw [List.take_concat_get', ← he, List.take_length]


private theorem base_geometry (n : ℕ) (w : List (Fin n)) (ws : List (List (Fin n)))
    (c : ℕ) (hs : ∀ z ∈ w :: ws, z.Sorted (· ≤ ·))
    (hc : ∀ j : ℕ, ColumnBelow ((w::ws)[j]?.getD []) ((w::ws)[j+1]?.getD []))
    (hn : ∀ z ∈ w::ws, z ≠ []) (he : w.length = c+1)
    (hb : (ws[0]?.getD []).length ≤ c) :
    ∃ q, reverseRows n (w::ws) 0 c = some q ∧
      Geometry (w::ws) 0 c q ∧ HeadWitness (w::ws) 0 c q := by
  obtain ⟨b,hb',hw⟩ := split_last w c he
  have hs' : (w.take c).Sorted (· ≤ ·) := (hs w (by simp)).take
  have hl : (w.take c).length = c := by simp [List.length_take, he]
  have ht : ∀ j : ℕ, ColumnBelow (ws[j]?.getD []) (ws[j+1]?.getD []) := by
    intro j; simpa using hc (j+1)
  by_cases hz : c = 0
  · subst c
    have hws : ws = [] := by
      cases ws with
      | nil => rfl
      | cons v vs =>
        have hv := hn v (by simp)
        simp only [List.getElem?_cons_zero, Option.getD_some, Nat.le_zero] at hb
        exact False.elim (hv (List.length_eq_zero_iff.mp hb))
    subst ws
    refine ⟨⟨[],b,[0]⟩, by simp [reverseRows,he,hb'], ?_, ?_⟩
    · simp [Geometry, below_nil]
      intro j
      cases j <;> simp
    · simpa [HeadWitness] using hw
  · refine ⟨⟨w.take c :: ws,b,[c]⟩, by simp [reverseRows,he,hb',hz], ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, by simp, by simp, by simp, by simp⟩
      · intro z hz'
        rcases List.mem_cons.mp hz' with rfl | hz'
        · exact hs'
        · exact hs z (by simp [hz'])
      · intro j
        cases j with
        | zero =>
          exact take_below w (ws[0]?.getD []) c (by simpa using hc 0) hb
        | succ j => simpa using ht j
      · intro z hz'
        rcases List.mem_cons.mp hz' with rfl | hz'
        · intro hh; have := congrArg List.length hh; simp [hl] at this; exact hz this
        · exact hn z (by simp [hz'])
      · intro j
        cases j <;> simp [hl]
    · simpa [HeadWitness] using hw


private theorem path_bound (cs : List ℕ) (j k : ℕ) (hs : cs.Sorted (· ≥ ·))
    (hh : cs.head? = some j) (hjk : j ≤ k) : ∀ i ∈ cs, i ≤ k := by
  cases cs with
  | nil => simp at hh
  | cons x xs =>
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst x
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact hjk
    · exact le_trans ((List.sorted_cons.mp hs).1 i hi) hjk

private theorem preceding_step (n : ℕ) (w : List (Fin n)) (ws : List (List (Fin n)))
    (r c : ℕ) (q : ReverseRun n) (hs : w.Sorted (· ≤ ·))
    (hc : ColumnBelow w (ws[0]?.getD []))
    (he : (ws[r]?.getD []).length = c+1)
    (hg : Geometry ws r c q) (hw : HeadWitness ws r c q) :
    ∃ v a k, reverseStep n w q.letter = some (v,a,k) ∧
      ColumnBelow v (q.output[0]?.getD []) ∧ v.Sorted (· ≤ ·) ∧
      v.length = w.length ∧ (∀ j ∈ q.columns, j ≤ k) := by
  cases r with
  | zero =>
    obtain ⟨hws,hout,hcols⟩ := hw
    have hc' : ColumnBelow w ((ws[0]?.getD []).take c ++ [q.letter]) := hws ▸ hc
    obtain ⟨v,a,k,hr,hk,hv,hvs,hvl⟩ := reverse_terminal_boundary n w
      ((ws[0]?.getD []).take c) q.letter hs hc'
    have hl : ((ws[0]?.getD []).take c).length = c := by simp [List.length_take,he]
    refine ⟨v,a,k,hr,?_,hvs,hvl,?_⟩
    · rw [hout]; exact hv
    · simpa [hcols,hl] using hk
  | succ r =>
    obtain ⟨d,j,hr,hj⟩ := hw
    obtain ⟨v,a,k,hv,hk,hcol,hvs,hvl⟩ := reverse_bump_boundary n w
      (ws[0]?.getD []) (q.output[0]?.getD []) d q.letter j hs hc hr
    exact ⟨v,a,k,hv,hcol,hvs,hvl,path_bound q.columns j k hg.2.2.2.2.2.1 hj hk⟩

private theorem reverse_geometry_aux (n : ℕ) (rs : List (List (Fin n))) (r c : ℕ)
    (hs : ∀ w ∈ rs, w.Sorted (· ≤ ·))
    (hc : ∀ j : ℕ, ColumnBelow (rs[j]?.getD []) (rs[j+1]?.getD []))
    (hn : ∀ w ∈ rs, w ≠ []) (hr : r < rs.length)
    (he : (rs[r]?.getD []).length = c+1)
    (hb : (rs[r+1]?.getD []).length ≤ c) :
    ∃ q, reverseRows n rs r c = some q ∧ Geometry rs r c q ∧ HeadWitness rs r c q := by
  induction r generalizing rs with
  | zero =>
    cases rs with
    | nil => simp at hr
    | cons w ws => exact base_geometry n w ws c hs hc hn (by simpa using he) (by simpa using hb)
  | succ r ih =>
    cases rs with
    | nil => simp at hr
    | cons w ws =>
      have hst : ∀ v ∈ ws, v.Sorted (· ≤ ·) := fun v hv => hs v (by simp [hv])
      have hnt : ∀ v ∈ ws, v ≠ [] := fun v hv => hn v (by simp [hv])
      have hct : ∀ j : ℕ, ColumnBelow (ws[j]?.getD []) (ws[j+1]?.getD []) := by
        intro j; simpa using hc (j+1)
      obtain ⟨q,hq,hg,hw⟩ := ih ws hst hct hnt (by simpa using hr)
        (by simpa using he) (by simpa using hb)
      obtain ⟨v,a,k,hv,hcol,hvs,hvl,hpath⟩ := preceding_step n w ws r c q
        (hs w (by simp)) (by simpa using hc 0) (by simpa using he) hg hw
      obtain ⟨hqs,hqc,hqn,hql,hcl,hcs,hce,hqt⟩ := hg
      refine ⟨⟨v::q.output,a,k::q.columns⟩, by simp [reverseRows,hq,hv], ?_, ?_⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact hvs
          · exact hqs z hz
        · intro j
          cases j with
          | zero => exact hcol
          | succ j => simpa using hqc j
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · intro hz
            have := hn w (by simp)
            apply this
            apply List.length_eq_zero_iff.mp
            simpa [hz] using hvl.symm
          · exact hqn z hz
        · intro j
          cases j with
          | zero => simpa using hvl
          | succ j => simpa using hql j
        · simpa using congrArg Nat.succ hcl
        · exact List.sorted_cons.mpr ⟨hpath,hcs⟩
        · simp [List.getLast?_cons, hce]
        · simpa using hqt
      · exact ⟨q.letter,k,by simpa using hv,by simp⟩


theorem reverseRows_geometry (n : ℕ) (rs : List (List (Fin n))) (r c : ℕ)
    (hs : ∀ w ∈ rs, w.Sorted (· ≤ ·))
    (hc : ∀ j : ℕ, ColumnBelow (rs[j]?.getD []) (rs[j+1]?.getD []))
    (hn : ∀ w ∈ rs, w ≠ []) (hr : r < rs.length)
    (he : (rs[r]?.getD []).length = c+1)
    (hb : (rs[r+1]?.getD []).length ≤ c) :
    ∃ q, reverseRows n rs r c = some q ∧
      (∀ w ∈ q.output, w.Sorted (· ≤ ·)) ∧
      (∀ j : ℕ, ColumnBelow (q.output[j]?.getD []) (q.output[j+1]?.getD [])) ∧
      (∀ w ∈ q.output, w ≠ []) ∧
      (∀ j : ℕ, (q.output[j]?.getD []).length =
        if j = r then c else (rs[j]?.getD []).length) ∧
      q.columns.length = r+1 ∧ q.columns.Sorted (· ≥ ·) ∧
      q.columns.getLast? = some c ∧ q.output.drop (r+1) = rs.drop (r+1) := by
  obtain ⟨q,heq,hg,_⟩ := reverse_geometry_aux n rs r c hs hc hn hr he hb
  exact ⟨q,heq,hg⟩

private theorem rows_getD (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (hT : InAlphabet n T) (r : ℕ) :
    (rows n T hT)[r]?.getD [] = row n T hT r := by
  by_cases hr : r < μ.colLen 0
  · simp [rows, hr]
  · have hz : μ.rowLen r = 0 := by
      have hn : ¬ (r, 0) ∈ μ := by simpa only [YoungDiagram.mem_iff_lt_colLen] using hr
      rw [YoungDiagram.mem_iff_lt_rowLen] at hn
      omega
    have he : row n T hT r = [] := List.length_eq_zero_iff.mp (by rw [row_length, hz])
    have ho : (List.range (μ.colLen 0))[r]? = none :=
      List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hr)
    simp [rows, ho, he]

theorem tableau_reverseRows_geometry (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (hT : InAlphabet n T) (p : ℕ × ℕ) (hp : IsCorner μ p) :
    let rs := rows n T hT
    let r := p.1
    let c := p.2
    ∃ q, reverseRows n rs r c = some q ∧
      (∀ w ∈ q.output, w.Sorted (· ≤ ·)) ∧
      (∀ j : ℕ, ColumnBelow (q.output[j]?.getD []) (q.output[j+1]?.getD [])) ∧
      (∀ w ∈ q.output, w ≠ []) ∧
      (∀ j : ℕ, (q.output[j]?.getD []).length =
        if j = r then c else (rs[j]?.getD []).length) ∧
      q.columns.length = r+1 ∧ q.columns.Sorted (· ≥ ·) ∧
      q.columns.getLast? = some c ∧ q.output.drop (r+1) = rs.drop (r+1) := by
  apply reverseRows_geometry n (rows n T hT) p.1 p.2
    (rows_sorted n μ T hT) (TableauRunGeometry.rows_columns n μ T hT)
    (TableauRunGeometry.rows_nonempty n μ T hT)
  · rw [rows_length]
    have h := YoungDiagram.mem_iff_lt_colLen.mp hp.1
    exact lt_of_lt_of_le h (μ.colLen_anti 0 p.2 (Nat.zero_le _))
  · rw [rows_getD, row_length]
    exact corner_rowLen μ p hp
  · rw [rows_getD, row_length]
    have h := hp.2.1
    rw [YoungDiagram.mem_iff_lt_rowLen] at h
    omega

#check reverseRows_geometry
#print axioms reverseRows_geometry
#check rows_getD
#print axioms rows_getD
#check tableau_reverseRows_geometry
#print axioms tableau_reverseRows_geometry

#check path_bound
#print axioms path_bound
#check preceding_step
#print axioms preceding_step
#check reverse_geometry_aux
#print axioms reverse_geometry_aux

#check base_geometry
#print axioms base_geometry

#check reverseRows
#print axioms reverseRows
#check Geometry
#print axioms Geometry
#check HeadWitness
#print axioms HeadWitness
#check below_nil
#print axioms below_nil
#check take_below
#print axioms take_below
#check split_last
#print axioms split_last
end OddMath.Frontier.TableauReverseRun
