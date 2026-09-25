import OddMath.Frontier.TableauReverseRow
import OddMath.Frontier.TableauCorner

/-!
# Adjacent reverse-carry boundary

Fulton, Young Tableaux §1.1, printed p.8 (publisher preview PDF20),
lines700–709 of the frozen text: select the rightmost entry strictly less
than the incoming letter. This proves one adjacent nonfailure/preservation
step, not full upward recursion or either full-tableau inverse law.
-/
namespace OddMath.Frontier.TableauReverseBoundary
open TableauSign TableauEvaluation TableauRowStep TableauRowRecursion
  TableauReverseRow TableauBumpBoundary TableauCorner

private theorem below_nil {n : ℕ} (upper : List (Fin n)) : ColumnBelow upper [] :=
  ⟨by simp, by simp⟩

private theorem below_cons {n : ℕ} (x y : Fin n) (xs ys : List (Fin n)) :
    ColumnBelow (x :: xs) (y :: ys) ↔ x < y ∧ ColumnBelow xs ys := by
  constructor
  · rintro ⟨hl,hp⟩
    refine ⟨?_, ⟨by simpa using hl, ?_⟩⟩
    · simpa using hp 0 (by simp)
    · intro c hc
      simpa using hp (c+1) (by simpa using hc)
  · rintro ⟨hxy,hl,hp⟩
    refine ⟨by simpa using hl, ?_⟩
    intro c hc
    cases c with
    | zero => simpa using hxy
    | succ c => simpa using hp c (by simpa using hc)

private theorem reverse_length (n : ℕ) (w v : List (Fin n)) (b a : Fin n) (c : ℕ)
    (hr : reverseStep n w b = some (v,a,c)) : v.length = w.length := by
  obtain ⟨u,z,rfl,rfl,_,_,_⟩ := reverseStep_spec n w v b a c hr
  simp

-- A lower suffix uniformly above the replacement stays strictly below the upper row.
private theorem reverse_below_bound (n : ℕ) (upper lower v : List (Fin n))
    (b a : Fin n) (c : ℕ) (hc : ColumnBelow upper lower)
    (hb : ∀ y ∈ lower, b < y) (hr : reverseStep n upper b = some (v,a,c)) :
    ColumnBelow v lower := by
  induction upper generalizing lower v a c with
  | nil => simp [reverseStep] at hr
  | cons x xs ih =>
    cases lower with
    | nil => exact below_nil v
    | cons y ys =>
      obtain ⟨hxy,hcols⟩ := (below_cons x y xs ys).mp hc
      have hy := hb y (by simp)
      have hys : ∀ z ∈ ys, b < z := fun z hz => hb z (by simp [hz])
      cases he : reverseStep n xs b with
      | none =>
        by_cases hx : x < b
        · simp only [reverseStep, he, hx, if_true, Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl,rfl,rfl⟩ := hr
          exact (below_cons b y xs ys).mpr ⟨hy,hcols⟩
        · simp [reverseStep, he, hx] at hr
      | some t =>
        rcases t with ⟨v',a',c'⟩
        simp only [reverseStep, he, Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl,rfl,rfl⟩ := hr
        exact (below_cons x y v' ys).mpr ⟨hxy,ih ys v' a' c' hcols hys he⟩

-- Induct through the retained lower prefix. The strict witness is at its end.
private theorem terminal_raw (n : ℕ) (upper lower : List (Fin n)) (b : Fin n)
    (hc : ColumnBelow upper (lower ++ [b])) :
    ∃ v a c, reverseStep n upper b = some (v,a,c) ∧
      lower.length ≤ c ∧ ColumnBelow v lower := by
  induction lower generalizing upper with
  | nil =>
    cases upper with
    | nil => obtain ⟨hl,_⟩ := hc; simp at hl
    | cons x xs =>
      have hx := ((below_cons x b xs []).mp hc).1
      cases he : reverseStep n xs b with
      | none => exact ⟨b::xs,x,0,by simp [reverseStep,he,hx],by simp,below_nil _⟩
      | some t =>
        rcases t with ⟨v,a,c⟩
        exact ⟨x::v,a,c+1,by simp [reverseStep,he],by simp,below_nil _⟩
  | cons y ys ih =>
    cases upper with
    | nil => obtain ⟨hl,_⟩ := hc; simp at hl
    | cons x xs =>
      obtain ⟨hxy,hcols⟩ := (below_cons x y xs (ys ++ [b])).mp hc
      obtain ⟨v,a,c,hr,hc',hv⟩ := ih xs hcols
      exact ⟨x::v,a,c+1,by simp [reverseStep,hr],by simpa using Nat.succ_le_succ hc',
        (below_cons x y v ys).mpr ⟨hxy,hv⟩⟩

-- Lower reverseStep supplies precisely this strict split and suffix bound.
private theorem bump_raw (n : ℕ) (upper u z : List (Fin n)) (b d : Fin n)
    (hc : ColumnBelow upper (u ++ (b :: z))) (hbd : b < d)
    (hz : ∀ y ∈ z, d ≤ y) :
    ∃ v a c, reverseStep n upper b = some (v,a,c) ∧
      u.length ≤ c ∧ ColumnBelow v (u ++ (d :: z)) := by
  induction u generalizing upper with
  | nil =>
    cases upper with
    | nil => obtain ⟨hl,_⟩ := hc; simp at hl
    | cons x xs =>
      obtain ⟨hxb,hcols⟩ := (below_cons x b xs z).mp hc
      cases he : reverseStep n xs b with
      | none =>
        exact ⟨b::xs,x,0,by simp [reverseStep,he,hxb],by simp,
          (below_cons b d xs z).mpr ⟨hbd,hcols⟩⟩
      | some t =>
        rcases t with ⟨v,a,c⟩
        have hv := reverse_below_bound n xs z v b a c hcols
          (fun y hy => lt_of_lt_of_le hbd (hz y hy)) he
        exact ⟨x::v,a,c+1,by simp [reverseStep,he],by simp,
          (below_cons x d v z).mpr ⟨lt_trans hxb hbd,hv⟩⟩
  | cons y ys ih =>
    cases upper with
    | nil => obtain ⟨hl,_⟩ := hc; simp at hl
    | cons x xs =>
      obtain ⟨hxy,hcols⟩ := (below_cons x y xs (ys ++ (b::z))).mp hc
      obtain ⟨v,a,c,hr,hc',hv⟩ := ih xs hcols
      exact ⟨x::v,a,c+1,by simp [reverseStep,hr],by simpa using Nat.succ_le_succ hc',
        (below_cons x y v (ys ++ (d::z))).mpr ⟨hxy,hv⟩⟩

theorem reverse_terminal_boundary (n : ℕ) (upper lower : List (Fin n)) (b : Fin n)
    (hs : upper.Sorted (· ≤ ·)) (hc : ColumnBelow upper (lower ++ [b])) :
    ∃ v a c, reverseStep n upper b = some (v,a,c) ∧
      lower.length ≤ c ∧ ColumnBelow v lower ∧ v.Sorted (· ≤ ·) ∧
      v.length = upper.length := by
  obtain ⟨v,a,c,hr,hc',hv⟩ := terminal_raw n upper lower b hc
  exact ⟨v,a,c,hr,hc',hv,reverseStep_sorted n upper v b a c hs hr,
    reverse_length n upper v b a c hr⟩

theorem reverse_bump_boundary (n : ℕ) (upper lower lower' : List (Fin n))
    (d b : Fin n) (j : ℕ) (hs : upper.Sorted (· ≤ ·))
    (hc : ColumnBelow upper lower)
    (hr : reverseStep n lower d = some (lower',b,j)) :
    ∃ v a c, reverseStep n upper b = some (v,a,c) ∧
      j ≤ c ∧ ColumnBelow v lower' ∧ v.Sorted (· ≤ ·) ∧
      v.length = upper.length := by
  obtain ⟨u,z,rfl,rfl,rfl,hbd,hz⟩ := reverseStep_spec n lower lower' d b j hr
  obtain ⟨v,a,c,he,hc',hv⟩ := bump_raw n upper u z b d hc hbd hz
  exact ⟨v,a,c,he,hc',hv,reverseStep_sorted n upper v b a c hs he,
    reverse_length n upper v b a c he⟩

-- Entry reconstruction, not merely a row-length or cardinality equality.
private theorem corner_row_split (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (hT : InAlphabet n T) (r c : ℕ) (hp : IsCorner μ (r+1,c))
    (b : Fin n) (hb : b.val + 1 = T.entry (r+1) c) :
    row n T hT (r+1) = (row n T hT (r+1)).take c ++ [b] := by
  apply (List.map_inj_right (f := fun i : Fin n => i.val + 1)
    (by intro a b h; apply Fin.ext; change a.val+1 = b.val+1 at h; omega)).mp
  rw [List.map_append, List.map_take, row_labels, corner_rowLen μ (r+1,c) hp,
    ← List.map_take, List.take_range]
  simp [List.range_succ, hb]

theorem tableau_corner_start (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (hT : InAlphabet n T) (r c : ℕ) (hp : IsCorner μ (r+1,c))
    (b : Fin n) (hb : b.val + 1 = T.entry (r+1) c) :
    ∃ v a k, reverseStep n (row n T hT r) b = some (v,a,k) ∧
      c ≤ k ∧ ColumnBelow v ((row n T hT (r+1)).take c) ∧
      v.Sorted (· ≤ ·) ∧ v.length = μ.rowLen r := by
  have hcol : ColumnBelow (row n T hT r) ((row n T hT (r+1)).take c ++ [b]) := by
    rw [← corner_row_split n μ T hT r c hp b hb]
    exact rows_columnBelow n μ T hT r
  obtain ⟨v,a,k,hr,hk,hc,hs,hl⟩ := reverse_terminal_boundary n (row n T hT r)
    ((row n T hT (r+1)).take c) b (row_sorted n μ T hT r) hcol
  have ht : ((row n T hT (r+1)).take c).length = c := by
    simp [List.length_take, row_length, corner_rowLen μ (r+1,c) hp]
  exact ⟨v,a,k,hr,ht ▸ hk,hc,hs,hl.trans (row_length n μ T hT r)⟩

theorem tableau_reverse_boundary (n : ℕ) (μ : YoungDiagram) (T : PositiveTableau μ)
    (hT : InAlphabet n T) (r : ℕ) (lower' : List (Fin n)) (d b : Fin n)
    (j : ℕ) (hr : reverseStep n (row n T hT (r+1)) d = some (lower',b,j)) :
    ∃ v a c, reverseStep n (row n T hT r) b = some (v,a,c) ∧
      j ≤ c ∧ ColumnBelow v lower' ∧ v.Sorted (· ≤ ·) ∧
      v.length = μ.rowLen r := by
  obtain ⟨v,a,c,he,hc,hv,hs,hl⟩ := reverse_bump_boundary n (row n T hT r)
    (row n T hT (r+1)) lower' d b j (row_sorted n μ T hT r)
    (rows_columnBelow n μ T hT r) hr
  exact ⟨v,a,c,he,hc,hv,hs,hl.trans (row_length n μ T hT r)⟩

#print axioms below_nil
#print axioms below_cons
#print axioms reverse_length
#print axioms reverse_below_bound
#print axioms terminal_raw
#print axioms bump_raw
#print axioms corner_row_split
#print axioms reverse_terminal_boundary
#print axioms reverse_bump_boundary
#print axioms tableau_corner_start
#print axioms tableau_reverse_boundary
end OddMath.Frontier.TableauReverseBoundary
