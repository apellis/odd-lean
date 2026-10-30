/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.PrefixQPDistinct
import OddMath.QuiverHecke.CyclotomicAction.PrefixQPEquation
/-! # Signed QP polynomial transport to the append endpoint

`qpProduct_comp_moveHom` transports the independently evaluated ordered product
through the moving chain. This supplies the polynomial comparison needed for
`DeformedBoundaryDivision.md` §3; it is not the full chain norm or boundary S.
The library crossing normalization retains the repeated-even factor −1.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

/-- The signed QP polynomial at the append endpoint, distinct from the chain norm. -/
def appendQPFactor (i : I) (v : List I) (j : I) (b : ℕ) :
    End ((pres D Sc).obj (ob D (v ++ [i]))) :=
  if j = i then
    if D.parity i = 1 then
      (dotE D Sc (v ++ [i]) b - dotE D Sc (v ++ [i]) v.length) ^ 2
    else -1
  else qPoly D Sc (dotE D Sc (v ++ [i]) v.length) (dotE D Sc (v ++ [i]) b) i j

def appendQPProduct (i : I) (v : List I) : End ((pres D Sc).obj (ob D (v ++ [i]))) :=
  ((List.range v.length).map fun b => appendQPFactor D Sc i v (v.getD b i) b).prod

private theorem split_getD (v : List I) (i : I) (b : ℕ) (hb : b < v.length) :
    v = v.take b ++ [v.getD b i] ++ v.drop (b + 1) := by
  induction v generalizing b with
  | nil => simp at hb
  | cons x v ih =>
    cases b with
    | zero => simp
    | succ b => simpa using congrArg (List.cons x) (ih b (by simpa using hb))

theorem dot_getD_comp_moveHom (i : I) (v : List I) (b : ℕ) (hb : b < v.length) :
    dotE D Sc (i :: v) (b + 1) ≫ moveHom D Sc i [] v =
      SKM.zsign k (D.parity (v.getD b i) * (D.parity i * wordSumParity D v)) •
        (moveHom D Sc i [] v ≫ dotE D Sc (v ++ [i]) b) := by
  have h := dot_mem_comp_moveHom D Sc i (v.getD b i) (v.drop (b + 1)) (v.take b)
    [] v (split_getD v i b hb)
  simpa only [List.nil_append, List.length_nil, zero_add, List.length_take,
    Nat.min_eq_left (Nat.le_of_lt hb), Nat.add_comm 1 b] using h

theorem qpFactor_comp_moveHom (i : I) (v : List I) (b : ℕ) (hb : b < v.length) :
    qpFactor D Sc i v (v.getD b i) b ≫ moveHom D Sc i [] v =
      moveHom D Sc i [] v ≫ appendQPFactor D Sc i v (v.getD b i) b := by
  have hm := dot_comp_moveHom D Sc i [] v
  simp only [List.nil_append, List.length_nil, zero_add] at hm
  have ho := dot_getD_comp_moveHom D Sc i v b hb
  have hm' := congrArg (SKM.zsign k (D.parity i * wordSumParity D v) • ·) hm
  have ho' := congrArg (SKM.zsign k (D.parity (v.getD b i) *
    (D.parity i * wordSumParity D v)) • ·) ho
  simp only [smul_smul, zsign_mul_self, one_smul] at hm' ho'
  unfold qpFactor appendQPFactor
  split_ifs with hj hp
  · rw [hj, hp, one_mul] at ho'
    have hs : moveHom D Sc i [] v ≫
        (dotE D Sc (v ++ [i]) b - dotE D Sc (v ++ [i]) v.length : End _) =
        SKM.zsign k (D.parity i * wordSumParity D v) •
          ((dotE D Sc (i :: v) (b + 1) - dotE D Sc (i :: v) 0 : End _) ≫
            moveHom D Sc i [] v) := by
      rw [Preadditive.comp_sub, Preadditive.sub_comp, smul_sub, ← ho', ← hm', hp]
    have he := comp_pow_of_signed _ _ _ _ hs 2
    simpa only [pow_two (SKM.zsign k _), zsign_mul_self, one_smul] using he.symm
  · change (- (𝟙 _) : _ ⟶ _) ≫ _ = _ ≫ (- (𝟙 _) : _ ⟶ _)
    rw [Preadditive.neg_comp, Preadditive.comp_neg, Category.id_comp, Category.comp_id]
  · symm
    apply comp_qPoly D Sc _ _ _ _ _ i (v.getD b i)
      (SKM.zsign k (D.parity i * wordSumParity D v))
      (SKM.zsign k (D.parity (v.getD b i) * (D.parity i * wordSumParity D v)))
      hm'.symm ho'.symm
    · intro n hn
      apply zsign_pow_eq_one
      rw [← mul_assoc, hn, zero_mul]
    · intro n hn
      apply zsign_pow_eq_one
      rw [← mul_assoc, hn, zero_mul]

theorem qpProduct_comp_moveHom (i : I) (v : List I) :
    qpProduct D Sc i v ≫ moveHom D Sc i [] v =
      moveHom D Sc i [] v ≫ appendQPProduct D Sc i v := by
  unfold qpProduct appendQPProduct
  have h (l : List ℕ) (hl : ∀ b ∈ l, b < v.length) :
      (l.map fun b => qpFactor D Sc i v (v.getD b i) b).prod ≫ moveHom D Sc i [] v =
        moveHom D Sc i [] v ≫ (l.map fun b => appendQPFactor D Sc i v (v.getD b i) b).prod := by
    induction l with
    | nil =>
      change (𝟙 _ : _ ⟶ _) ≫ _ = _ ≫ (𝟙 _ : _ ⟶ _)
      rw [Category.id_comp, Category.comp_id]
    | cons b l ih =>
      simp only [List.map_cons, List.prod_cons, End.mul_def, Category.assoc]
      rw [qpFactor_comp_moveHom D Sc i v b (hl b (by simp)),
        ← Category.assoc, ih (fun c hc => hl c (by simp [hc])), Category.assoc]
  exact h _ (fun b hb => List.mem_range.mp hb)
end OddMath.QuiverHecke
