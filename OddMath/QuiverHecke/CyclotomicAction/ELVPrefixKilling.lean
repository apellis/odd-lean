/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVOldRightContext

/-!
# All-prefix relation killing over the ELV coefficient category

The relation-killing identity (K) of `DeformedGlobalQP.md` §2, needed by the
repeated-colour QP induction. Naturality acts on the full coefficient-plus-diagram
parity. The old two-sided ideal, rather than a moving-strand cyclotomic quotient,
is used for vanishing. All cutoffs and both moving-colour parities are retained.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The affine moving chain with unit full ELV coefficient. -/
def move (i : I) (v : List I) : hom D Sc cutoff (i :: v) (v ++ [i]) :=
  (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] moveHom D Sc i [] v

private theorem move_induction_hom {v w : List I} {P : hom D Sc cutoff v w → Prop}
    (x : hom D Sc cutoff v w) (zero : P 0)
    (tmul : ∀ (p q : ZMod 2) (a : (obj D Sc cutoff v).fst ⟶ (obj D Sc cutoff w).fst)
      (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)),
      a ∈ parity (R := k) _ _ p → f ∈ parity (R := k) _ _ q → P (BoxProd.tmulHom a f))
    (add : ∀ x y, P x → P y → P (x + y)) : P x :=
  BoxProd.induction_on_homogeneous (P := P) x zero tmul add

/-- Naturality of the moving chain for arbitrary full-coefficient old morphisms.
The word-parity equality is automatic on the permutation blocks used below. -/
theorem insert_comp_move (i : I) {v w : List I}
    (hp : wordSumParity D w = wordSumParity D v) (f : hom D Sc cutoff v w) :
    insert D Sc cutoff i v w f ≫ move D Sc cutoff i w =
      move D Sc cutoff i v ≫ rightContext D Sc cutoff [i] v w
        (twist k (D.parity i * wordSumParity D v) f) := by
  induction f using move_induction_hom D Sc cutoff with
  | zero => simp only [map_zero, Limits.zero_comp, Limits.comp_zero]
  | add f g hf hg => simp only [map_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]
  | tmul q r a f ha hf =>
    change f ∈ parity (R := k) ((pres D Sc).obj (ob D v))
      ((pres D Sc).obj (ob D w)) r at hf
    have hm := moveHom_parity D Sc i [] w
    rw [hp] at hm
    have hnat := hom_comp_moveHom D Sc i f
    rw [twist_of_mem _ hf, MonoidalSupercategory.smul_whiskerRight (R := k),
      Linear.comp_smul] at hnat
    have ht : (a ⊗ₜ[k] f : hom D Sc cutoff v w) ∈
        parity (R := k) (obj D Sc cutoff v) (obj D Sc cutoff w) (q + r) :=
      BoxProd.tmul_mem_parity (X := obj D Sc cutoff v) (Y := obj D Sc cutoff w) ha hf
    change insert D Sc cutoff i v w (a ⊗ₜ[k] f) ≫ move D Sc cutoff i w =
      move D Sc cutoff i v ≫ rightContext D Sc cutoff [i] v w
        (twist k (D.parity i * wordSumParity D v) (a ⊗ₜ[k] f))
    rw [twist_of_mem _ ht, map_smul, Linear.comp_smul]
    change (BoxProd.tmulHom (X := obj D Sc cutoff (i :: v))
        (Y := obj D Sc cutoff (i :: w)) a (affineInsert D Sc i v w f)) ≫
        BoxProd.tmulHom (X := obj D Sc cutoff (i :: w))
          (Y := obj D Sc cutoff (w ++ [i])) (SuperalgebraCat.ofElem 1)
          (moveHom D Sc i [] w) =
      sign k ((D.parity i * wordSumParity D v) * (q + r)) •
        (BoxProd.tmulHom (X := obj D Sc cutoff (i :: v))
          (Y := obj D Sc cutoff (v ++ [i])) (SuperalgebraCat.ofElem 1)
          (moveHom D Sc i [] v) ≫
        BoxProd.tmulHom (X := obj D Sc cutoff (v ++ [i]))
          (Y := obj D Sc cutoff (w ++ [i])) a (affineRightContext D Sc [i] v w f))
    let a' : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff := a
    have hone : SuperalgebraCat.ofElem
        (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ∈
        parity (R := k) (obj D Sc cutoff (i :: v)).fst
          (obj D Sc cutoff (v ++ [i])).fst 0 := id_mem (R := k) _
    have hr : affineRightContext D Sc [i] v w f ∈
        parity (R := k) (obj D Sc cutoff (v ++ [i])).snd
          (obj D Sc cutoff (w ++ [i])).snd r :=
      MonoidalSupercategory.whiskerRight_mem ((pres D Sc).obj (ob D [i])) hf
    rw [BoxProd.tmulHom_comp_tmulHom
      (X := obj D Sc cutoff (i :: v)) (Y := obj D Sc cutoff (i :: w))
      (Z := obj D Sc cutoff (w ++ [i])) ha _ _ hm]
    change koszulSign q (D.parity i * wordSumParity D v) •
      ((1 * a') ⊗ₜ[k] (affineInsert D Sc i v w f ≫ moveHom D Sc i [] w)) =
      sign k ((D.parity i * wordSumParity D v) * (q + r)) •
        (BoxProd.tmulHom (X := obj D Sc cutoff (i :: v))
          (Y := obj D Sc cutoff (v ++ [i])) (SuperalgebraCat.ofElem 1)
          (moveHom D Sc i [] v) ≫
        BoxProd.tmulHom (X := obj D Sc cutoff (v ++ [i]))
          (Y := obj D Sc cutoff (w ++ [i])) a (affineRightContext D Sc [i] v w f))
    rw [BoxProd.tmulHom_comp_tmulHom
        (X := obj D Sc cutoff (i :: v)) (Y := obj D Sc cutoff (v ++ [i]))
        (Z := obj D Sc cutoff (w ++ [i])) hone _ _ hr]
    change koszulSign q (D.parity i * wordSumParity D v) •
      ((1 * a') ⊗ₜ[k] (affineInsert D Sc i v w f ≫ moveHom D Sc i [] w)) =
      sign k ((D.parity i * wordSumParity D v) * (q + r)) •
        (koszulSign 0 r • ((a' * 1) ⊗ₜ[k]
          (moveHom D Sc i [] v ≫ affineRightContext D Sc [i] v w f)))
    rw [one_mul, mul_one, show affineInsert D Sc i v w f ≫ moveHom D Sc i [] w =
      sign k ((D.parity i * wordSumParity D v) * r) •
        (moveHom D Sc i [] v ≫ affineRightContext D Sc [i] v w f) from hnat]
    simp only [TensorProduct.tmul_smul, koszulSign_smul (R := k), zero_mul,
      sign_zero, one_smul, smul_smul, ← sign_add, mul_add, mul_comm q]

/-- Any old ideal morphism kills after the moving chain, in every right context.
No homogeneity of the old morphism or ambient continuation is required. -/
theorem projection_move_ideal_context (i : I) {v w : List I}
    (hp : wordSumParity D w = wordSumParity D v) (σ z : List I)
    (f : hom D Sc cutoff v w) (hf : f ∈ ideal D Sc cutoff v w)
    (h : hom D Sc cutoff ((w ++ [i]) ++ σ) z) :
    projection D Sc cutoff i (v ++ σ) z
      (rightContext D Sc cutoff σ (i :: v) (w ++ [i])
        (move D Sc cutoff i v ≫ rightContext D Sc cutoff [i] v w f) ≫ h) = 0 := by
  have hn := insert_comp_move D Sc cutoff i hp
    (twist k (D.parity i * wordSumParity D v) f)
  rw [twist_twist] at hn
  rw [← hn, rightContext_comp, rightContext_insert, Category.assoc]
  exact projection_old_ideal D Sc cutoff i
    (ideal_rightContext D Sc cutoff σ (twist_ideal D Sc cutoff _ hf)) _

/-- Full-coefficient prefix killing with an arbitrary old Hom before the relation,
and an arbitrary spectator context and ambient continuation. -/
theorem projection_prefix_relation_context (i j : I) {v t : List I}
    (hp : wordSumParity D (j :: t) = wordSumParity D v) (σ z : List I)
    (f : hom D Sc cutoff v (j :: t))
    (h : hom D Sc cutoff (((j :: t) ++ [i]) ++ σ) z) :
    projection D Sc cutoff i (v ++ σ) z
      (rightContext D Sc cutoff σ (i :: v) ((j :: t) ++ [i])
        (move D Sc cutoff i v ≫ rightContext D Sc cutoff [i] v (j :: t) f) ≫
        relation D Sc cutoff j ((t ++ [i]) ++ σ) ≫ h) = 0 := by
  have hz := projection_move_ideal_context D Sc cutoff i hp σ z
    (f ≫ relation D Sc cutoff j t)
    (comp_ideal D Sc cutoff f (relation_mem D Sc cutoff j t)) h
  rw [rightContext_comp D Sc cutoff [i] f (relation D Sc cutoff j t),
    rightContext_relation D Sc cutoff [i] j t] at hz
  rw [← Category.assoc, rightContext_comp] at hz
  have hr := rightContext_relation D Sc cutoff σ j (t ++ [i])
  change rightContext D Sc cutoff σ ((j :: t) ++ [i]) ((j :: t) ++ [i])
    (relation D Sc cutoff j (t ++ [i])) = relation D Sc cutoff j ((t ++ [i]) ++ σ) at hr
  rw [hr, Category.assoc] at hz
  exact hz

/-- The all-prefix identity (K), including arbitrary right contexts. The bare
crossing prefix is the existing `lastToFirstHom`. The target retains arbitrary
full ELV old morphisms, and the polynomial includes coefficient parity. -/
theorem allPrefix_relation_context (i : I) (μ σ z : List I)
    (h : hom D Sc cutoff (((i :: μ) ++ [i]) ++ σ) z) :
    projection D Sc cutoff i ((μ ++ [i]) ++ σ) z
      (rightContext D Sc cutoff σ (i :: (μ ++ [i])) ((i :: μ) ++ [i])
        (move D Sc cutoff i (μ ++ [i]) ≫
          rightContext D Sc cutoff [i] (μ ++ [i]) (i :: μ)
            ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
              lastToFirstHom D Sc i μ)) ≫
        relation D Sc cutoff i ((μ ++ [i]) ++ σ) ≫ h) = 0 := by
  apply projection_prefix_relation_context
  simp only [wordSumParity, List.map_append, List.sum_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  exact add_comm _ _

end OddMath.QuiverHecke.ELVOld
