/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVSourceRows
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Basic

/-! # Polynomial common-source rows

Finite-row coordinates for the prepend endpoint of the ELV deformed square
resolution. Exponents are split into central blocks and residues. All old
columns are retained, including zero corners and the empty content.
-/

noncomputable section
open CategoryTheory
open scoped Classical DirectSum
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Finite polynomial-row labels: a common tail and an exponent residue. -/
abbrev SourcePolynomialIndex (ν : List I) (d : ℕ) := SourceTailIndex ν × Fin d

/-- Coefficients of the finite polynomial rows, before bundling their shift action. -/
abbrev SourcePolynomialCoefficients (ν : List I) (d : ℕ) :=
  ⨁ q : SourcePolynomialIndex ν d × ℕ, OldContentRow D Sc cutoff ν q.1.1.1.val

/-- Regroup the coefficient carrier as a finite family of genuine row polynomials
`ℕ →₀ OldContentRow`. This is the coefficient form of the finite row decomposition. -/
def sourcePolynomialCoefficientEquiv (ν : List I) (d : ℕ) :
    SourcePolynomialCoefficients D Sc cutoff ν d ≃ₗ[(ContentRing D Sc cutoff ν)ᵐᵒᵖ]
      (∀ q : SourcePolynomialIndex ν d, ℕ →₀ OldContentRow D Sc cutoff ν q.1.1.val) :=
  (DirectSum.lequivCongrLeft (ContentRing D Sc cutoff ν)ᵐᵒᵖ
    (Equiv.sigmaEquivProd (SourcePolynomialIndex ν d) ℕ).symm).trans
    ((DirectSum.sigmaLcurryEquiv (ContentRing D Sc cutoff ν)ᵐᵒᵖ
      (δ := fun (q : SourcePolynomialIndex ν d) (_ : ℕ) =>
        OldContentRow D Sc cutoff ν q.1.1.val)).trans
      ((DirectSum.linearEquivFunOnFintype (ContentRing D Sc cutoff ν)ᵐᵒᵖ _ _).trans
        (LinearEquiv.piCongrRight fun q : SourcePolynomialIndex ν d =>
          (finsuppLequivDFinsupp (ContentRing D Sc cutoff ν)ᵐᵒᵖ
            (M := OldContentRow D Sc cutoff ν q.1.1.val)).symm)))

/-- Euclidean division of a moving exponent. -/
def sourceExponentSplit (d : ℕ) (hd : 0 < d) : ℕ ≃ Fin d × ℕ where
  toFun m := (⟨m % d, Nat.mod_lt m hd⟩, m / d)
  invFun q := d * q.2 + q.1.val
  left_inv m := by
    exact Nat.div_add_mod m d
  right_inv q := by
    apply Prod.ext
    · apply Fin.ext
      simp [Nat.add_mod, Nat.mod_eq_of_lt q.1.isLt]
    · change (d * q.2 + q.1.val) / d = q.2
      rw [Nat.mul_add_div hd, Nat.div_eq_of_lt q.1.isLt, Nat.add_zero]

/-- Split `m = d * q + δ`, preserving the entire old row. -/
def sourceRowsSplit (ν : List I) (d : ℕ) (hd : 0 < d) :
    SourceRows D Sc cutoff ν →ₗ[(ContentRing D Sc cutoff ν)ᵐᵒᵖ]
      SourcePolynomialCoefficients D Sc cutoff ν d :=
  DirectSum.toModule _ _ _ fun q =>
    DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _
      (fun r => OldContentRow D Sc cutoff ν r.1.1.1.val) ((q.1, (sourceExponentSplit d hd q.2).1),
      (sourceExponentSplit d hd q.2).2)

/-- Reassemble an exponent from its block and residue. -/
def sourceRowsJoin (ν : List I) (d : ℕ) :
    SourcePolynomialCoefficients D Sc cutoff ν d →ₗ[(ContentRing D Sc cutoff ν)ᵐᵒᵖ]
      SourceRows D Sc cutoff ν :=
  DirectSum.toModule _ _ _ fun q =>
    DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _
      (fun r => OldContentRow D Sc cutoff ν r.1.1.val) (q.1.1, d * q.2 + q.1.2.val)

@[simp] theorem sourceRowsJoin_split (ν : List I) (d : ℕ) (hd : 0 < d)
    (z : SourceRows D Sc cutoff ν) :
    sourceRowsJoin D Sc cutoff ν d (sourceRowsSplit D Sc cutoff ν d hd z) = z := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | of q b =>
    change sourceRowsJoin D Sc cutoff ν d
      (sourceRowsSplit D Sc cutoff ν d hd (DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _ _ q b)) = _
    simp only [sourceRowsJoin, sourceRowsSplit, DirectSum.toModule_lof]
    have h := (sourceExponentSplit d hd).left_inv q.2
    change d * (q.2 / d) + q.2 % d = q.2 at h
    change (DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _
      (fun r => OldContentRow D Sc cutoff ν r.1.1.val) (q.1, d * (q.2 / d) + q.2 % d)) b = _
    rw [h]
    rfl

@[simp] theorem sourceRowsSplit_join (ν : List I) (d : ℕ) (hd : 0 < d)
    (z : SourcePolynomialCoefficients D Sc cutoff ν d) :
    sourceRowsSplit D Sc cutoff ν d hd (sourceRowsJoin D Sc cutoff ν d z) = z := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | of q b =>
    change sourceRowsSplit D Sc cutoff ν d hd
      (sourceRowsJoin D Sc cutoff ν d (DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _ _ q b)) = _
    simp only [sourceRowsJoin, sourceRowsSplit, DirectSum.toModule_lof]
    have h := (sourceExponentSplit d hd).right_inv (q.1.2, q.2)
    change sourceExponentSplit d hd (d * q.2 + q.1.2.val) = (q.1.2, q.2) at h
    rw [h]
    rfl

/-- Explicit coefficient-coordinate equivalence, with no assumption on old corners. -/
def sourceRowsSplitEquiv (ν : List I) (d : ℕ) (hd : 0 < d) :
    SourceRows D Sc cutoff ν ≃ₗ[(ContentRing D Sc cutoff ν)ᵐᵒᵖ]
      SourcePolynomialCoefficients D Sc cutoff ν d where
  __ := sourceRowsSplit D Sc cutoff ν d hd
  invFun := sourceRowsJoin D Sc cutoff ν d
  left_inv := sourceRowsJoin_split D Sc cutoff ν d hd
  right_inv := sourceRowsSplit_join D Sc cutoff ν d hd

open OddMath.FiniteHomMatrix

/-- Insert an old representable row in its target row of the old matrix ring. -/
def oldRowInsert (ν : List I) (t : ContentWords ν)
    (z : OldContentRow D Sc cutoff ν t.val) : ContentRing D Sc cutoff ν :=
  ∑ v : ContentWords ν, single t v (z v)

@[simp] theorem oldRowInsert_zero (ν : List I) (t : ContentWords ν) :
    oldRowInsert D Sc cutoff ν t 0 = 0 := by simp [oldRowInsert]

@[simp] theorem oldRowInsert_add (ν : List I) (t : ContentWords ν)
    (z w : OldContentRow D Sc cutoff ν t.val) :
    oldRowInsert D Sc cutoff ν t (z + w) =
      oldRowInsert D Sc cutoff ν t z + oldRowInsert D Sc cutoff ν t w := by
  simp [oldRowInsert, Finset.sum_add_distrib]

@[simp] theorem oldRowInsert_single (ν : List I) (t v : ContentWords ν)
    (z : Old D Sc cutoff v.val t.val) :
    oldRowInsert D Sc cutoff ν t (Pi.single v z) = single t v z := by
  unfold oldRowInsert
  rw [Finset.sum_eq_single v]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp

private theorem oldRowInsert_singleVec (ν : List I) (t v : ContentWords ν)
    (z : Old D Sc cutoff v.val t.val) :
    oldRowInsert D Sc cutoff ν t
      (RightModule.singleVec (contentObject D Sc cutoff ν) (oldRowPresheaf D Sc cutoff t.val) v z) =
      single t v z := by
  unfold oldRowInsert
  rw [Finset.sum_eq_single v]
  · simp
  · intro b _ hb
    simp [RightModule.singleVec_ne, hb]
  · simp

private theorem oldRow_map (ν : List I) (t i j : ContentWords ν)
    (f : contentObject D Sc cutoff ν j ⟶ contentObject D Sc cutoff ν i)
    (z : Old D Sc cutoff i.val t.val) :
    (oldRowPresheaf D Sc cutoff t.val).map f.op z = oldComp D Sc cutoff j.val i.val t.val f z := rfl

/-- The row insertion respects the full noncommutative right action. -/
theorem oldRowInsert_smul (ν : List I) (t : ContentWords ν)
    (a : (ContentRing D Sc cutoff ν)ᵐᵒᵖ) (z : OldContentRow D Sc cutoff ν t.val) :
    oldRowInsert D Sc cutoff ν t (a • z) = oldRowInsert D Sc cutoff ν t z * a.unop := by
  obtain ⟨a⟩ := a
  change oldRowInsert D Sc cutoff ν t (MulOpposite.op a • z) =
    oldRowInsert D Sc cutoff ν t z * a
  induction a using OddMath.FiniteHomMatrix.induction with
  | hz => simp
  | ha a b ha hb => simp only [MulOpposite.op_add, add_smul, oldRowInsert_add, mul_add, ha, hb]
  | hs i j f =>
    change oldRowInsert D Sc cutoff ν t (RightModule.act _ _ (single i j f) z) = _
    rw [RightModule.act_single]
    have hm := oldRow_map D Sc cutoff ν t i j f (z i)
    change (oldRowPresheaf D Sc cutoff t.val).map f.op (z i) = _ at hm
    rw [hm]
    rw [oldRowInsert_singleVec, oldRowInsert, Finset.sum_mul, Finset.sum_eq_single i]
    · exact (single_mul_single t i j (z i) f).symm
    · intro b _ hb
      exact single_mul_single_of_ne t b i j hb _ _
    · intro h
      exact (h (Finset.mem_univ i)).elim

/-- Inclusion in the rank-one free right old module. -/
def oldRowSection (ν : List I) (t : ContentWords ν) :
    OldContentRow D Sc cutoff ν t.val →ₗ[(ContentRing D Sc cutoff ν)ᵐᵒᵖ]
      (ContentRing D Sc cutoff ν)ᵐᵒᵖ where
  toFun z := MulOpposite.op (oldRowInsert D Sc cutoff ν t z)
  map_add' z w := by simp
  map_smul' a z := by
    change MulOpposite.op (oldRowInsert D Sc cutoff ν t (a • z)) =
      MulOpposite.op (oldRowInsert D Sc cutoff ν t z * a.unop)
    rw [oldRowInsert_smul]

/-- The identity in the representable old row. -/
def oldRowUnit (ν : List I) (t : ContentWords ν) : OldContentRow D Sc cutoff ν t.val :=
  Pi.single t (𝟙 (contentObject D Sc cutoff ν t))

/-- Retraction from the rank-one free right old module. -/
def oldRowRetraction (ν : List I) (t : ContentWords ν) :
    (ContentRing D Sc cutoff ν)ᵐᵒᵖ →ₗ[(ContentRing D Sc cutoff ν)ᵐᵒᵖ]
      OldContentRow D Sc cutoff ν t.val :=
  LinearMap.toSpanSingleton _ _ (oldRowUnit D Sc cutoff ν t)

@[simp] theorem oldRowRetraction_section (ν : List I) (t : ContentWords ν)
    (z : OldContentRow D Sc cutoff ν t.val) :
    oldRowRetraction D Sc cutoff ν t (oldRowSection D Sc cutoff ν t z) = z := by
  change MulOpposite.op (∑ v : ContentWords ν, single (obj := contentObject D Sc cutoff ν) t v (z v)) •
    oldRowUnit D Sc cutoff ν t = z
  rw [Finset.op_sum, Finset.sum_smul]
  funext v
  simp only [RightModule.sum_apply]
  change (∑ w : ContentWords ν,
    RightModule.act _ _ (single t w (z w)) (oldRowUnit D Sc cutoff ν t) v) = z v
  simp only [RightModule.act_single]
  rw [Finset.sum_eq_single v]
  · rw [RightModule.singleVec_same, oldRow_map]
    change oldComp D Sc cutoff v.val t.val t.val (z v)
      ((oldRowUnit D Sc cutoff ν t) t) = z v
    have hu : (oldRowUnit D Sc cutoff ν t) t = 𝟙 (contentObject D Sc cutoff ν t) := by
      simp [oldRowUnit]
    rw [hu]
    exact Category.comp_id (X := contentObject D Sc cutoff ν v)
      (Y := contentObject D Sc cutoff ν t) (z v)
  · intro w _ hw
    exact RightModule.singleVec_ne _ _ w v (Ne.symm hw) _
  · simp

instance oldContentRow_projective (ν : List I) (t : ContentWords ν) :
    Module.Projective (ContentRing D Sc cutoff ν)ᵐᵒᵖ (OldContentRow D Sc cutoff ν t.val) :=
  Module.Projective.of_split (oldRowSection D Sc cutoff ν t)
    (oldRowRetraction D Sc cutoff ν t) (by
      ext z
      exact oldRowRetraction_section D Sc cutoff ν t z)

instance oldContentRow_finite (ν : List I) (t : ContentWords ν) :
    Module.Finite (ContentRing D Sc cutoff ν)ᵐᵒᵖ (OldContentRow D Sc cutoff ν t.val) :=
  Module.Finite.of_surjective (oldRowRetraction D Sc cutoff ν t)
    (Function.LeftInverse.surjective (oldRowRetraction_section D Sc cutoff ν t))

open CyclotomicAction MulOpposite

/-- The source rows with the central polynomial variable acting by `d` exponent steps. -/
abbrev SourceRowsPolynomial (ν : List I) (d : ℕ) :=
  RightCentralPolynomialModule (sourceRowsShift D Sc cutoff ν d)

/-- One coefficient shift in the finite polynomial-row coordinates. -/
def sourcePolynomialShift (ν : List I) (d : ℕ) :
    SourcePolynomialCoefficients D Sc cutoff ν d →ₗ[(ContentRing D Sc cutoff ν)ᵐᵒᵖ]
      SourcePolynomialCoefficients D Sc cutoff ν d :=
  DirectSum.toModule _ _ _ fun q =>
    DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _
      (fun r => OldContentRow D Sc cutoff ν r.1.1.1.val) (q.1, q.2 + 1)

/-- Finite old-idempotent polynomial rows, encoded by their finitely supported coefficients. -/
abbrev PolynomialOldRows (ν : List I) (d : ℕ) :=
  RightCentralPolynomialModule (sourcePolynomialShift D Sc cutoff ν d)

theorem sourceRowsJoin_shift (ν : List I) (d : ℕ)
    (z : SourcePolynomialCoefficients D Sc cutoff ν d) :
    sourceRowsJoin D Sc cutoff ν d (sourcePolynomialShift D Sc cutoff ν d z) =
      sourceRowsShift D Sc cutoff ν d (sourceRowsJoin D Sc cutoff ν d z) := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | of q b =>
    change sourceRowsJoin D Sc cutoff ν d
      (sourcePolynomialShift D Sc cutoff ν d (DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _ _ q b)) =
      sourceRowsShift D Sc cutoff ν d
        (sourceRowsJoin D Sc cutoff ν d (DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _ _ q b))
    simp only [sourcePolynomialShift, sourceRowsJoin, sourceRowsShift, DirectSum.toModule_lof]
    have h : d * (q.2 + 1) + q.1.2.val = d + (d * q.2 + q.1.2.val) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    rw [h]

/-- Polynomial-linearity of reassembly, not just ground-ring linearity. -/
def sourceRowsPolynomialJoin (ν : List I) (d : ℕ) :
    PolynomialOldRows D Sc cutoff ν d →ₗ[(Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ]
      SourceRowsPolynomial D Sc cutoff ν d :=
  RightCentralPolynomialModule.map _ _ (sourceRowsJoin D Sc cutoff ν d)
    (sourceRowsJoin_shift D Sc cutoff ν d)

/-- Explicit finite polynomial-row decomposition for every positive central step. -/
def sourceRowsPolynomialEquiv (ν : List I) (d : ℕ) (hd : 0 < d) :
    SourceRowsPolynomial D Sc cutoff ν d ≃ₗ[(Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ]
      PolynomialOldRows D Sc cutoff ν d :=
  (LinearEquiv.ofBijective (sourceRowsPolynomialJoin D Sc cutoff ν d) (by
    constructor
    · exact (sourceRowsSplitEquiv D Sc cutoff ν d hd).symm.injective
    · exact (sourceRowsSplitEquiv D Sc cutoff ν d hd).symm.surjective)).symm

private def polynomialLinearMap {R M N : Type*} [Ring R] [AddCommGroup M] [AddCommGroup N]
    [Module (Polynomial R)ᵐᵒᵖ M] [Module (Polynomial R)ᵐᵒᵖ N]
    (f : M →+ N)
    (hc : ∀ (r : R) (m : M), f (op (Polynomial.C r) • m) = op (Polynomial.C r) • f m)
    (hx : ∀ m, f (op (Polynomial.X : Polynomial R) • m) = (op Polynomial.X : (Polynomial R)ᵐᵒᵖ) • f m) :
    M →ₗ[(Polynomial R)ᵐᵒᵖ] N where
  __ := f
  map_smul' p m := by
    obtain ⟨p⟩ := p
    change f (op p • m) = op p • f m
    induction p using Polynomial.induction_on generalizing m with
    | C r => exact hc r m
    | add p q hp hq =>
      rw [MulOpposite.op_add, add_smul, f.map_add, hp, hq, add_smul]
    | monomial n r ih =>
      rw [pow_succ, ← mul_assoc, op_mul, mul_smul, hx, ih, mul_smul]

/-- The finite free ambient right polynomial module. -/
abbrev SourcePolynomialFree (ν : List I) (d : ℕ) :=
  SourcePolynomialIndex ν d → (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ

/-- Coefficientwise insertion of the old rows into polynomial matrices. -/
def polynomialRowsSectionAdd (ν : List I) (d : ℕ) :
    SourcePolynomialCoefficients D Sc cutoff ν d →+ SourcePolynomialFree D Sc cutoff ν d :=
  DirectSum.toAddMonoid fun q =>
    { toFun := fun z => Pi.single q.1 (op (Polynomial.monomial q.2
        (oldRowInsert D Sc cutoff ν q.1.1.1 z)))
      map_zero' := by simp
      map_add' := by intros; simp [Pi.single_add] }

@[simp] theorem polynomialRowsSectionAdd_of (ν : List I) (d : ℕ)
    (q : SourcePolynomialIndex ν d × ℕ) (z : OldContentRow D Sc cutoff ν q.1.1.1.val) :
    polynomialRowsSectionAdd D Sc cutoff ν d (DirectSum.of _ q z) =
      Pi.single q.1 (op (Polynomial.monomial q.2 (oldRowInsert D Sc cutoff ν q.1.1.1 z))) :=
  DirectSum.toAddMonoid_of _ _ _

private theorem polynomialRowsSectionAdd_C (ν : List I) (d : ℕ)
    (a : ContentRing D Sc cutoff ν) (z : SourcePolynomialCoefficients D Sc cutoff ν d) :
    polynomialRowsSectionAdd D Sc cutoff ν d (op a • z) =
      op (Polynomial.C a) • polynomialRowsSectionAdd D Sc cutoff ν d z := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | of q b =>
    change polynomialRowsSectionAdd D Sc cutoff ν d
      (op a • DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _ _ q b) = _
    rw [← map_smul]
    change polynomialRowsSectionAdd D Sc cutoff ν d (DirectSum.of _ q (op a • b)) = _
    rw [polynomialRowsSectionAdd_of, polynomialRowsSectionAdd_of, oldRowInsert_smul]
    rw [← Pi.single_smul]
    congr 1
    change op (Polynomial.monomial q.2 (oldRowInsert D Sc cutoff ν q.1.1.1 b * a)) =
      op (Polynomial.monomial q.2 (oldRowInsert D Sc cutoff ν q.1.1.1 b) * Polynomial.C a)
    rw [Polynomial.monomial_mul_C]

private theorem polynomialRowsSectionAdd_X (ν : List I) (d : ℕ)
    (z : SourcePolynomialCoefficients D Sc cutoff ν d) :
    polynomialRowsSectionAdd D Sc cutoff ν d (sourcePolynomialShift D Sc cutoff ν d z) =
      op (Polynomial.X : Polynomial (ContentRing D Sc cutoff ν)) •
        polynomialRowsSectionAdd D Sc cutoff ν d z := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | of q b =>
    change polynomialRowsSectionAdd D Sc cutoff ν d
      (sourcePolynomialShift D Sc cutoff ν d
        (DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _ _ q b)) = _
    rw [sourcePolynomialShift, DirectSum.toModule_lof]
    change polynomialRowsSectionAdd D Sc cutoff ν d (DirectSum.of _ (q.1, q.2 + 1) b) = _
    rw [polynomialRowsSectionAdd_of, polynomialRowsSectionAdd_of, ← Pi.single_smul]
    congr 1
    change op (Polynomial.monomial (q.2 + 1) (oldRowInsert D Sc cutoff ν q.1.1.1 b)) =
      op (Polynomial.monomial q.2 (oldRowInsert D Sc cutoff ν q.1.1.1 b) * Polynomial.X)
    rw [Polynomial.monomial_mul_X]

/-- Polynomial-linear section into a finite free module, with explicit coefficient formula. -/
def polynomialRowsSection (ν : List I) (d : ℕ) :
    PolynomialOldRows D Sc cutoff ν d →ₗ[(Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ]
      SourcePolynomialFree D Sc cutoff ν d :=
  polynomialLinearMap
    ((polynomialRowsSectionAdd D Sc cutoff ν d).comp
      (RightCentralPolynomialModule.of (sourcePolynomialShift D Sc cutoff ν d)).symm.toAddMonoidHom)
    (by
      intro a z
      obtain ⟨z, rfl⟩ := (RightCentralPolynomialModule.of _).surjective z
      rw [RightCentralPolynomialModule.C_smul_of]
      exact polynomialRowsSectionAdd_C D Sc cutoff ν d a z)
    (by
      intro z
      obtain ⟨z, rfl⟩ := (RightCentralPolynomialModule.of _).surjective z
      rw [RightCentralPolynomialModule.X_smul_of]
      exact polynomialRowsSectionAdd_X D Sc cutoff ν d z)

/-- Retraction from the finite free module, evaluated on the old identity rows. -/
def polynomialRowsRetraction (ν : List I) (d : ℕ) :
    SourcePolynomialFree D Sc cutoff ν d →ₗ[(Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ]
      PolynomialOldRows D Sc cutoff ν d :=
  ∑ q : SourcePolynomialIndex ν d,
    (LinearMap.toSpanSingleton _ _
      (RightCentralPolynomialModule.of (sourcePolynomialShift D Sc cutoff ν d)
        (DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _ _ (q, 0)
          (oldRowUnit D Sc cutoff ν q.1.1)))).comp (LinearMap.proj q)

@[simp] theorem polynomialRowsSection_of (ν : List I) (d : ℕ)
    (q : SourcePolynomialIndex ν d × ℕ) (z : OldContentRow D Sc cutoff ν q.1.1.1.val) :
    polynomialRowsSection D Sc cutoff ν d
      (RightCentralPolynomialModule.of _ (DirectSum.of _ q z)) =
      Pi.single q.1 (op (Polynomial.monomial q.2 (oldRowInsert D Sc cutoff ν q.1.1.1 z))) :=
  polynomialRowsSectionAdd_of D Sc cutoff ν d q z

@[simp] theorem polynomialRowsRetraction_single (ν : List I) (d : ℕ)
    (q : SourcePolynomialIndex ν d) (p : (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ) :
    polynomialRowsRetraction D Sc cutoff ν d (Pi.single q p) =
      p • RightCentralPolynomialModule.of (sourcePolynomialShift D Sc cutoff ν d)
        (DirectSum.of _ (q, 0) (oldRowUnit D Sc cutoff ν q.1.1)) := by
  simp only [polynomialRowsRetraction, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, LinearMap.toSpanSingleton_apply]
  rw [Finset.sum_eq_single q]
  · rw [Pi.single_eq_same]
    rfl
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, zero_smul]
  · intro h
    exact (h (Finset.mem_univ q)).elim

private theorem polynomialRows_X_pow (ν : List I) (d : ℕ)
    (q : SourcePolynomialIndex ν d) (b : OldContentRow D Sc cutoff ν q.1.1.val)
    (n m : ℕ) :
    (op (Polynomial.X : Polynomial (ContentRing D Sc cutoff ν))) ^ n •
      RightCentralPolynomialModule.of (sourcePolynomialShift D Sc cutoff ν d)
        (DirectSum.of _ (q, m) b) =
      RightCentralPolynomialModule.of (sourcePolynomialShift D Sc cutoff ν d)
        (DirectSum.of _ (q, n + m) b) := by
  induction n with
  | zero => rw [pow_zero, one_smul, Nat.zero_add]
  | succ n ih =>
    rw [pow_succ', mul_smul, ih, RightCentralPolynomialModule.X_smul_of]
    change RightCentralPolynomialModule.of _
      (sourcePolynomialShift D Sc cutoff ν d
        (DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _ _ (q, n + m) b)) = _
    rw [sourcePolynomialShift, DirectSum.toModule_lof]
    have h : n + m + 1 = n + 1 + m := by omega
    rw [h]
    rfl

private theorem polynomialRows_monomial (ν : List I) (d : ℕ)
    (q : SourcePolynomialIndex ν d) (b : OldContentRow D Sc cutoff ν q.1.1.val)
    (n : ℕ) (a : ContentRing D Sc cutoff ν) :
    op (Polynomial.monomial n a) •
      RightCentralPolynomialModule.of (sourcePolynomialShift D Sc cutoff ν d)
        (DirectSum.of _ (q, 0) b) =
      RightCentralPolynomialModule.of (sourcePolynomialShift D Sc cutoff ν d)
        (DirectSum.of _ (q, n) (op a • b)) := by
  have he : op (Polynomial.monomial n a) =
      (op (Polynomial.X : Polynomial (ContentRing D Sc cutoff ν))) ^ n * op (Polynomial.C a) := by
    rw [← Polynomial.C_mul_X_pow_eq_monomial, op_mul, op_pow]
  rw [he, mul_smul]
  rw [RightCentralPolynomialModule.C_smul_of]
  rw [← DirectSum.of_smul]
  exact polynomialRows_X_pow D Sc cutoff ν d q (op a • b) n 0

/-- The polynomial insertion and retraction split, including zero idempotent rows. -/
@[simp] theorem polynomialRowsRetraction_section (ν : List I) (d : ℕ)
    (z : PolynomialOldRows D Sc cutoff ν d) :
    polynomialRowsRetraction D Sc cutoff ν d (polynomialRowsSection D Sc cutoff ν d z) = z := by
  obtain ⟨z, rfl⟩ := (RightCentralPolynomialModule.of _).surjective z
  induction z using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | of q b =>
    rw [polynomialRowsSection_of, polynomialRowsRetraction_single, polynomialRows_monomial]
    have h : op (oldRowInsert D Sc cutoff ν q.1.1.1 b) •
        oldRowUnit D Sc cutoff ν q.1.1.1 = b := oldRowRetraction_section D Sc cutoff ν q.1.1.1 b
    rw [h]

instance polynomialOldRows_projective (ν : List I) (d : ℕ) :
    Module.Projective (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ (PolynomialOldRows D Sc cutoff ν d) :=
  Module.Projective.of_split (polynomialRowsSection D Sc cutoff ν d)
    (polynomialRowsRetraction D Sc cutoff ν d) (by
      ext z
      exact polynomialRowsRetraction_section D Sc cutoff ν d z)

instance polynomialOldRows_finite (ν : List I) (d : ℕ) :
    Module.Finite (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ (PolynomialOldRows D Sc cutoff ν d) :=
  Module.Finite.of_surjective (polynomialRowsRetraction D Sc cutoff ν d)
    (Function.LeftInverse.surjective (polynomialRowsRetraction_section D Sc cutoff ν d))

/-- Concrete finite-free section for the original exponent-shift module. -/
def sourceRowsPolynomialSection (ν : List I) (d : ℕ) (hd : 0 < d) :
    SourceRowsPolynomial D Sc cutoff ν d →ₗ[(Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ]
      SourcePolynomialFree D Sc cutoff ν d :=
  (polynomialRowsSection D Sc cutoff ν d).comp
    (sourceRowsPolynomialEquiv D Sc cutoff ν d hd).toLinearMap

/-- Concrete finite-free retraction for the original exponent-shift module. -/
def sourceRowsPolynomialRetraction (ν : List I) (d : ℕ) :
    SourcePolynomialFree D Sc cutoff ν d →ₗ[(Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ]
      SourceRowsPolynomial D Sc cutoff ν d :=
  (sourceRowsPolynomialJoin D Sc cutoff ν d).comp (polynomialRowsRetraction D Sc cutoff ν d)

@[simp] theorem sourceRowsPolynomialRetraction_section (ν : List I) (d : ℕ) (hd : 0 < d)
    (z : SourceRowsPolynomial D Sc cutoff ν d) :
    sourceRowsPolynomialRetraction D Sc cutoff ν d
      (sourceRowsPolynomialSection D Sc cutoff ν d hd z) = z := by
  simp only [sourceRowsPolynomialRetraction, sourceRowsPolynomialSection,
    LinearMap.comp_apply, polynomialRowsRetraction_section, LinearEquiv.coe_coe]
  exact (sourceRowsPolynomialEquiv D Sc cutoff ν d hd).symm_apply_apply z

/-- Finite projectivity uses only positivity of the central step, not nonzero old corners. -/
theorem sourceRowsPolynomial_projective (ν : List I) (d : ℕ) (hd : 0 < d) :
    Module.Projective (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ
      (SourceRowsPolynomial D Sc cutoff ν d) :=
  Module.Projective.of_equiv' (sourceRowsPolynomialEquiv D Sc cutoff ν d hd).symm

theorem sourceRowsPolynomial_finite (ν : List I) (d : ℕ) (hd : 0 < d) :
    Module.Finite (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ
      (SourceRowsPolynomial D Sc cutoff ν d) :=
  Module.Finite.of_surjective (sourceRowsPolynomialRetraction D Sc cutoff ν d)
    (Function.LeftInverse.surjective (sourceRowsPolynomialRetraction_section D Sc cutoff ν d hd))

@[simp] theorem sourceRowsPolynomialEquiv_symm_of (ν : List I) (d : ℕ) (hd : 0 < d)
    (z : SourcePolynomialCoefficients D Sc cutoff ν d) :
    (sourceRowsPolynomialEquiv D Sc cutoff ν d hd).symm
      (RightCentralPolynomialModule.of _ z) =
      RightCentralPolynomialModule.of _ (sourceRowsJoin D Sc cutoff ν d z) := rfl

@[simp] theorem sourceRowsPolynomialEquiv_of (ν : List I) (d : ℕ) (hd : 0 < d)
    (z : SourceRows D Sc cutoff ν) :
    sourceRowsPolynomialEquiv D Sc cutoff ν d hd (RightCentralPolynomialModule.of _ z) =
      RightCentralPolynomialModule.of _ (sourceRowsSplit D Sc cutoff ν d hd z) := by
  apply (sourceRowsPolynomialEquiv D Sc cutoff ν d hd).symm.injective
  rw [LinearEquiv.symm_apply_apply, sourceRowsPolynomialEquiv_symm_of, sourceRowsJoin_split]

instance sourceRowsPolynomial_projective_inst (ν : List I) (d : ℕ) [NeZero d] :
    Module.Projective (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ
      (SourceRowsPolynomial D Sc cutoff ν d) :=
  sourceRowsPolynomial_projective D Sc cutoff ν d (Nat.pos_of_ne_zero (NeZero.ne d))

instance sourceRowsPolynomial_finite_inst (ν : List I) (d : ℕ) [NeZero d] :
    Module.Finite (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ
      (SourceRowsPolynomial D Sc cutoff ν d) :=
  sourceRowsPolynomial_finite D Sc cutoff ν d (Nat.pos_of_ne_zero (NeZero.ne d))

end OddMath.QuiverHecke.ELVOld
