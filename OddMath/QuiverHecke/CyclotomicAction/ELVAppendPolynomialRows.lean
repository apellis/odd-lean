/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendRows
import OddMath.QuiverHecke.CyclotomicAction.ELVPolynomialIdempotents

/-! # Polynomial common-append rows

Finite polynomial coordinates for the append endpoint of the ELV deformed
square resolution. Moving exponents split into central blocks and residues;
the coefficient of each block is the entire representable old row.
-/

noncomputable section
open CategoryTheory
open scoped Classical DirectSum
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Finite polynomial-row labels: a common tail and an exponent residue. -/
abbrev AppendPolynomialIndex (i : I) (ν : List I) (d : ℕ) := AppendTailIndex i ν × Fin d

/-- Coefficients of the finite polynomial rows, before bundling their shift action. -/
abbrev AppendPolynomialCoefficients (i : I) (ν : List I) (d : ℕ) :=
  ⨁ q : AppendPolynomialIndex i ν d × ℕ, OldContentRow D Sc cutoff ν q.1.1.1.val

/-- Regroup the coefficient carrier as a finite family of genuine row polynomials
`ℕ →₀ OldContentRow`. This is the coefficient form of the finite row decomposition. -/
def appendPolynomialCoefficientEquiv (i : I) (ν : List I) (d : ℕ) :
    AppendPolynomialCoefficients D Sc cutoff i ν d ≃ₗ[(ContentRing D Sc cutoff ν)ᵐᵒᵖ]
      (∀ q : AppendPolynomialIndex i ν d, ℕ →₀ OldContentRow D Sc cutoff ν q.1.1.val) :=
  (DirectSum.lequivCongrLeft (ContentRing D Sc cutoff ν)ᵐᵒᵖ
    (Equiv.sigmaEquivProd (AppendPolynomialIndex i ν d) ℕ).symm).trans
    ((DirectSum.sigmaLcurryEquiv (ContentRing D Sc cutoff ν)ᵐᵒᵖ
      (δ := fun (q : AppendPolynomialIndex i ν d) (_ : ℕ) =>
        OldContentRow D Sc cutoff ν q.1.1.val)).trans
      ((DirectSum.linearEquivFunOnFintype (ContentRing D Sc cutoff ν)ᵐᵒᵖ _ _).trans
        (LinearEquiv.piCongrRight fun q : AppendPolynomialIndex i ν d =>
          (finsuppLequivDFinsupp (ContentRing D Sc cutoff ν)ᵐᵒᵖ
            (M := OldContentRow D Sc cutoff ν q.1.1.val)).symm)))

/-- Split `m = d * q + δ`, preserving the entire old row. -/
def appendRowsSplit (i : I) (ν : List I) (d : ℕ) (hd : 0 < d) :
    AppendRows D Sc cutoff i ν →ₗ[(ContentRing D Sc cutoff ν)ᵐᵒᵖ]
      AppendPolynomialCoefficients D Sc cutoff i ν d :=
  DirectSum.toModule _ _ _ fun q =>
    DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _
      (fun r => OldContentRow D Sc cutoff ν r.1.1.1.val) ((q.1, (sourceExponentSplit d hd q.2).1),
      (sourceExponentSplit d hd q.2).2)

/-- Reassemble an exponent from its block and residue. -/
def appendRowsJoin (i : I) (ν : List I) (d : ℕ) :
    AppendPolynomialCoefficients D Sc cutoff i ν d →ₗ[(ContentRing D Sc cutoff ν)ᵐᵒᵖ]
      AppendRows D Sc cutoff i ν :=
  DirectSum.toModule _ _ _ fun q =>
    DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _
      (fun r => OldContentRow D Sc cutoff ν r.1.1.val) (q.1.1, d * q.2 + q.1.2.val)

@[simp] theorem appendRowsJoin_split (i : I) (ν : List I) (d : ℕ) (hd : 0 < d)
    (z : AppendRows D Sc cutoff i ν) :
    appendRowsJoin D Sc cutoff i ν d (appendRowsSplit D Sc cutoff i ν d hd z) = z := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | of q b =>
    change appendRowsJoin D Sc cutoff i ν d
      (appendRowsSplit D Sc cutoff i ν d hd (DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _ _ q b)) = _
    simp only [appendRowsJoin, appendRowsSplit, DirectSum.toModule_lof]
    have h := (sourceExponentSplit d hd).left_inv q.2
    change d * (q.2 / d) + q.2 % d = q.2 at h
    change (DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _
      (fun r => OldContentRow D Sc cutoff ν r.1.1.val) (q.1, d * (q.2 / d) + q.2 % d)) b = _
    rw [h]
    rfl

@[simp] theorem appendRowsSplit_join (i : I) (ν : List I) (d : ℕ) (hd : 0 < d)
    (z : AppendPolynomialCoefficients D Sc cutoff i ν d) :
    appendRowsSplit D Sc cutoff i ν d hd (appendRowsJoin D Sc cutoff i ν d z) = z := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | of q b =>
    change appendRowsSplit D Sc cutoff i ν d hd
      (appendRowsJoin D Sc cutoff i ν d (DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _ _ q b)) = _
    simp only [appendRowsJoin, appendRowsSplit, DirectSum.toModule_lof]
    have h := (sourceExponentSplit d hd).right_inv (q.1.2, q.2)
    change sourceExponentSplit d hd (d * q.2 + q.1.2.val) = (q.1.2, q.2) at h
    rw [h]
    rfl

/-- Explicit coefficient-coordinate equivalence, with no assumption on old corners. -/
def appendRowsSplitEquiv (i : I) (ν : List I) (d : ℕ) (hd : 0 < d) :
    AppendRows D Sc cutoff i ν ≃ₗ[(ContentRing D Sc cutoff ν)ᵐᵒᵖ]
      AppendPolynomialCoefficients D Sc cutoff i ν d where
  __ := appendRowsSplit D Sc cutoff i ν d hd
  invFun := appendRowsJoin D Sc cutoff i ν d
  left_inv := appendRowsJoin_split D Sc cutoff i ν d hd
  right_inv := appendRowsSplit_join D Sc cutoff i ν d hd

open CyclotomicAction MulOpposite

/-- The append rows with the central polynomial variable acting by `d` exponent steps. -/
abbrev AppendRowsPolynomial (i : I) (ν : List I) (d : ℕ) :=
  RightCentralPolynomialModule (appendRowsShift D Sc cutoff i ν d)

/-- One coefficient shift in the finite polynomial-row coordinates. -/
def appendPolynomialShift (i : I) (ν : List I) (d : ℕ) :
    AppendPolynomialCoefficients D Sc cutoff i ν d →ₗ[(ContentRing D Sc cutoff ν)ᵐᵒᵖ]
      AppendPolynomialCoefficients D Sc cutoff i ν d :=
  DirectSum.toModule _ _ _ fun q =>
    DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _
      (fun r => OldContentRow D Sc cutoff ν r.1.1.1.val) (q.1, q.2 + 1)

/-- Finite old-idempotent polynomial rows, encoded by their finitely supported coefficients. -/
abbrev AppendPolynomialOldRows (i : I) (ν : List I) (d : ℕ) :=
  RightCentralPolynomialModule (appendPolynomialShift D Sc cutoff i ν d)

theorem appendRowsJoin_shift (i : I) (ν : List I) (d : ℕ)
    (z : AppendPolynomialCoefficients D Sc cutoff i ν d) :
    appendRowsJoin D Sc cutoff i ν d (appendPolynomialShift D Sc cutoff i ν d z) =
      appendRowsShift D Sc cutoff i ν d (appendRowsJoin D Sc cutoff i ν d z) := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | of q b =>
    change appendRowsJoin D Sc cutoff i ν d
      (appendPolynomialShift D Sc cutoff i ν d (DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _ _ q b)) =
      appendRowsShift D Sc cutoff i ν d
        (appendRowsJoin D Sc cutoff i ν d (DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _ _ q b))
    simp only [appendPolynomialShift, appendRowsJoin, appendRowsShift, DirectSum.toModule_lof]
    have h : d * (q.2 + 1) + q.1.2.val = d + (d * q.2 + q.1.2.val) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    rw [h]

/-- Polynomial-linearity of reassembly, not just ground-ring linearity. -/
def appendRowsPolynomialJoin (i : I) (ν : List I) (d : ℕ) :
    AppendPolynomialOldRows D Sc cutoff i ν d →ₗ[(Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ]
      AppendRowsPolynomial D Sc cutoff i ν d :=
  RightCentralPolynomialModule.map _ _ (appendRowsJoin D Sc cutoff i ν d)
    (appendRowsJoin_shift D Sc cutoff i ν d)

/-- Explicit finite polynomial-row decomposition for every positive central step. -/
def appendRowsPolynomialEquiv (i : I) (ν : List I) (d : ℕ) (hd : 0 < d) :
    AppendRowsPolynomial D Sc cutoff i ν d ≃ₗ[(Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ]
      AppendPolynomialOldRows D Sc cutoff i ν d :=
  (LinearEquiv.ofBijective (appendRowsPolynomialJoin D Sc cutoff i ν d) (by
    constructor
    · exact (appendRowsSplitEquiv D Sc cutoff i ν d hd).symm.injective
    · exact (appendRowsSplitEquiv D Sc cutoff i ν d hd).symm.surjective)).symm

private def appendPolynomialLinearMap {R M N : Type*} [Ring R] [AddCommGroup M] [AddCommGroup N]
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
abbrev AppendPolynomialFree (i : I) (ν : List I) (d : ℕ) :=
  AppendPolynomialIndex i ν d → (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ

/-- Coefficientwise insertion of the old rows into polynomial matrices. -/
def appendPolynomialRowsSectionAdd (i : I) (ν : List I) (d : ℕ) :
    AppendPolynomialCoefficients D Sc cutoff i ν d →+ AppendPolynomialFree D Sc cutoff i ν d :=
  DirectSum.toAddMonoid fun q =>
    { toFun := fun z => Pi.single q.1 (op (Polynomial.monomial q.2
        (oldRowInsert D Sc cutoff ν q.1.1.1 z)))
      map_zero' := by simp
      map_add' := by intros; simp [Pi.single_add] }

@[simp] theorem appendPolynomialRowsSectionAdd_of (i : I) (ν : List I) (d : ℕ)
    (q : AppendPolynomialIndex i ν d × ℕ) (z : OldContentRow D Sc cutoff ν q.1.1.1.val) :
    appendPolynomialRowsSectionAdd D Sc cutoff i ν d (DirectSum.of _ q z) =
      Pi.single q.1 (op (Polynomial.monomial q.2 (oldRowInsert D Sc cutoff ν q.1.1.1 z))) :=
  DirectSum.toAddMonoid_of _ _ _

private theorem appendPolynomialRowsSectionAdd_C (i : I) (ν : List I) (d : ℕ)
    (a : ContentRing D Sc cutoff ν) (z : AppendPolynomialCoefficients D Sc cutoff i ν d) :
    appendPolynomialRowsSectionAdd D Sc cutoff i ν d (op a • z) =
      op (Polynomial.C a) • appendPolynomialRowsSectionAdd D Sc cutoff i ν d z := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | of q b =>
    change appendPolynomialRowsSectionAdd D Sc cutoff i ν d
      (op a • DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _ _ q b) = _
    rw [← map_smul]
    change appendPolynomialRowsSectionAdd D Sc cutoff i ν d (DirectSum.of _ q (op a • b)) = _
    rw [appendPolynomialRowsSectionAdd_of, appendPolynomialRowsSectionAdd_of, oldRowInsert_smul]
    rw [← Pi.single_smul]
    congr 1
    change op (Polynomial.monomial q.2 (oldRowInsert D Sc cutoff ν q.1.1.1 b * a)) =
      op (Polynomial.monomial q.2 (oldRowInsert D Sc cutoff ν q.1.1.1 b) * Polynomial.C a)
    rw [Polynomial.monomial_mul_C]

private theorem appendPolynomialRowsSectionAdd_X (i : I) (ν : List I) (d : ℕ)
    (z : AppendPolynomialCoefficients D Sc cutoff i ν d) :
    appendPolynomialRowsSectionAdd D Sc cutoff i ν d (appendPolynomialShift D Sc cutoff i ν d z) =
      op (Polynomial.X : Polynomial (ContentRing D Sc cutoff ν)) •
        appendPolynomialRowsSectionAdd D Sc cutoff i ν d z := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | of q b =>
    change appendPolynomialRowsSectionAdd D Sc cutoff i ν d
      (appendPolynomialShift D Sc cutoff i ν d
        (DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _ _ q b)) = _
    rw [appendPolynomialShift, DirectSum.toModule_lof]
    change appendPolynomialRowsSectionAdd D Sc cutoff i ν d (DirectSum.of _ (q.1, q.2 + 1) b) = _
    rw [appendPolynomialRowsSectionAdd_of, appendPolynomialRowsSectionAdd_of, ← Pi.single_smul]
    congr 1
    change op (Polynomial.monomial (q.2 + 1) (oldRowInsert D Sc cutoff ν q.1.1.1 b)) =
      op (Polynomial.monomial q.2 (oldRowInsert D Sc cutoff ν q.1.1.1 b) * Polynomial.X)
    rw [Polynomial.monomial_mul_X]

/-- Polynomial-linear section into a finite free module, with explicit coefficient formula. -/
def appendPolynomialRowsSection (i : I) (ν : List I) (d : ℕ) :
    AppendPolynomialOldRows D Sc cutoff i ν d →ₗ[(Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ]
      AppendPolynomialFree D Sc cutoff i ν d :=
  appendPolynomialLinearMap
    ((appendPolynomialRowsSectionAdd D Sc cutoff i ν d).comp
      (RightCentralPolynomialModule.of (appendPolynomialShift D Sc cutoff i ν d)).symm.toAddMonoidHom)
    (by
      intro a z
      obtain ⟨z, rfl⟩ := (RightCentralPolynomialModule.of _).surjective z
      rw [RightCentralPolynomialModule.C_smul_of]
      exact appendPolynomialRowsSectionAdd_C D Sc cutoff i ν d a z)
    (by
      intro z
      obtain ⟨z, rfl⟩ := (RightCentralPolynomialModule.of _).surjective z
      rw [RightCentralPolynomialModule.X_smul_of]
      exact appendPolynomialRowsSectionAdd_X D Sc cutoff i ν d z)

/-- Retraction from the finite free module, evaluated on the old identity rows. -/
def appendPolynomialRowsRetraction (i : I) (ν : List I) (d : ℕ) :
    AppendPolynomialFree D Sc cutoff i ν d →ₗ[(Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ]
      AppendPolynomialOldRows D Sc cutoff i ν d :=
  ∑ q : AppendPolynomialIndex i ν d,
    (LinearMap.toSpanSingleton _ _
      (RightCentralPolynomialModule.of (appendPolynomialShift D Sc cutoff i ν d)
        (DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _ _ (q, 0)
          (oldRowUnit D Sc cutoff ν q.1.1)))).comp (LinearMap.proj q)

@[simp] theorem appendPolynomialRowsSection_of (i : I) (ν : List I) (d : ℕ)
    (q : AppendPolynomialIndex i ν d × ℕ) (z : OldContentRow D Sc cutoff ν q.1.1.1.val) :
    appendPolynomialRowsSection D Sc cutoff i ν d
      (RightCentralPolynomialModule.of _ (DirectSum.of _ q z)) =
      Pi.single q.1 (op (Polynomial.monomial q.2 (oldRowInsert D Sc cutoff ν q.1.1.1 z))) :=
  appendPolynomialRowsSectionAdd_of D Sc cutoff i ν d q z

@[simp] theorem appendPolynomialRowsRetraction_single (i : I) (ν : List I) (d : ℕ)
    (q : AppendPolynomialIndex i ν d) (p : (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ) :
    appendPolynomialRowsRetraction D Sc cutoff i ν d (Pi.single q p) =
      p • RightCentralPolynomialModule.of (appendPolynomialShift D Sc cutoff i ν d)
        (DirectSum.of _ (q, 0) (oldRowUnit D Sc cutoff ν q.1.1)) := by
  simp only [appendPolynomialRowsRetraction, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, LinearMap.toSpanSingleton_apply]
  rw [Finset.sum_eq_single q]
  · rw [Pi.single_eq_same]
    rfl
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, zero_smul]
  · intro h
    exact (h (Finset.mem_univ q)).elim

private theorem appendPolynomialRows_X_pow (i : I) (ν : List I) (d : ℕ)
    (q : AppendPolynomialIndex i ν d) (b : OldContentRow D Sc cutoff ν q.1.1.val)
    (n m : ℕ) :
    (op (Polynomial.X : Polynomial (ContentRing D Sc cutoff ν))) ^ n •
      RightCentralPolynomialModule.of (appendPolynomialShift D Sc cutoff i ν d)
        (DirectSum.of _ (q, m) b) =
      RightCentralPolynomialModule.of (appendPolynomialShift D Sc cutoff i ν d)
        (DirectSum.of _ (q, n + m) b) := by
  induction n with
  | zero => rw [pow_zero, one_smul, Nat.zero_add]
  | succ n ih =>
    rw [pow_succ', mul_smul, ih, RightCentralPolynomialModule.X_smul_of]
    change RightCentralPolynomialModule.of _
      (appendPolynomialShift D Sc cutoff i ν d
        (DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _ _ (q, n + m) b)) = _
    rw [appendPolynomialShift, DirectSum.toModule_lof]
    have h : n + m + 1 = n + 1 + m := by omega
    rw [h]
    rfl

private theorem appendPolynomialRows_monomial (i : I) (ν : List I) (d : ℕ)
    (q : AppendPolynomialIndex i ν d) (b : OldContentRow D Sc cutoff ν q.1.1.val)
    (n : ℕ) (a : ContentRing D Sc cutoff ν) :
    op (Polynomial.monomial n a) •
      RightCentralPolynomialModule.of (appendPolynomialShift D Sc cutoff i ν d)
        (DirectSum.of _ (q, 0) b) =
      RightCentralPolynomialModule.of (appendPolynomialShift D Sc cutoff i ν d)
        (DirectSum.of _ (q, n) (op a • b)) := by
  have he : op (Polynomial.monomial n a) =
      (op (Polynomial.X : Polynomial (ContentRing D Sc cutoff ν))) ^ n * op (Polynomial.C a) := by
    rw [← Polynomial.C_mul_X_pow_eq_monomial, op_mul, op_pow]
  rw [he, mul_smul]
  rw [RightCentralPolynomialModule.C_smul_of]
  rw [← DirectSum.of_smul]
  exact appendPolynomialRows_X_pow D Sc cutoff i ν d q (op a • b) n 0

/-- The polynomial insertion and retraction split, including zero idempotent rows. -/
@[simp] theorem appendPolynomialRowsRetraction_section (i : I) (ν : List I) (d : ℕ)
    (z : AppendPolynomialOldRows D Sc cutoff i ν d) :
    appendPolynomialRowsRetraction D Sc cutoff i ν d (appendPolynomialRowsSection D Sc cutoff i ν d z) = z := by
  obtain ⟨z, rfl⟩ := (RightCentralPolynomialModule.of _).surjective z
  induction z using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | of q b =>
    rw [appendPolynomialRowsSection_of, appendPolynomialRowsRetraction_single, appendPolynomialRows_monomial]
    have h : op (oldRowInsert D Sc cutoff ν q.1.1.1 b) •
        oldRowUnit D Sc cutoff ν q.1.1.1 = b := oldRowRetraction_section D Sc cutoff ν q.1.1.1 b
    rw [h]

instance appendPolynomialOldRows_projective (i : I) (ν : List I) (d : ℕ) :
    Module.Projective (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ (AppendPolynomialOldRows D Sc cutoff i ν d) :=
  Module.Projective.of_split (appendPolynomialRowsSection D Sc cutoff i ν d)
    (appendPolynomialRowsRetraction D Sc cutoff i ν d) (by
      ext z
      exact appendPolynomialRowsRetraction_section D Sc cutoff i ν d z)

instance appendPolynomialOldRows_finite (i : I) (ν : List I) (d : ℕ) :
    Module.Finite (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ (AppendPolynomialOldRows D Sc cutoff i ν d) :=
  Module.Finite.of_surjective (appendPolynomialRowsRetraction D Sc cutoff i ν d)
    (Function.LeftInverse.surjective (appendPolynomialRowsRetraction_section D Sc cutoff i ν d))

/-- Concrete finite-free section for the original exponent-shift module. -/
def appendRowsPolynomialSection (i : I) (ν : List I) (d : ℕ) (hd : 0 < d) :
    AppendRowsPolynomial D Sc cutoff i ν d →ₗ[(Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ]
      AppendPolynomialFree D Sc cutoff i ν d :=
  (appendPolynomialRowsSection D Sc cutoff i ν d).comp
    (appendRowsPolynomialEquiv D Sc cutoff i ν d hd).toLinearMap

/-- Concrete finite-free retraction for the original exponent-shift module. -/
def appendRowsPolynomialRetraction (i : I) (ν : List I) (d : ℕ) :
    AppendPolynomialFree D Sc cutoff i ν d →ₗ[(Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ]
      AppendRowsPolynomial D Sc cutoff i ν d :=
  (appendRowsPolynomialJoin D Sc cutoff i ν d).comp (appendPolynomialRowsRetraction D Sc cutoff i ν d)

@[simp] theorem appendRowsPolynomialRetraction_section (i : I) (ν : List I) (d : ℕ) (hd : 0 < d)
    (z : AppendRowsPolynomial D Sc cutoff i ν d) :
    appendRowsPolynomialRetraction D Sc cutoff i ν d
      (appendRowsPolynomialSection D Sc cutoff i ν d hd z) = z := by
  simp only [appendRowsPolynomialRetraction, appendRowsPolynomialSection,
    LinearMap.comp_apply, appendPolynomialRowsRetraction_section, LinearEquiv.coe_coe]
  exact (appendRowsPolynomialEquiv D Sc cutoff i ν d hd).symm_apply_apply z

/-- Finite projectivity uses only positivity of the central step, not nonzero old corners. -/
theorem appendRowsPolynomial_projective (i : I) (ν : List I) (d : ℕ) (hd : 0 < d) :
    Module.Projective (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ
      (AppendRowsPolynomial D Sc cutoff i ν d) :=
  Module.Projective.of_equiv' (appendRowsPolynomialEquiv D Sc cutoff i ν d hd).symm

theorem appendRowsPolynomial_finite (i : I) (ν : List I) (d : ℕ) (hd : 0 < d) :
    Module.Finite (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ
      (AppendRowsPolynomial D Sc cutoff i ν d) :=
  Module.Finite.of_surjective (appendRowsPolynomialRetraction D Sc cutoff i ν d)
    (Function.LeftInverse.surjective (appendRowsPolynomialRetraction_section D Sc cutoff i ν d hd))

@[simp] theorem appendRowsPolynomialEquiv_symm_of (i : I) (ν : List I) (d : ℕ) (hd : 0 < d)
    (z : AppendPolynomialCoefficients D Sc cutoff i ν d) :
    (appendRowsPolynomialEquiv D Sc cutoff i ν d hd).symm
      (RightCentralPolynomialModule.of _ z) =
      RightCentralPolynomialModule.of _ (appendRowsJoin D Sc cutoff i ν d z) := rfl

@[simp] theorem appendRowsPolynomialEquiv_of (i : I) (ν : List I) (d : ℕ) (hd : 0 < d)
    (z : AppendRows D Sc cutoff i ν) :
    appendRowsPolynomialEquiv D Sc cutoff i ν d hd (RightCentralPolynomialModule.of _ z) =
      RightCentralPolynomialModule.of _ (appendRowsSplit D Sc cutoff i ν d hd z) := by
  apply (appendRowsPolynomialEquiv D Sc cutoff i ν d hd).symm.injective
  rw [LinearEquiv.symm_apply_apply, appendRowsPolynomialEquiv_symm_of, appendRowsJoin_split]

instance appendRowsPolynomial_projective_inst (i : I) (ν : List I) (d : ℕ) [NeZero d] :
    Module.Projective (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ
      (AppendRowsPolynomial D Sc cutoff i ν d) :=
  appendRowsPolynomial_projective D Sc cutoff i ν d (Nat.pos_of_ne_zero (NeZero.ne d))

instance appendRowsPolynomial_finite_inst (i : I) (ν : List I) (d : ℕ) [NeZero d] :
    Module.Finite (Polynomial (ContentRing D Sc cutoff ν))ᵐᵒᵖ
      (AppendRowsPolynomial D Sc cutoff i ν d) :=
  appendRowsPolynomial_finite D Sc cutoff i ν d (Nat.pos_of_ne_zero (NeZero.ne d))

end OddMath.QuiverHecke.ELVOld
