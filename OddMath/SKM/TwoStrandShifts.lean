/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.SKM.TwoStrandSummands

/-!
# Degree shifts of the even two-strand summand

The shift identification needed for the even two-strand case of Brundan–Ellis,
arXiv:1701.04133v2, Lemma 11.5. Statements concern the split Grothendieck group
of one hom category, not the full Grothendieck ring.
-/

noncomputable section

namespace OddMath.SKM.TwoStrand

open CategoryTheory StringDiagrams GradedSupercategory
open CategoryTheory.Idempotents CategoryTheory.Limits

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] (Sc : Scalars D k) (sy : Symmetrizer D)
  (hc : Sc.Homogeneous) (i : I) (ν : X)

private theorem q_projector (hi : D.parity i = 0) (n : ℤ) :
    (QPiCategory.Q (R := k) (C := Base Sc sy hc i ν)).map
      (projector Sc sy hc i ν hi n) = projector Sc sy hc i ν hi (n + 1) := by
  apply Subtype.ext; apply Subtype.ext
  change 𝟙 _ ≫ (e Sc sy hc i ν ≫ 𝟙 _) = e Sc sy hc i ν
  simp only [Category.id_comp, Category.comp_id]

private def projectorIso {C : Type*} [Category C] (V : C) (p q : End V)
    (hp : p ≫ p = p) (hq : q ≫ q = q) (h : p = q) :
    (⟨V, p, hp⟩ : Karoubi C) ≅ ⟨V, q, hq⟩ where
  hom := ⟨q, by change p ≫ q ≫ q = q; rw [h, hq, hq]⟩
  inv := ⟨q, by change q ≫ q ≫ p = q; rw [h, hq, hq]⟩
  hom_inv_id := by apply Karoubi.hom_ext; exact hq.trans h.symm
  inv_hom_id := by apply Karoubi.hom_ext; exact hq

private theorem q_matrix_projector (hi : D.parity i = 0) (n : ℤ) :
    ((QPiCategory.Q (R := k) (C := Karoubi (Mat_ (Base Sc sy hc i ν)))).obj
      (raw Sc sy hc i ν hi n)).p = (raw Sc sy hc i ν hi (n + 1)).p := by
  change (Mat_.embedding (Base Sc sy hc i ν)).map
      ((QPiCategory.Q (R := k)).map (projector Sc sy hc i ν hi n)) = _
  rw [q_projector]
  rfl

/-- The existing `Q` functor shifts the raw summand by one. -/
def qRawIso (hi : D.parity i = 0) (n : ℤ) :
    (QPiCategory.Q (R := k) (C := Karoubi (Mat_ (Base Sc sy hc i ν)))).obj
      (raw Sc sy hc i ν hi n) ≅ raw Sc sy hc i ν hi (n + 1) :=
  projectorIso _ _ _
    ((QPiCategory.Q (R := k) (C := Karoubi (Mat_ (Base Sc sy hc i ν)))).obj
      (raw Sc sy hc i ν hi n)).idem
    (raw Sc sy hc i ν hi (n + 1)).idem (q_matrix_projector Sc sy hc i ν hi n)

private theorem qinv_projector (hi : D.parity i = 0) (n : ℤ) :
    (QPiCategory.Qinv (R := k) (C := Base Sc sy hc i ν)).map
      (projector Sc sy hc i ν hi n) = projector Sc sy hc i ν hi (n - 1) := by
  apply Subtype.ext; apply Subtype.ext
  change 𝟙 _ ≫ (e Sc sy hc i ν ≫ 𝟙 _) = e Sc sy hc i ν
  simp only [Category.id_comp, Category.comp_id]

private theorem qinv_matrix_projector (hi : D.parity i = 0) (n : ℤ) :
    ((QPiCategory.Qinv (R := k) (C := Karoubi (Mat_ (Base Sc sy hc i ν)))).obj
      (raw Sc sy hc i ν hi n)).p = (raw Sc sy hc i ν hi (n - 1)).p := by
  change (Mat_.embedding (Base Sc sy hc i ν)).map
      ((QPiCategory.Qinv (R := k)).map (projector Sc sy hc i ν hi n)) = _
  rw [qinv_projector]
  rfl

/-- The inverse shift functor lowers the raw shift by one. -/
def qinvRawIso (hi : D.parity i = 0) (n : ℤ) :
    (QPiCategory.Qinv (R := k) (C := Karoubi (Mat_ (Base Sc sy hc i ν)))).obj
      (raw Sc sy hc i ν hi n) ≅ raw Sc sy hc i ν hi (n - 1) :=
  projectorIso _ _ _
    ((QPiCategory.Qinv (R := k) (C := Karoubi (Mat_ (Base Sc sy hc i ν)))).obj
      (raw Sc sy hc i ν hi n)).idem
    (raw Sc sy hc i ν hi (n - 1)).idem (qinv_matrix_projector Sc sy hc i ν hi n)

private def powFamilyIso {C : Type*} [Category C] (E : C ≌ C) (f : ℤ → C)
    (d : ℤ) (step : ∀ m, E.functor.obj (f m) ≅ f (m + d)) :
    ∀ (n : ℕ) (m : ℤ), (E.powNat n).functor.obj (f m) ≅ f (m + n * d)
  | 0, m => eqToIso (by simp [Equivalence.powNat])
  | 1, m => (step m) ≪≫ eqToIso (by simp)
  | n + 2, m =>
      (E.powNat (n + 1)).functor.mapIso (step m) ≪≫
        powFamilyIso E f d step (n + 1) (m + d) ≪≫
          eqToIso (by congr 1; push_cast; ring)

/-- Integer powers of the existing Q equivalence identify every raw shift.
The exponent may be negative; no replacement shift functor is introduced. -/
def qPowRawIso (hi : D.parity i = 0) (n m : ℤ) :
    ((QPiCategory.qEquivalence k (Karoubi (Mat_ (Base Sc sy hc i ν))) ^ n).functor.obj
      (raw Sc sy hc i ν hi m)) ≅ raw Sc sy hc i ν hi (m + n) := by
  cases n with
  | ofNat n =>
    exact powFamilyIso _ (raw Sc sy hc i ν hi) 1 (qRawIso Sc sy hc i ν hi) n m ≪≫
      eqToIso (by simp)
  | negSucc n =>
    exact powFamilyIso _ (raw Sc sy hc i ν hi) (-1) (qinvRawIso Sc sy hc i ν hi) (n + 1) m ≪≫
      eqToIso (by congr 1; omega)

/-- The recovered splitting, now expressed using powers of the actual Q functor. -/
def qDecomposition (hi : D.parity i = 0) :
    whole Sc sy hc i ν ≅ raw Sc sy hc i ν hi 0 ⊞
      ((QPiCategory.qEquivalence k (Karoubi (Mat_ (Base Sc sy hc i ν))) ^
        (2 * sy.d i)).functor.obj (raw Sc sy hc i ν hi 0)) :=
  decomposition Sc sy hc i ν hi ≪≫ biprod.mapIso (Iso.refl _) 
    ((qPowRawIso Sc sy hc i ν hi (2 * sy.d i) 0) ≪≫ eqToIso (by rw [zero_add])).symm

private theorem classFamily {R C : Type*} [CommRing R] [Category C]
    [Preadditive C] [Linear R C] [QPiCategory R C] [HasBinaryBiproducts C]
    (f : ℤ → C)
    (up : ∀ m, (QPiCategory.Q (R := R)).obj (f m) ≅ f (m + 1))
    (down : ∀ m, (QPiCategory.Qinv (R := R)).obj (f m) ≅ f (m - 1))
    (m n : ℤ) :
    letI := K₀.moduleLaurent R C
    (LaurentPolynomial.T n : LaurentPolynomial Zπ) • K₀.mk (f m) = K₀.mk (f (m + n)) := by
  let := K₀.moduleLaurent R C
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [show (n : ℤ) + 1 = 1 + n by omega, LaurentPolynomial.T_add, mul_smul, ih,
      K₀.T_smul_mk,
      K₀.mk_eq_mk_of_iso (up (m + n))]
    congr 2
    omega
  | pred n ih =>
    rw [show -(n : ℤ) - 1 = -1 + -(n : ℤ) by omega,
      LaurentPolynomial.T_add, mul_smul, ih,
      K₀.T_neg_one_smul_mk, K₀.mk_eq_mk_of_iso (down (m + -(n : ℤ)))]
    congr 2
    omega

/-- Every integer shift acts through the existing Laurent-module structure on split K₀. -/
theorem class_raw_shift (hi : D.parity i = 0) (m n : ℤ) :
    letI := K₀.moduleLaurent k (Karoubi (Mat_ (Base Sc sy hc i ν)))
    (LaurentPolynomial.T n : LaurentPolynomial Zπ) • K₀.mk (raw Sc sy hc i ν hi m) =
      K₀.mk (raw Sc sy hc i ν hi (m + n)) :=
  classFamily (R := k) (C := Karoubi (Mat_ (Base Sc sy hc i ν)))
    (raw Sc sy hc i ν hi) (qRawIso Sc sy hc i ν hi) (qinvRawIso Sc sy hc i ν hi) m n

/-- The raw two-strand coefficient is `1 + q^(2dᵢ)` in split K₀ of this hom category. -/
theorem class_raw_coefficient (hi : D.parity i = 0) :
    letI := K₀.moduleLaurent k (Karoubi (Mat_ (Base Sc sy hc i ν)))
    K₀.mk (whole Sc sy hc i ν) =
      (1 + LaurentPolynomial.T (2 * sy.d i) : LaurentPolynomial Zπ) •
        K₀.mk (raw Sc sy hc i ν hi 0) := by
  let := K₀.moduleLaurent k (Karoubi (Mat_ (Base Sc sy hc i ν)))
  rw [add_smul, one_smul, class_raw_shift, zero_add]
  exact class_decomposition Sc sy hc i ν hi

/-- Local normalization of the even two-strand summand: positive shift `dᵢ`.
This does not redefine the divided powers elsewhere in the library. -/
def normalizedTwo (hi : D.parity i = 0) : Karoubi (Mat_ (Base Sc sy hc i ν)) :=
  (QPiCategory.qEquivalence k (Karoubi (Mat_ (Base Sc sy hc i ν))) ^ sy.d i).functor.obj
    (raw Sc sy hc i ν hi 0)

private theorem normalized_class (hi : D.parity i = 0) :
    K₀.mk (normalizedTwo Sc sy hc i ν hi) = K₀.mk (raw Sc sy hc i ν hi (sy.d i)) :=
  K₀.mk_eq_mk_of_iso (qPowRawIso Sc sy hc i ν hi (sy.d i) 0 ≪≫
    eqToIso (by rw [zero_add]))

private theorem coefficient_add {A M : Type*} [Semiring A] [AddCommMonoid M] [Module A M]
    (a b : A) (x y z w : M) (hx : x = y + z) (hy : a • w = y) (hz : b • w = z) :
    x = (a + b) • w := by rw [add_smul, hy, hz]; exact hx

/-- The local normalized summand has even quantum-integer coefficient
`q^(-dᵢ) + q^dᵢ`. This is a split-K₀ hom-category statement, not a K₀Ring comparison. -/
theorem class_normalized_coefficient (hi : D.parity i = 0) :
    letI := K₀.moduleLaurent k (Karoubi (Mat_ (Base Sc sy hc i ν)))
    K₀.mk (whole Sc sy hc i ν) =
      (LaurentPolynomial.T (-sy.d i) + LaurentPolynomial.T (sy.d i) : LaurentPolynomial Zπ) •
        K₀.mk (normalizedTwo Sc sy hc i ν hi) := by
  let := K₀.moduleLaurent k (Karoubi (Mat_ (Base Sc sy hc i ν)))
  rw [normalized_class]
  apply coefficient_add _ _ _ _ _ _ (class_decomposition Sc sy hc i ν hi)
  · exact (class_raw_shift Sc sy hc i ν hi (sy.d i) (-sy.d i)).trans
      (congrArg (fun n => K₀.mk (raw Sc sy hc i ν hi n)) (add_neg_cancel _))
  · exact (class_raw_shift Sc sy hc i ν hi (sy.d i) (sy.d i)).trans
      (congrArg (fun n => K₀.mk (raw Sc sy hc i ν hi n)) (by omega))

end OddMath.SKM.TwoStrand
