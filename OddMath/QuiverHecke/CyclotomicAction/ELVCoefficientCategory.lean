/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientTransport

/-!
# The signed ELV coefficient quotient category

ELV (3.24)–(3.27), as used in `DeformedProjectiveResolution.md` §1 and
`DeformedGlobalQP.md` §3: the full polynomial/exterior coefficient algebra
modulo the specified two-sided coefficient ideal, including the even-cutoff
top relation. Homogeneity of that ideal gives a graded quotient algebra.
The resulting box-product category has signed composition, and its quotient
functor is linear and parity-preserving. Its Homs are exactly the existing
`ELVCoefficientHom` tensor modules.

Only coefficient relations are imposed. Neither the old-strand nor the
moving-strand cyclotomic polynomial is killed here. The old-cyclotomic
balanced target, all-prefix killing, QP and projective resolution remain
separate obligations. No flatness or restriction on the colour set is used.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVQuotient
universe u
variable {k A B : Type u} [CommRing k] [Ring A] [Algebra k A]
  [Ring B] [Algebra k B]

private theorem span_proj_mem (G : ZMod 2 → Submodule k A) [GradedAlgebra G]
    (s : Set A) (hs : ∀ x ∈ s, ∃ p, x ∈ G p)
    {x : A} (hx : x ∈ TwoSidedIdeal.span s) :
    ∀ p, GradedAlgebra.proj G p x ∈ TwoSidedIdeal.span s := by
  induction hx using TwoSidedIdeal.span_induction with
  | mem x hx =>
    obtain ⟨q, hq⟩ := hs x hx
    intro p
    by_cases h : q = p
    · subst p
      rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same G hq]
      exact TwoSidedIdeal.subset_span (s := s) hx
    · simpa only [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_ne G hq h] using
        (TwoSidedIdeal.span s).zero_mem
  | zero => intro p; simp
  | add x y hx hy ihx ihy =>
    intro p
    simpa only [map_add] using (TwoSidedIdeal.span s).add_mem (ihx p) (ihy p)
  | neg x hx ih =>
    intro p
    simpa only [map_neg] using (TwoSidedIdeal.span s).neg_mem (ih p)
  | left_absorb a x hx ih =>
    refine DirectSum.Decomposition.inductionOn G ?_ ?_ ?_ a
    · intro p; simp
    · intro q a p
      have h := DirectSum.coe_decompose_mul_add_of_left_mem G
        (i := q) (j := p - q) (b := x) a.property
      have he : q + (p - q) = p := by abel
      rw [he] at h
      rw [GradedAlgebra.proj_apply, h]
      exact (TwoSidedIdeal.span s).mul_mem_left _ _ (ih (p - q))
    · intro a b ha hb p
      simpa only [add_mul, map_add] using (TwoSidedIdeal.span s).add_mem (ha p) (hb p)
  | right_absorb b x hx ih =>
    refine DirectSum.Decomposition.inductionOn G ?_ ?_ ?_ b
    · intro p; simp
    · intro q b p
      have h := DirectSum.coe_decompose_mul_add_of_right_mem G
        (i := p - q) (j := q) (a := x) b.property
      rw [sub_add_cancel] at h
      rw [GradedAlgebra.proj_apply, h]
      exact (TwoSidedIdeal.span s).mul_mem_right _ _ (ih (p - q))
    · intro a b ha hb p
      simpa only [mul_add, map_add] using (TwoSidedIdeal.span s).add_mem (ha p) (hb p)

variable (G : ZMod 2 → Submodule k A) [GradedAlgebra G]

private theorem proj_sum (x : A) :
    GradedAlgebra.proj G 0 x + GradedAlgebra.proj G 1 x = x := by
  refine DirectSum.Decomposition.inductionOn G (by simp) ?_ ?_ x
  · intro p x
    rcases parity_eq_zero_or_one p with rfl | rfl
    · simp only [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same G x.property,
        DirectSum.decompose_of_mem_ne G x.property (by decide : (0 : ZMod 2) ≠ 1), add_zero]
    · simp only [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same G x.property,
        DirectSum.decompose_of_mem_ne G x.property (by decide : (1 : ZMod 2) ≠ 0), zero_add]
  · intro x y hx hy
    simpa only [map_add, add_add_add_comm] using congrArg₂ (· + ·) hx hy

variable (q : A →ₐ[k] B) (hq : Function.Surjective q)
  (hker : ∀ x, q x = 0 → ∀ p, q (GradedAlgebra.proj G p x) = 0)

private def quotientProj (p : ZMod 2) : B →ₗ[k] B :=
  ((LinearMap.ker q.toLinearMap).liftQ
    (q.toLinearMap.comp (GradedAlgebra.proj G p)) (fun x hx => hker x hx p)).comp
    (q.toLinearMap.quotKerEquivOfSurjective hq).symm.toLinearMap

private theorem quotientProj_apply (p : ZMod 2) (x : A) :
    quotientProj G q hq hker p (q x) = q (GradedAlgebra.proj G p x) := by
  unfold quotientProj
  change (LinearMap.ker q.toLinearMap).liftQ
    (q.toLinearMap.comp (GradedAlgebra.proj G p)) (fun x hx => hker x hx p)
    ((q.toLinearMap.quotKerEquivOfSurjective hq).symm (q.toLinearMap x)) = _
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

private abbrev quotientSVec : SVec k where
  carrier := B
  odd := quotientProj G q hq hker 1
  odd_comp_odd := by
    ext b
    obtain ⟨x, rfl⟩ := hq b
    simp only [LinearMap.comp_apply, quotientProj_apply, GradedAlgebra.proj_apply,
      DirectSum.decompose_of_mem_same G (DirectSum.decompose G x 1).property]

private theorem quotientSVec_proj (p : ZMod 2) (x : A) :
    (quotientSVec G q hq hker).proj p (q x) = q (GradedAlgebra.proj G p x) := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · change q x - quotientProj G q hq hker 1 (q x) = _
    rw [quotientProj_apply, ← map_sub]
    apply congrArg q
    exact sub_eq_iff_eq_add.mpr (proj_sum G x).symm
  · exact quotientProj_apply G q hq hker 1 x

private theorem quotientSVec_mem {p : ZMod 2} {x : A} (hx : x ∈ G p) :
    q x ∈ (quotientSVec G q hq hker).part p := by
  rw [SVec.mem_part_iff, quotientSVec_proj, GradedAlgebra.proj_apply,
    DirectSum.decompose_of_mem_same G hx]

private theorem quotientSVec_lift {p : ZMod 2} {b : B}
    (hb : b ∈ (quotientSVec G q hq hker).part p) : ∃ a ∈ G p, q a = b := by
  obtain ⟨a, rfl⟩ := hq b
  exact ⟨GradedAlgebra.proj G p a, (DirectSum.decompose G a p).property,
    (quotientSVec_proj G q hq hker p a).symm.trans ((SVec.mem_part_iff _).mp hb)⟩

private abbrev quotientGradedAlgebra : GradedAlgebra (quotientSVec G q hq hker).part :=
  { (SVec.isInternal_part (quotientSVec G q hq hker)).chooseDecomposition with
    one_mem := by
      simpa only [map_one] using quotientSVec_mem G q hq hker
        (SetLike.GradedOne.one_mem : (1 : A) ∈ G 0)
    mul_mem := by
      intro p r a b ha hb
      obtain ⟨a, ha', rfl⟩ := quotientSVec_lift G q hq hker ha
      obtain ⟨b, hb', rfl⟩ := quotientSVec_lift G q hq hker hb
      rw [← map_mul]
      exact quotientSVec_mem G q hq hker (SetLike.mul_mem_graded ha' hb') }

end OddMath.QuiverHecke.ELVQuotient

namespace OddMath.SKM.SYM
open OddMath.QuiverHecke.ELVQuotient
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k] (D : Datum I X)

private def modelRelations (cutoff : I → ℕ) : Set (PolynomialExterior D k) :=
  polynomialExteriorEquiv D k '' {a | ELVCoefficientRelation D k cutoff a}

private theorem modelIdeal (cutoff : I → ℕ) :
    (elvCoefficientIdeal D k cutoff).comap (polynomialExteriorEquiv D k).symm.toRingHom =
      TwoSidedIdeal.span (modelRelations (k := k) D cutoff) := by
  apply le_antisymm
  · have h : elvCoefficientIdeal D k cutoff ≤
        (TwoSidedIdeal.span (modelRelations (k := k) D cutoff)).comap
          (polynomialExteriorEquiv D k).toRingHom := by
      apply TwoSidedIdeal.span_le.mpr
      intro a ha
      rw [SetLike.mem_coe, TwoSidedIdeal.mem_comap]
      exact TwoSidedIdeal.subset_span (s := modelRelations (k := k) D cutoff) ⟨a, ha, rfl⟩
    intro a ha
    rw [TwoSidedIdeal.mem_comap] at ha
    have hh := h ha
    rw [TwoSidedIdeal.mem_comap] at hh
    change polynomialExteriorEquiv D k ((polynomialExteriorEquiv D k).symm a) ∈ _ at hh
    rwa [AlgEquiv.apply_symm_apply] at hh
  · apply TwoSidedIdeal.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    rw [SetLike.mem_coe, TwoSidedIdeal.mem_comap]
    change (polynomialExteriorEquiv D k).symm (polynomialExteriorEquiv D k a) ∈ elvCoefficientIdeal D k cutoff
    rw [AlgEquiv.symm_apply_apply]
    exact TwoSidedIdeal.subset_span ha

private theorem modelRelations_homogeneous (cutoff : I → ℕ) :
    ∀ a ∈ modelRelations (k := k) D cutoff, ∃ p, a ∈ polynomialExteriorParity D k p := by
  rintro _ ⟨a, ha, rfl⟩
  rcases ha with ⟨i, r, _, rfl⟩ | ⟨i, _, rfl⟩
  · exact ⟨0, polynomialExterior_e_mem_even D k i r⟩
  · refine ⟨1, ?_⟩
    rw [map_mul]
    simpa only [add_zero] using SetLike.mul_mem_graded
      (polynomialExterior_delta_mem_odd D k i) (elvChi_mem_even D i (cutoff i.1 / 2))

/-- Both parity projections preserve the exact two-sided ELV coefficient ideal. -/
theorem elvCoefficientIdeal_parity (cutoff : I → ℕ) {a : PolynomialExterior D k}
    (ha : (polynomialExteriorEquiv D k).symm a ∈ elvCoefficientIdeal D k cutoff)
    (p : ZMod 2) :
    (polynomialExteriorEquiv D k).symm (GradedAlgebra.proj (polynomialExteriorParity D k) p a) ∈
      elvCoefficientIdeal D k cutoff := by
  have h := modelIdeal (k := k) D cutoff
  change a ∈ (elvCoefficientIdeal D k cutoff).comap
    (polynomialExteriorEquiv D k).symm.toRingHom at ha
  change GradedAlgebra.proj (polynomialExteriorParity D k) p a ∈
    (elvCoefficientIdeal D k cutoff).comap (polynomialExteriorEquiv D k).symm.toRingHom
  rw [h] at ha ⊢
  exact span_proj_mem _ _ (modelRelations_homogeneous D cutoff) ha p

/-- Quotient on the polynomial/exterior presentation, through its algebra equivalence. -/
def elvModelQuotient (cutoff : I → ℕ) :
    PolynomialExterior D k →ₐ[k] ELVCoefficientAlgebra (k := k) D cutoff :=
  (elvCoefficientQuotient D cutoff).comp (polynomialExteriorEquiv D k).symm.toAlgHom

private theorem modelQuotient_surjective (cutoff : I → ℕ) :
    Function.Surjective (elvModelQuotient (k := k) D cutoff) :=
  (RingCon.mkₐ_surjective (α := k) (elvCoefficientIdeal D k cutoff).ringCon).comp
    (polynomialExteriorEquiv D k).symm.surjective

private theorem modelQuotient_kernel (cutoff : I → ℕ) (a : PolynomialExterior D k)
    (ha : elvModelQuotient D cutoff a = 0) (p : ZMod 2) :
    elvModelQuotient D cutoff (GradedAlgebra.proj (polynomialExteriorParity D k) p a) = 0 := by
  apply elvCoefficientQuotient_eq_zero
  apply elvCoefficientIdeal_parity D cutoff
  exact Quotient.exact ha

/-- The canonical parity on the finite ELV coefficient algebra. -/
def elvCoefficientParity (cutoff : I → ℕ) :
    ZMod 2 → Submodule k (ELVCoefficientAlgebra (k := k) D cutoff) :=
  (quotientSVec (polynomialExteriorParity D k) (elvModelQuotient D cutoff)
    (modelQuotient_surjective D cutoff) (modelQuotient_kernel D cutoff)).part

instance elvCoefficientGradedAlgebra (cutoff : I → ℕ) :
    GradedAlgebra (elvCoefficientParity (k := k) D cutoff) :=
  quotientGradedAlgebra _ _ (modelQuotient_surjective D cutoff) (modelQuotient_kernel D cutoff)

theorem elvModelQuotient_mem {cutoff : I → ℕ} {p : ZMod 2} {a : PolynomialExterior D k}
    (ha : a ∈ polynomialExteriorParity D k p) :
    elvModelQuotient D cutoff a ∈ elvCoefficientParity D cutoff p :=
  quotientSVec_mem _ _ _ _ ha

end OddMath.SKM.SYM

namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

private theorem coefficientHom_induction {A B : CoefficientH D Sc}
    {P : (A ⟶ B) → Prop} (x : A ⟶ B) (zero : P 0)
    (tmul : ∀ (p q : ZMod 2) (a : A.fst ⟶ B.fst) (f : A.snd ⟶ B.snd),
      a ∈ parity (R := k) A.fst B.fst p → f ∈ parity (R := k) A.snd B.snd q →
      P (BoxProd.tmulHom a f))
    (add : ∀ x y, P x → P y → P (x + y)) : P x :=
  BoxProd.induction_on_homogeneous (P := P) x zero tmul add

/-- The signed affine category over the exact finite ELV coefficient algebra.
No strand cyclotomic polynomial is imposed in this coefficient quotient. -/
abbrev ELVCoefficientCategory (cutoff : I → ℕ) :=
  BoxProd k (SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := k) D cutoff)) (H D Sc)

abbrev elvQuotientObj (cutoff : I → ℕ) (A : CoefficientH D Sc) :
    ELVCoefficientCategory D Sc cutoff :=
  ⟨SuperalgebraCat.star _, A.snd⟩

def elvQuotientMap (cutoff : I → ℕ) (A B : CoefficientH D Sc) :
    (A ⟶ B) →ₗ[k] (elvQuotientObj D Sc cutoff A ⟶ elvQuotientObj D Sc cutoff B) :=
  TensorProduct.map (SKM.SYM.elvModelQuotient D cutoff).toLinearMap LinearMap.id

@[simp] theorem elvQuotientMap_tmul (cutoff : I → ℕ) {A B : CoefficientH D Sc}
    (a : A.fst ⟶ B.fst) (f : A.snd ⟶ B.snd) :
    elvQuotientMap D Sc cutoff A B (BoxProd.tmulHom a f) =
      BoxProd.tmulHom (X := elvQuotientObj D Sc cutoff A)
        (Y := elvQuotientObj D Sc cutoff B)
        (SuperalgebraCat.ofElem (SKM.SYM.elvModelQuotient D cutoff a)) f := rfl

/-- The quotient preserves the signed categorical composition, not just linear combinations. -/
theorem elvQuotientMap_comp (cutoff : I → ℕ) {A B C : CoefficientH D Sc}
    (x : A ⟶ B) (y : B ⟶ C) :
    elvQuotientMap D Sc cutoff A C (x ≫ y) =
      elvQuotientMap D Sc cutoff A B x ≫ elvQuotientMap D Sc cutoff B C y := by
  induction x using coefficientHom_induction D Sc with
  | zero => simp only [Limits.zero_comp, map_zero]
  | add x x' hx hx' => simp only [Preadditive.add_comp, map_add, hx, hx']
  | tmul p r a f ha hf =>
    induction y using coefficientHom_induction D Sc with
    | zero => simp only [Limits.comp_zero, map_zero]
    | add y y' hy hy' => simp only [Preadditive.comp_add, map_add, hy, hy']
    | tmul q s b g hb hg =>
      have hqa : SuperalgebraCat.ofElem (SKM.SYM.elvModelQuotient D cutoff a) ∈
          parity (R := k) (elvQuotientObj D Sc cutoff A).fst
            (elvQuotientObj D Sc cutoff B).fst p := SKM.SYM.elvModelQuotient_mem D ha
      rw [BoxProd.tmulHom_comp_tmulHom ha f b hg, map_zsmul,
        elvQuotientMap_tmul, elvQuotientMap_tmul, elvQuotientMap_tmul,
        BoxProd.tmulHom_comp_tmulHom
          (X := elvQuotientObj D Sc cutoff A) (Y := elvQuotientObj D Sc cutoff B)
          (Z := elvQuotientObj D Sc cutoff C) hqa f
          (SuperalgebraCat.ofElem (SKM.SYM.elvModelQuotient D cutoff b)) hg]
      exact congrArg (fun z : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff =>
        koszulSign p s • BoxProd.tmulHom
          (X := elvQuotientObj D Sc cutoff A) (Y := elvQuotientObj D Sc cutoff C)
          (SuperalgebraCat.ofElem z) (f ≫ g))
        (map_mul (SKM.SYM.elvModelQuotient D cutoff)
          (SuperalgebraCat.toElem b) (SuperalgebraCat.toElem a))

private theorem elvQuotientMap_proj (cutoff : I → ℕ) {A B : CoefficientH D Sc}
    (p : ZMod 2) (x : A ⟶ B) :
    elvQuotientMap D Sc cutoff A B (proj k p x) =
      proj k p (elvQuotientMap D Sc cutoff A B x) := by
  induction x using coefficientHom_induction D Sc with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul q r a f ha hf =>
    have hs : BoxProd.tmulHom a f ∈ parity (R := k) A B (q + r) :=
      BoxProd.tmul_mem_parity ha hf
    have ht : BoxProd.tmulHom (X := elvQuotientObj D Sc cutoff A)
        (Y := elvQuotientObj D Sc cutoff B)
        (SuperalgebraCat.ofElem (SKM.SYM.elvModelQuotient D cutoff a)) f ∈
        parity (R := k) (elvQuotientObj D Sc cutoff A) (elvQuotientObj D Sc cutoff B) (q + r) :=
      BoxProd.tmul_mem_parity (SKM.SYM.elvModelQuotient_mem D ha) hf
    by_cases h : q + r = p
    · subst p
      rw [proj_of_mem hs, elvQuotientMap_tmul, proj_of_mem ht]
    · rw [proj_of_mem_ne hs h, map_zero, elvQuotientMap_tmul, proj_of_mem_ne ht h]

/-- Quotient parity is the image of the original polynomial/exterior parity. -/
theorem elvQuotientMap_mem (cutoff : I → ℕ) {A B : CoefficientH D Sc}
    {p : ZMod 2} {x : A ⟶ B} (hx : x ∈ parity (R := k) A B p) :
    elvQuotientMap D Sc cutoff A B x ∈ parity (R := k)
      (elvQuotientObj D Sc cutoff A) (elvQuotientObj D Sc cutoff B) p := by
  apply mem_iff_proj.mpr
  rw [← elvQuotientMap_proj, proj_of_mem hx]

/-- The finite-coefficient quotient functor on the signed affine category. -/
def elvQuotientFunctor (cutoff : I → ℕ) :
    CoefficientH D Sc ⥤ ELVCoefficientCategory D Sc cutoff where
  obj := elvQuotientObj D Sc cutoff
  map := elvQuotientMap D Sc cutoff _ _
  map_id A := by
    change SKM.SYM.elvModelQuotient D cutoff 1 ⊗ₜ[k] (𝟙 A.snd) = 1 ⊗ₜ[k] (𝟙 A.snd)
    rw [map_one]
  map_comp := elvQuotientMap_comp D Sc cutoff

instance elvQuotientFunctor_additive (cutoff : I → ℕ) :
    (elvQuotientFunctor D Sc cutoff).Additive where
  map_add := map_add (elvQuotientMap D Sc cutoff _ _) _ _

instance elvQuotientFunctor_linear (cutoff : I → ℕ) :
    Functor.Linear k (elvQuotientFunctor D Sc cutoff) where
  map_smul f r := map_smul (elvQuotientMap D Sc cutoff _ _) r f

instance elvQuotientFunctor_super (cutoff : I → ℕ) :
    IsSuperfunctor k (elvQuotientFunctor D Sc cutoff) where
  map_mem := elvQuotientMap_mem D Sc cutoff

/-- The quotient category has exactly the previously constructed quotient tensor Homs. -/
def elvQuotientHomEquiv (cutoff : I → ℕ) (t t' : List I) :
    (elvQuotientObj D Sc cutoff (coefficientObj D Sc t) ⟶
      elvQuotientObj D Sc cutoff (coefficientObj D Sc t')) ≃ₗ[k]
      ELVCoefficientHom D Sc cutoff t t' := LinearEquiv.refl k _

/-- The earlier tensor quotient is exactly the map of the categorical quotient functor. -/
theorem elvQuotientMap_eq (cutoff : I → ℕ) (t t' : List I) :
    (elvQuotientHomEquiv D Sc cutoff t t').toLinearMap.comp
      (elvQuotientMap D Sc cutoff (coefficientObj D Sc t) (coefficientObj D Sc t')) =
      elvHomQuotient D Sc cutoff t t' := by
  ext x
  obtain ⟨x, rfl⟩ := (sourceTensorEquiv D Sc t t').surjective x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a f =>
    change SKM.SYM.elvModelQuotient D cutoff (SKM.SYM.polynomialExteriorEquiv D k a) ⊗ₜ[k] f =
      elvHomQuotient D Sc cutoff t t' (sourceCoefficientHom D Sc a f)
    rw [elvHomQuotient_source]
    change SKM.SYM.elvCoefficientQuotient D cutoff
      ((SKM.SYM.polynomialExteriorEquiv D k).symm (SKM.SYM.polynomialExteriorEquiv D k a)) ⊗ₜ[k] f = _
    rw [AlgEquiv.symm_apply_apply]

/-- Full source coefficients map to their exact ELV quotient classes. -/
theorem elvQuotientMap_source (cutoff : I → ℕ) {t t' : List I}
    (a : SKM.SYM D k) (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :
    elvQuotientMap D Sc cutoff _ _ (sourceCoefficientHom D Sc a f) =
      SKM.SYM.elvCoefficientQuotient D cutoff a ⊗ₜ[k] f := by
  change SKM.SYM.elvCoefficientQuotient D cutoff
    ((SKM.SYM.polynomialExteriorEquiv D k).symm (SKM.SYM.polynomialExteriorEquiv D k a)) ⊗ₜ[k] f = _
  rw [AlgEquiv.symm_apply_apply]

/-- Every element of the coefficient ideal vanishes in the categorical quotient. -/
theorem elvQuotientMap_kills {cutoff : I → ℕ} {t t' : List I}
    {a : SKM.SYM D k} (ha : a ∈ SKM.SYM.elvCoefficientIdeal D k cutoff)
    (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :
    elvQuotientMap D Sc cutoff _ _ (sourceCoefficientHom D Sc a f) = 0 := by
  rw [elvQuotientMap_source, SKM.SYM.elvCoefficientQuotient_eq_zero D ha,
    TensorProduct.zero_tmul]

/-- The two-sided span of the coefficient arm of `ELVGenerator`, at fixed strand number.
The odd and even strand-polynomial arms of `ELVGenerator` are not imposed here. -/
def ELVCoefficientRelationSpan (cutoff : I → ℕ) (t t' : List I) :
    Submodule k (coefficientObj D Sc t ⟶ coefficientObj D Sc t') :=
  Submodule.span k {f | ∃ v : List I, v.length = t.length ∧
    ∃ c : SKM.SYM D k, c ∈ SKM.SYM.elvCoefficientIdeal D k cutoff ∧
    ∃ a : coefficientObj D Sc t ⟶ coefficientObj D Sc v,
    ∃ b : coefficientObj D Sc v ⟶ coefficientObj D Sc t',
      a ≫ sourceCoefficientHom D Sc c (𝟙 _) ≫ b = f}

/-- This is precisely a subspan of the specified ELV relation span, using its coefficient arm. -/
theorem elvCoefficientRelationSpan_le (cutoff : I → ℕ) (t t' : List I) :
    ELVCoefficientRelationSpan D Sc cutoff t t' ≤ ELVRelationSpan D Sc cutoff t t' := by
  apply Submodule.span_mono
  rintro _ ⟨v, hv, c, hc, a, b, rfl⟩
  exact ⟨v, hv, sourceCoefficientHom D Sc c (𝟙 _), Or.inl ⟨c, hc, rfl⟩, a, b, rfl⟩

/-- The quotient functor kills the actual two-sided coefficient span. -/
theorem elvQuotientMap_kills_span (cutoff : I → ℕ) (t t' : List I) :
    ELVCoefficientRelationSpan D Sc cutoff t t' ≤
      LinearMap.ker (elvQuotientMap D Sc cutoff (coefficientObj D Sc t) (coefficientObj D Sc t')) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨v, _, c, hc, a, b, rfl⟩
  change elvQuotientMap D Sc cutoff _ _ (a ≫ sourceCoefficientHom D Sc c (𝟙 _) ≫ b) = 0
  rw [elvQuotientMap_comp, elvQuotientMap_comp, elvQuotientMap_kills D Sc hc,
    Limits.zero_comp, Limits.comp_zero]

/-- In the quotient category an odd coefficient anticommutes with an odd affine morphism. -/
theorem elvQuotient_odd_comp_odd (cutoff : I → ℕ) {t t' t'' : List I}
    (i : {i : I // D.parity i = 1})
    (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t'))
    {g : (pres D Sc).obj (ob D t') ⟶ (pres D Sc).obj (ob D t'')}
    (hg : g ∈ parity (R := k) _ _ 1) :
    (elvQuotientFunctor D Sc cutoff).map (sourceCoefficientHom D Sc (SKM.SYM.delta D k i) f) ≫
      (elvQuotientFunctor D Sc cutoff).map (sourceCoefficientHom D Sc 1 g) =
      -(elvQuotientFunctor D Sc cutoff).map
        (sourceCoefficientHom D Sc (SKM.SYM.delta D k i) (f ≫ g)) := by
  rw [← Functor.map_comp, odd_coefficient_comp_odd D Sc i f hg, Functor.map_neg]

end OddMath.QuiverHecke
