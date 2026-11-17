import Mathlib.Algebra.DirectSum.Module
import OddMath.QuiverHecke.CoefficientExtension
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerChains.IntertwinerGrading
import OddMath.QuiverHecke.CyclotomicSeparation
import OddMath.QuiverHecke.ELVCyclotomicSeparation
import OddMath.QuiverHecke.WeightedCoefficientSeparation
import OddMath.SKM.BubbleAlgebra
import OddMath.SKM.BubbleELVCoefficients
import OddMath.SKM.BubbleELVSpecialization
import OddMath.SKM.BubbleExterior
import OddMath.SKM.BubbleParity
import OddMath.SKM.BubblePolynomialExterior

/-!
# Coefficient transport

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-!
# Coefficient-polynomial transport through an intertwiner chain

The full source-coefficient transport identity of
`docs/Nondegeneracy/DeformedProjectiveResolution.md`, §1, equation (1),
supporting the repeated-colour QP step in `DeformedGlobalQP.md`, §3.
The affine dot transport is supplied by the existing KKO I (8.13) lemmas.

A coefficient of degree m in a polynomial of total parity P has parity
P - m p(x). Its Koszul sign and the dot sign combine to P times the
parity of the entire intertwiner chain. Odd coefficients are not central:
the composition is the existing `sourceCoefficientHom` composition in
`CoefficientH`, retaining the full abstract SYM algebra.

Both moving and old strands are covered over any commutative ground ring
with the given scalar datum, without finite-colour or monicity assumptions.
Finite ELV coefficient quotient descent and the balanced QP induction are
separate obligations, not consequences claimed here.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

private theorem coefficientTransport_zsign (p : ZMod 2) :
    SKM.zsign k p = sign k p := by
  rcases parity_eq_zero_or_one p with h | h <;> simp [h, SKM.zsign]

private theorem coefficientTransport_pow_parity {A : H D Sc} (y : End A)
    {p : ZMod 2} (hy : y ∈ parity (R := k) A A p) (m : ℕ) :
    (y ^ m : End A) ∈ parity (R := k) A A (m • p) := by
  induction m with
  | zero => simpa only [pow_zero, zero_nsmul, End.one_def] using id_mem (R := k) A
  | succ m ih =>
    simpa only [pow_succ, End.mul_def, succ_nsmul, add_comm] using comp_mem hy ih

/-- Finite dot polynomial with coefficients in the full abstract source algebra. -/
def coefficientDotPolynomial (w : List I) (r N : ℕ) (c : Fin (N + 1) → SKM.SYM D k) :
    End (coefficientObj D Sc w) :=
  ∑ m, sourceCoefficientHom D Sc (c m) (dotE D Sc w r ^ m.val)

private theorem coefficientTransport_sum {t t' : List I}
    (x : End ((pres D Sc).obj (ob D t)))
    (y : End ((pres D Sc).obj (ob D t')))
    (g : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t'))
    (p q P : ZMod 2) (N : ℕ) (c : Fin (N + 1) → SKM.SYM D k)
    (hy : y ∈ parity (R := k) _ _ p) (hg : g ∈ parity (R := k) _ _ q)
    (h : ∀ m : ℕ, (x ^ m : End _) ≫ g = sign k (m • (p * q)) •
      (g ≫ (y ^ m : End _)))
    (hc : ∀ m, SKM.SYM.polynomialExteriorEquiv D k (c m) ∈
      SKM.SYM.polynomialExteriorParity D k (P - m.val • p)) :
    (∑ m, sourceCoefficientHom D Sc (c m) (x ^ m.val)) ≫
        sourceCoefficientHom D Sc 1 g =
      sign k (P * q) • (sourceCoefficientHom D Sc 1 g ≫
        ∑ m, sourceCoefficientHom D Sc (c m) (y ^ m.val)) := by
  classical
  rw [Preadditive.sum_comp, Preadditive.comp_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro m _
  have h1 : SKM.SYM.polynomialExteriorEquiv D k 1 ∈
      SKM.SYM.polynomialExteriorParity D k 0 := by
    rw [map_one]
    exact SetLike.GradedOne.one_mem
  rw [sourceCoefficientHom_comp D Sc (hc m) _ _ hg,
    sourceCoefficientHom_comp D Sc h1 _ _ (coefficientTransport_pow_parity D Sc y hy m.val),
    koszulSign_zero_left, one_smul, one_mul, mul_one, h,
    sourceCoefficientHom_smul_right, koszulSign_smul (R := k), smul_smul, ← sign_add]
  congr 2
  simp only [nsmul_eq_mul]
  ring

/-- Full source coefficients and the moving dot acquire a common total Koszul sign.
No centrality of odd coefficients is assumed. This is affine transport, not the
balanced QP induction or construction of the finite ELV action. -/
theorem coefficientDotPolynomial_comp_moveHom (i : I) (l ν : List I) (N : ℕ)
    (c : Fin (N + 1) → SKM.SYM D k) (P : ZMod 2)
    (hc : ∀ m, SKM.SYM.polynomialExteriorEquiv D k (c m) ∈
      SKM.SYM.polynomialExteriorParity D k (P - m.val • D.parity i)) :
    coefficientDotPolynomial D Sc (l ++ i :: ν) l.length N c ≫
        sourceCoefficientHom D Sc 1 (moveHom D Sc i l ν) =
      sign k (P * (D.parity i * wordSumParity D ν)) •
        (sourceCoefficientHom D Sc 1 (moveHom D Sc i l ν) ≫
          coefficientDotPolynomial D Sc (l ++ ν ++ [i]) (l.length + ν.length) N c) := by
  apply coefficientTransport_sum D Sc _ _ _ (D.parity i)
    (D.parity i * wordSumParity D ν) P N c
  · simpa only [List.append_assoc, List.append_nil, List.length_append] using
      positionedDot_parity D Sc (l ++ ν) [] i
  · exact moveHom_parity D Sc i l ν
  · intro m
    have he : D.parity i * (D.parity i * wordSumParity D ν) =
        D.parity i * wordSumParity D ν := by
      rcases parity_eq_zero_or_one (D.parity i) with hp | hp <;> simp [hp]
    rw [he, ← coefficientTransport_zsign]
    exact dot_pow_comp_moveHom D Sc i l ν m
  · exact hc

end OddMath.QuiverHecke
end

end

section

/-!
# ELV coefficient-quotient transport

The coefficient-sensitive transport of `DeformedProjectiveResolution.md` §1 (1),
with the finite coefficient algebra of ELV (3.24)–(3.27). The quotient is by
`elvCoefficientIdeal`, including its even-cutoff top relation, not by an
ordinary polynomial ideal. The target is the coefficient-quotient tensor
module; no balanced QP identity or categorical action is asserted here.
-/

noncomputable section
open scoped TensorProduct
namespace OddMath.SKM.SYM
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : Datum I X)

/-- The finite ELV coefficient algebra, retaining the exterior generators. -/
abbrev ELVCoefficientAlgebra (cutoff : I → ℕ) :=
  (elvCoefficientIdeal D k cutoff).ringCon.Quotient

def elvCoefficientQuotient (cutoff : I → ℕ) :
    SYM D k →ₐ[k] ELVCoefficientAlgebra (k := k) D cutoff :=
  (elvCoefficientIdeal D k cutoff).ringCon.mkₐ k

theorem elvCoefficientQuotient_eq_zero {cutoff : I → ℕ} {a : SYM D k}
    (ha : a ∈ elvCoefficientIdeal D k cutoff) :
    elvCoefficientQuotient D cutoff a = 0 := Quotient.sound ha

/-- The top relation is retained also at cutoff zero, where it kills delta. -/
theorem elvCoefficientQuotient_top (cutoff : I → ℕ)
    (i : {i : I // D.parity i = 1}) (he : cutoff i.1 % 2 = 0) :
    elvCoefficientQuotient (k := k) D cutoff
      (delta D k i * elvChi D k i (cutoff i.1 / 2)) = 0 := by
  apply elvCoefficientQuotient_eq_zero
  exact TwoSidedIdeal.subset_span (Or.inr ⟨i, he, rfl⟩)

theorem elvChi_mem_even (i : {i : I // D.parity i = 1}) (r : ℕ) :
    polynomialExteriorEquiv D k (elvChi D k i r) ∈ polynomialExteriorParity D k 0 := by
  cases r with
  | zero => simpa [elvChi] using
      (SetLike.GradedOne.one_mem : (1 : PolynomialExterior D k) ∈ polynomialExteriorParity D k 0)
  | succ r => exact polynomialExterior_e_mem_even D k i.1 r

theorem elvCoefficient_mem_parity (i : {i : I // D.parity i = 1}) (n : ℕ) :
    polynomialExteriorEquiv D k (elvCoefficient D k i n) ∈
      polynomialExteriorParity D k (n : ZMod 2) := by
  have hn : (n : ZMod 2) = (n % 2 : ℕ) := by
    simpa only [ZMod.val_natCast] using (ZMod.natCast_zmod_val (n : ZMod 2)).symm
  unfold elvCoefficient
  split_ifs with he
  · rw [hn, he, Nat.cast_zero]
    exact elvChi_mem_even D i _
  · have ho : n % 2 = 1 := by omega
    rw [hn, ho, Nat.cast_one, map_mul]
    simpa only [add_zero] using SetLike.mul_mem_graded
      (polynomialExterior_delta_mem_odd D k i) (elvChi_mem_even D i (n / 2))

/-- The coefficient of x^j has parity N-j, including exterior coefficients. -/
theorem elvMonicCoefficient_mem_parity (i : {i : I // D.parity i = 1})
    (N : ℕ) (j : Fin (N + 1)) :
    polynomialExteriorEquiv D k (elvMonicCoefficient D k i N j) ∈
      polynomialExteriorParity D k ((N : ZMod 2) - j.val • D.parity i.1) := by
  have hj : j.val ≤ N := Nat.le_of_lt_succ j.isLt
  rw [elvMonicCoefficient, map_smul, i.property, nsmul_eq_mul, mul_one,
    ← Nat.cast_sub hj]
  exact Submodule.smul_mem _ _ (elvCoefficient_mem_parity D i (N - j.val))
end OddMath.SKM.SYM

namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

/-- Base change of an affine Hom module to the exact finite ELV coefficient algebra. -/
abbrev ELVCoefficientHom (cutoff : I → ℕ) (t t' : List I) :=
  SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff ⊗[k]
    ((pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t'))

/-- The canonical coefficient-quotient map; no flatness or descent premise. -/
def elvHomQuotient (cutoff : I → ℕ) (t t' : List I) :
    (coefficientObj D Sc t ⟶ coefficientObj D Sc t') →ₗ[k]
      ELVCoefficientHom D Sc cutoff t t' :=
  (TensorProduct.map (SKM.SYM.elvCoefficientQuotient D cutoff).toLinearMap
    (LinearMap.id : _ →ₗ[k] _)).comp (sourceTensorEquiv D Sc t t').symm.toLinearMap

@[simp] theorem elvHomQuotient_source (cutoff : I → ℕ) {t t' : List I}
    (a : SKM.SYM D k) (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :
    elvHomQuotient D Sc cutoff t t' (sourceCoefficientHom D Sc a f) =
      SKM.SYM.elvCoefficientQuotient D cutoff a ⊗ₜ[k] f := by
  change TensorProduct.map _ _ ((sourceTensorEquiv D Sc t t').symm
    (sourceTensorEquiv D Sc t t' (a ⊗ₜ[k] f))) = _
  rw [LinearEquiv.symm_apply_apply, TensorProduct.map_tmul]
  rfl

/-- The ELV polynomial at any strand, with the existing normalized left coefficients. -/
def elvDotPolynomial (i : {i : I // D.parity i = 1}) (w : List I) (r N : ℕ) :
    End (coefficientObj D Sc w) :=
  coefficientDotPolynomial D Sc w r N (SKM.SYM.elvMonicCoefficient D k i N)

/-- At the first strand this is exactly the pre-existing ELV cyclotomic generator. -/
theorem elvDotPolynomial_first (i : {i : I // D.parity i = 1}) (tail : List I) (N : ℕ) :
    elvDotPolynomial D Sc i (i.1 :: tail) 0 N = elvCyclotomic D Sc i tail N := by
  unfold elvDotPolynomial coefficientDotPolynomial elvCyclotomic deformedCyclotomic
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp only [dotE_pow, firstDotPower, List.map_replicate]

end OddMath.QuiverHecke
end

end

section

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

/-- The two-sided ideal generated by homogeneous coefficients is closed
under each parity projection. Used for the literal coefficient-power quotient. -/
theorem homogeneousIdeal_projection_mem
    (G : ZMod 2 → Submodule k A) [GradedAlgebra G]
    (s : Set A) (hs : ∀ x ∈ s, ∃ p, x ∈ G p)
    {x : A} (hx : x ∈ TwoSidedIdeal.span s) (p : ZMod 2) :
    GradedAlgebra.proj G p x ∈ TwoSidedIdeal.span s :=
  span_proj_mem G s hs hx p

/-- The parity superspace of a homogeneous algebra quotient, on its
literal quotient carrier. The kernel projection hypothesis is explicit. -/
abbrev gradedQuotientSpace : SVec k := quotientSVec G q hq hker

/-- The quotient parity projection is induced by the original one. -/
theorem gradedQuotientSpace_projection (p : ZMod 2) (x : A) :
    (gradedQuotientSpace G q hq hker).proj p (q x) =
      q (GradedAlgebra.proj G p x) := quotientSVec_proj G q hq hker p x

/-- Homogeneous representatives retain their original parity. -/
theorem gradedQuotientSpace_mem {p : ZMod 2} {x : A} (hx : x ∈ G p) :
    q x ∈ (gradedQuotientSpace G q hq hker).part p := quotientSVec_mem G q hq hker hx

/-- Multiplication on the literal quotient respects the induced parity
grading, with no coefficient-flatness assumption. -/
abbrev gradedQuotientAlgebra : GradedAlgebra (gradedQuotientSpace G q hq hker).part :=
  quotientGradedAlgebra G q hq hker

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

end OddMath.QuiverHecke
end

end
