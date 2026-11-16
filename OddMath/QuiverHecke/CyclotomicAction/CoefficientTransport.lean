import OddMath.QuiverHecke.CyclotomicAction.IntertwinerChains
import OddMath.QuiverHecke.CyclotomicAction.SignedIntertwiner
import OddMath.QuiverHecke.WeightedCoefficientSeparation
import OddMath.QuiverHecke.ELVCyclotomicSeparation
import Mathlib.Algebra.DirectSum.Module

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

section

/-!
# The old-cyclotomic ELV target

`DeformedGlobalQP.md` §1 and `DeformedProjectiveResolution.md` §3:
the matrix-Hom components of H e(i,β) / H F₂ R₁(β)e(i,β), over the
signed ELV coefficient category. `insert` fixes the full coefficient algebra
and inserts the moving strand on the left. `ideal` is two-sided only in the
old category; `relations` closes its image under ambient left multiplication
(postcomposition in diagram order), not arbitrary right H multiplication.

`Target`, `projection` and `act` construct the quotient module componentwise,
without finite-colour matrix units. `pair` descends h ⊗ πᵖb ↦ [h ξ(φᵖ(b))]
and satisfies signed balance using total parity, including exterior coefficients.
`insert_elvPolynomial` identifies the old polynomial with F₂, and
`projection_elvPolynomial` proves its vanishing. No moving F₁ relation is imposed.

`ELVBalancedTensor` supplies the bundled signed tensor equivalence.
Right PBW coordinates for this coefficient extension, nonvanishing of the
moving polynomial, and all-prefix QP/cancellation remain unproved.
No flatness or cyclotomic freeness is assumed.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

abbrev obj (v : List I) := elvQuotientObj D Sc cutoff (coefficientObj D Sc v)
abbrev hom (v w : List I) := obj D Sc cutoff v ⟶ obj D Sc cutoff w

def affineInsert (i : I) (v w : List I) :
    ((pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) →ₗ[k]
    ((pres D Sc).obj (ob D (i :: v)) ⟶ (pres D Sc).obj (ob D (i :: w))) where
  toFun f := (pres D Sc).obj (ob D [i]) ◁ f
  map_add' := MonoidalSupercategory.whiskerLeft_add (R := k) _
  map_smul' := MonoidalSupercategory.whiskerLeft_smul (R := k) _

/-- The old algebra inclusion on positions two onwards; coefficients are unchanged. -/
def insert (i : I) (v w : List I) : hom D Sc cutoff v w →ₗ[k]
    hom D Sc cutoff (i :: v) (i :: w) :=
  TensorProduct.map LinearMap.id (affineInsert D Sc i v w)

@[simp] theorem insert_tmul (i : I) {v w : List I}
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) :
    insert D Sc cutoff i v w (a ⊗ₜ[k] f) = a ⊗ₜ[k] affineInsert D Sc i v w f := rfl

private theorem induction_hom {v w : List I} {P : hom D Sc cutoff v w → Prop}
    (x : hom D Sc cutoff v w) (zero : P 0)
    (tmul : ∀ (p q : ZMod 2) (a : (obj D Sc cutoff v).fst ⟶ (obj D Sc cutoff w).fst)
      (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)),
      a ∈ parity (R := k) _ _ p → f ∈ parity (R := k) _ _ q → P (BoxProd.tmulHom a f))
    (add : ∀ x y, P x → P y → P (x + y)) : P x :=
  BoxProd.induction_on_homogeneous (P := P) x zero tmul add

theorem insert_comp (i : I) {v w z : List I}
    (f : hom D Sc cutoff v w) (g : hom D Sc cutoff w z) :
    insert D Sc cutoff i v z (f ≫ g) =
      insert D Sc cutoff i v w f ≫ insert D Sc cutoff i w z g := by
  induction f using induction_hom D Sc cutoff with
  | zero => simp only [Limits.zero_comp, map_zero]
  | add f f' hf hf' => simp only [Preadditive.add_comp, map_add, hf, hf']
  | tmul p q a f ha hf =>
    induction g using induction_hom D Sc cutoff with
    | zero => simp only [Limits.comp_zero, map_zero]
    | add g g' hg hg' => simp only [Preadditive.comp_add, map_add, hg, hg']
    | tmul r s b g hb hg =>
      have hi : affineInsert D Sc i w z g ∈ parity (R := k) _ _ s :=
        MonoidalSupercategory.whiskerLeft_mem ((pres D Sc).obj (ob D [i])) hg
      rw [BoxProd.tmulHom_comp_tmulHom ha f b hg, map_zsmul]
      change koszulSign p s • BoxProd.tmulHom
        (X := obj D Sc cutoff (i :: v)) (Y := obj D Sc cutoff (i :: z))
        (a ≫ b) (affineInsert D Sc i v z (f ≫ g)) =
        BoxProd.tmulHom (X := obj D Sc cutoff (i :: v)) (Y := obj D Sc cutoff (i :: w))
          a (affineInsert D Sc i v w f) ≫
        BoxProd.tmulHom (X := obj D Sc cutoff (i :: w)) (Y := obj D Sc cutoff (i :: z))
          b (affineInsert D Sc i w z g)
      rw [BoxProd.tmulHom_comp_tmulHom
        (X := obj D Sc cutoff (i :: v)) (Y := obj D Sc cutoff (i :: w))
        (Z := obj D Sc cutoff (i :: z)) ha _ b hi]
      congr 2
      exact MonoidalSupercategory.whiskerLeft_comp (R := k) _ f g

@[simp] theorem insert_id (i : I) (v : List I) :
    insert D Sc cutoff i v v (𝟙 _) = 𝟙 _ := by
  change (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
    ((pres D Sc).obj (ob D [i]) ◁ 𝟙 ((pres D Sc).obj (ob D v))) = _
  exact congrArg (fun f => (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] f)
    (MonoidalSupercategory.whiskerLeft_id (R := k) ((pres D Sc).obj (ob D [i]))
      ((pres D Sc).obj (ob D v)))

/-- The actual first-position cyclotomic relation in the finite coefficient category. -/
def relation (j : I) (v : List I) : hom D Sc cutoff (j :: v) (j :: v) :=
  if h : D.parity j = 1 then
    (elvQuotientFunctor D Sc cutoff).map (elvCyclotomic D Sc ⟨j, h⟩ v (cutoff j))
  else (elvQuotientFunctor D Sc cutoff).map (evenCyclotomic D Sc j v (cutoff j))

/-- The two-sided cyclotomic ideal belongs to the OLD category only. -/
def ideal (v w : List I) : Submodule k (hom D Sc cutoff v w) :=
  Submodule.span k {f | ∃ j t,
    ∃ a : hom D Sc cutoff v (j :: t), ∃ b : hom D Sc cutoff (j :: t) w,
      a ≫ relation D Sc cutoff j t ≫ b = f}

/-- Matrix component of H e(i,β) / H F₂ R₁(β)e(i,β).
Only the right factor is old; the final factor is an arbitrary enlarged affine Hom. -/
def relations (i : I) (v w : List I) : Submodule k (hom D Sc cutoff (i :: v) w) :=
  Submodule.span k {f | ∃ t, ∃ r : hom D Sc cutoff v t,
    r ∈ ideal D Sc cutoff v t ∧ ∃ h : hom D Sc cutoff (i :: t) w,
      insert D Sc cutoff i v t r ≫ h = f}

abbrev Target (i : I) (v w : List I) :=
  hom D Sc cutoff (i :: v) w ⧸ relations D Sc cutoff i v w

def projection (i : I) (v w : List I) : hom D Sc cutoff (i :: v) w →ₗ[k]
    Target D Sc cutoff i v w := (relations D Sc cutoff i v w).mkQ

theorem projection_old_ideal (i : I) {v t w : List I}
    {r : hom D Sc cutoff v t} (hr : r ∈ ideal D Sc cutoff v t)
    (h : hom D Sc cutoff (i :: t) w) :
    projection D Sc cutoff i v w (insert D Sc cutoff i v t r ≫ h) = 0 := by
  change (relations D Sc cutoff i v w).mkQ _ = 0
  exact (Submodule.Quotient.mk_eq_zero (relations D Sc cutoff i v w)).mpr
    (Submodule.subset_span ⟨t, r, hr, h, rfl⟩)

theorem relation_mem (j : I) (t : List I) :
    relation D Sc cutoff j t ∈ ideal D Sc cutoff (j :: t) (j :: t) := by
  apply Submodule.subset_span
  exact ⟨j, t, 𝟙 _, 𝟙 _, by simp⟩

theorem projection_relation (i j : I) (t w : List I)
    (h : hom D Sc cutoff (i :: j :: t) w) :
    projection D Sc cutoff i (j :: t) w
      (insert D Sc cutoff i _ _ (relation D Sc cutoff j t) ≫ h) = 0 :=
  projection_old_ideal D Sc cutoff i (relation_mem D Sc cutoff j t) h

theorem ideal_comp {v t w : List I} {r : hom D Sc cutoff v t}
    (hr : r ∈ ideal D Sc cutoff v t) (b : hom D Sc cutoff t w) :
    r ≫ b ∈ ideal D Sc cutoff v w := by
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨j, s, a, c, rfl⟩ := hr
    exact Submodule.subset_span ⟨j, s, a, c ≫ b, by simp only [Category.assoc]⟩
  | zero => simp
  | add r s _ _ hr hs => exact (by
      rw [Preadditive.add_comp]; exact Submodule.add_mem _ hr hs)
  | smul c r _ hr => exact (by
      rw [Linear.smul_comp]; exact Submodule.smul_mem _ c hr)

theorem comp_ideal {v t w : List I} (a : hom D Sc cutoff v t)
    {r : hom D Sc cutoff t w} (hr : r ∈ ideal D Sc cutoff t w) :
    a ≫ r ∈ ideal D Sc cutoff v w := by
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨j, s, b, c, rfl⟩ := hr
    exact Submodule.subset_span ⟨j, s, a ≫ b, c, by simp only [Category.assoc]⟩
  | zero => simp
  | add r s _ _ hr hs => exact (by
      rw [Preadditive.comp_add]; exact Submodule.add_mem _ hr hs)
  | smul c r _ hr => exact (by
      rw [Linear.comp_smul]; exact Submodule.smul_mem _ c hr)

/-- The ambient action is only on the left (postcomposition in diagram order). -/
theorem relations_comp (i : I) {v t w : List I}
    {r : hom D Sc cutoff (i :: v) t} (hr : r ∈ relations D Sc cutoff i v t)
    (h : hom D Sc cutoff t w) : r ≫ h ∈ relations D Sc cutoff i v w := by
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨s, b, hb, a, rfl⟩ := hr
    exact Submodule.subset_span ⟨s, b, hb, a ≫ h, by simp only [Category.assoc]⟩
  | zero => simp
  | add r s _ _ hr hs => exact (by
      rw [Preadditive.add_comp]; exact Submodule.add_mem _ hr hs)
  | smul c r _ hr => exact (by
      rw [Linear.smul_comp]; exact Submodule.smul_mem _ c hr)

/-- Left H action on the quotient, with no closure under arbitrary right H factors. -/
def act (i : I) {v t w : List I} (h : hom D Sc cutoff t w) :
    Target D Sc cutoff i v t →ₗ[k] Target D Sc cutoff i v w :=
  (relations D Sc cutoff i v t).mapQ (relations D Sc cutoff i v w)
    (Linear.rightComp k _ h) (fun _ hr => relations_comp D Sc cutoff i hr h)

private theorem dot_pow_mem (w : List I) (r : ℕ) {p : ZMod 2}
    (hp : dotE D Sc w r ∈ parity (R := k) _ _ p) (n : ℕ) :
    (dotE D Sc w r ^ n : End _) ∈ parity (R := k) _ _ (n • p) := by
  induction n with
  | zero => simpa only [pow_zero, zero_nsmul, End.one_def] using id_mem (R := k) _
  | succ n ih => simpa only [pow_succ, End.mul_def, succ_nsmul, add_comm] using comp_mem hp ih

private theorem polynomial_mem (w : List I) (r N : ℕ) (c : Fin (N + 1) → SKM.SYM D k)
    (p P : ZMod 2) (hp : dotE D Sc w r ∈ parity (R := k) _ _ p)
    (hc : ∀ j, SKM.SYM.polynomialExteriorEquiv D k (c j) ∈
      SKM.SYM.polynomialExteriorParity D k (P - j.val • p)) :
    coefficientDotPolynomial D Sc w r N c ∈ parity (R := k) _ _ P := by
  apply Submodule.sum_mem
  intro j _
  have h := BoxProd.tmul_mem_parity
    (X := coefficientObj D Sc w) (Y := coefficientObj D Sc w)
    (hc j) (dot_pow_mem D Sc w r hp j.val)
  change sourceCoefficientHom D Sc (c j) (dotE D Sc w r ^ j.val) ∈
    parity (R := k) _ _ (P - j.val • p + j.val • p) at h
  rw [sub_add_cancel] at h
  exact h

/-- The entire polynomial has its total parity, including all exterior coefficients. -/
theorem relation_mem_parity (j : I) (v : List I) :
    relation D Sc cutoff j v ∈ parity (R := k) _ _ ((cutoff j : ZMod 2) * D.parity j) := by
  unfold relation
  split_ifs with hj
  · apply elvQuotientMap_mem
    rw [← elvDotPolynomial_first]
    unfold elvDotPolynomial
    rw [hj, mul_one]
    exact polynomial_mem D Sc _ _ _ _ _ _
      (positionedDot_parity D Sc [] v j)
      (SKM.SYM.elvMonicCoefficient_mem_parity D ⟨j, hj⟩ _)
  · have he : D.parity j = 0 := (parity_eq_zero_or_one (D.parity j)).resolve_right hj
    apply elvQuotientMap_mem
    have hpoly : evenCyclotomic D Sc j v (cutoff j) =
        coefficientDotPolynomial D Sc (j :: v) 0 (cutoff j)
          (SKM.SYM.evenMonicCoefficient D k j (cutoff j)) := by
      unfold evenCyclotomic deformedCyclotomic coefficientDotPolynomial
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      simp only [dotE_pow, firstDotPower, List.map_replicate]
    rw [hpoly, he, mul_zero]
    apply polynomial_mem D Sc _ _ _ _ 0 0
    · have h := positionedDot_parity D Sc [] v j
      rw [he] at h
      exact h
    · intro a
      simp only [nsmul_zero, sub_self, SKM.SYM.evenMonicCoefficient, map_smul]
      apply Submodule.smul_mem
      cases cutoff j - a.val with
      | zero => simpa only [SKM.SYM.evenCyclotomicCoefficient, map_one] using
          (SetLike.GradedOne.one_mem : (1 : SKM.SYM.PolynomialExterior D k) ∈
            SKM.SYM.polynomialExteriorParity D k 0)
      | succ n => exact SKM.SYM.polynomialExterior_e_mem_even D k j n

/-- Total parity preserves the old ideal, rather than twisting only its dots. -/
theorem twist_ideal (p : ZMod 2) {v w : List I} {r : hom D Sc cutoff v w}
    (hr : r ∈ ideal D Sc cutoff v w) : twist k p r ∈ ideal D Sc cutoff v w := by
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨j, s, a, b, rfl⟩ := hr
    rw [twist_comp, twist_comp, twist_of_mem p (relation_mem_parity D Sc cutoff j s),
      Linear.smul_comp, Linear.comp_smul]
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨j, s, twist k p a, twist k p b, rfl⟩
  | zero => simpa only [map_zero] using (ideal D Sc cutoff v w).zero_mem
  | add r s _ _ hr hs => simpa only [map_add] using Submodule.add_mem _ hr hs
  | smul c r _ hr => simpa only [map_smul] using Submodule.smul_mem _ c hr

abbrev Old (v w : List I) := hom D Sc cutoff v w ⧸ ideal D Sc cutoff v w

/-- The total-parity automorphism on the old cyclotomic quotient. -/
def oldTwist (p : ZMod 2) (v w : List I) : Old D Sc cutoff v w →ₗ[k] Old D Sc cutoff v w :=
  (ideal D Sc cutoff v w).mapQ (ideal D Sc cutoff v w) (twist k p)
    (fun _ hr => twist_ideal D Sc cutoff p hr)

/-- h ⊗ πᵖ[b] maps to [h ξ(φᵖ(b))]. This is the signed balanced quotient map. -/
def pair (p : ZMod 2) (i : I) {v t w : List I} (h : hom D Sc cutoff (i :: t) w) :
    Old D Sc cutoff v t →ₗ[k] Target D Sc cutoff i v w :=
  (ideal D Sc cutoff v t).liftQ
    ((projection D Sc cutoff i v w).comp
      ((Linear.rightComp k _ h).comp ((insert D Sc cutoff i v t).comp (twist k p))))
    (fun _ hr => projection_old_ideal D Sc cutoff i (twist_ideal D Sc cutoff p hr) h)

@[simp] theorem pair_mk (p : ZMod 2) (i : I) {v t w : List I}
    (h : hom D Sc cutoff (i :: t) w) (b : hom D Sc cutoff v t) :
    pair D Sc cutoff p i h ((ideal D Sc cutoff v t).mkQ b) =
      projection D Sc cutoff i v w (insert D Sc cutoff i v t (twist k p b) ≫ h) := rfl

/-- Full signed balance, before choosing homogeneous representatives. In algebra order:
h ξ(r) ⊗ πᵖb = h ⊗ πᵖ(φᵖ(r)b). -/
theorem pair_balance (p : ZMod 2) (i : I) {v s t w : List I}
    (h : hom D Sc cutoff (i :: t) w) (r : hom D Sc cutoff s t)
    (b : hom D Sc cutoff v s) :
    pair D Sc cutoff p i (insert D Sc cutoff i s t r ≫ h) ((ideal D Sc cutoff v s).mkQ b) =
      pair D Sc cutoff p i h ((ideal D Sc cutoff v t).mkQ (b ≫ twist k p r)) := by
  simp only [pair_mk, twist_comp, twist_twist, insert_comp, Category.assoc]

/-- Every quotient class is the signed pairing with the old identity class. -/
theorem pair_id (p : ZMod 2) (i : I) {v w : List I}
    (h : hom D Sc cutoff (i :: v) w) :
    pair D Sc cutoff p i h ((ideal D Sc cutoff v v).mkQ (𝟙 _)) =
      projection D Sc cutoff i v w h := by
  rw [pair_mk, twist_id, insert_id, Category.id_comp]

/-- The quotient projection is surjective, with no flatness hypothesis. -/
theorem projection_surjective (i : I) (v w : List I) :
    Function.Surjective (projection D Sc cutoff i v w) := Submodule.mkQ_surjective _

@[simp] theorem act_projection (i : I) {v t w : List I}
    (h : hom D Sc cutoff t w) (x : hom D Sc cutoff (i :: v) t) :
    act D Sc cutoff i h (projection D Sc cutoff i v t x) =
      projection D Sc cutoff i v w (x ≫ h) := rfl

theorem act_id (i : I) {v w : List I} (x : Target D Sc cutoff i v w) :
    act D Sc cutoff i (𝟙 _) x = x := by
  obtain ⟨x, rfl⟩ := projection_surjective D Sc cutoff i v w x
  rw [act_projection, Category.comp_id]

theorem act_comp (i : I) {v s t w : List I} (f : hom D Sc cutoff s t)
    (g : hom D Sc cutoff t w) (x : Target D Sc cutoff i v s) :
    act D Sc cutoff i g (act D Sc cutoff i f x) = act D Sc cutoff i (f ≫ g) x := by
  obtain ⟨x, rfl⟩ := projection_surjective D Sc cutoff i v s x
  simp only [act_projection, Category.assoc]

theorem oldTwist_twice (p : ZMod 2) (v w : List I) (b : Old D Sc cutoff v w) :
    oldTwist D Sc cutoff p v w (oldTwist D Sc cutoff p v w b) = b := by
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v w).mkQ_surjective b
  change (ideal D Sc cutoff v w).mkQ (twist k p (twist k p b)) = _
  rw [twist_twist]

end OddMath.QuiverHecke.ELV
end

end

section

/-!
# The signed balanced tensor for the old ELV quotient

The quotient comparison of `DeformedGlobalQP.md` §1, with the full exterior
coefficient algebra. The tensor is the coend of the coefficient-category
Homs with the old cyclotomic quotient. Its balance twists the old action by
total parity. `balancedEquiv` identifies it with `ELV.Target`, by pairing
and insertion of the old identity class, without flatness assumptions.
This is the quotient comparison needed for right PBW coordinates; those
coordinates and moving-polynomial cancellation are not asserted here.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct DirectSum Classical
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The old quotient action, twisted on the acting morphism by total parity. -/
def oldCompose (p : ZMod 2) {v s t : List I} (r : hom D Sc cutoff s t) :
    Old D Sc cutoff v s →ₗ[k] Old D Sc cutoff v t :=
  (ideal D Sc cutoff v s).mapQ (ideal D Sc cutoff v t)
    (Linear.rightComp k _ (twist k p r))
    (fun _ hb => ideal_comp D Sc cutoff hb _)

@[simp] theorem oldCompose_mk (p : ZMod 2) {v s t : List I}
    (r : hom D Sc cutoff s t) (b : hom D Sc cutoff v s) :
    oldCompose D Sc cutoff p r ((ideal D Sc cutoff v s).mkQ b) =
      (ideal D Sc cutoff v t).mkQ (b ≫ twist k p r) := rfl

/-- Ordinary module tensors, indexed by the intermediate old word. -/
abbrev TensorSum (i : I) (v w : List I) :=
  ⨁ t : List I, hom D Sc cutoff (i :: t) w ⊗[k] Old D Sc cutoff v t

/-- A pure tensor in the summand specified by its old intermediate word. -/
def tensorIn (i : I) {v t w : List I} (h : hom D Sc cutoff (i :: t) w)
    (b : Old D Sc cutoff v t) : TensorSum D Sc cutoff i v w :=
  DirectSum.lof k (List I) (fun t => hom D Sc cutoff (i :: t) w ⊗[k]
    Old D Sc cutoff v t) t (h ⊗ₜ[k] b)

/-- Only old-category balance is imposed, with the prescribed total-parity twist. -/
def balanceRelations (p : ZMod 2) (i : I) (v w : List I) :
    Submodule k (TensorSum D Sc cutoff i v w) :=
  Submodule.span k {z | ∃ s t, ∃ h : hom D Sc cutoff (i :: t) w,
    ∃ r : hom D Sc cutoff s t, ∃ b : Old D Sc cutoff v s,
      tensorIn D Sc cutoff i (insert D Sc cutoff i s t r ≫ h) b -
        tensorIn D Sc cutoff i h (oldCompose D Sc cutoff p r b) = z}

/-- The balanced tensor with the full old ELV coefficient module. -/
abbrev BalancedTensor (p : ZMod 2) (i : I) (v w : List I) :=
  TensorSum D Sc cutoff i v w ⧸ balanceRelations D Sc cutoff p i v w

def balancedTmul (p : ZMod 2) (i : I) {v t w : List I}
    (h : hom D Sc cutoff (i :: t) w) (b : Old D Sc cutoff v t) :
    BalancedTensor D Sc cutoff p i v w :=
  (balanceRelations D Sc cutoff p i v w).mkQ (tensorIn D Sc cutoff i h b)

theorem balancedTmul_balance (p : ZMod 2) (i : I) {v s t w : List I}
    (h : hom D Sc cutoff (i :: t) w) (r : hom D Sc cutoff s t)
    (b : Old D Sc cutoff v s) :
    balancedTmul D Sc cutoff p i (insert D Sc cutoff i s t r ≫ h) b =
      balancedTmul D Sc cutoff p i h (oldCompose D Sc cutoff p r b) := by
  apply sub_eq_zero.mp
  rw [balancedTmul, balancedTmul, ← map_sub]
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (Submodule.subset_span ⟨s, t, h, r, b, rfl⟩)

private def pairBilinear (p : ZMod 2) (i : I) (v t w : List I) :
    hom D Sc cutoff (i :: t) w →ₗ[k]
      Old D Sc cutoff v t →ₗ[k] Target D Sc cutoff i v w where
  toFun := pair D Sc cutoff p i
  map_add' h h' := by
    apply LinearMap.ext
    intro b
    obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective b
    simp only [LinearMap.add_apply, pair_mk, Preadditive.comp_add, map_add]
  map_smul' c h := by
    apply LinearMap.ext
    intro b
    obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective b
    simp only [LinearMap.smul_apply, pair_mk, Linear.comp_smul, map_smul,
      RingHom.id_apply]

private def tensorSumPair (p : ZMod 2) (i : I) (v w : List I) :
    TensorSum D Sc cutoff i v w →ₗ[k] Target D Sc cutoff i v w :=
  DirectSum.toModule k (List I) _
    (fun t => TensorProduct.lift (pairBilinear D Sc cutoff p i v t w))

private theorem tensorSumPair_in (p : ZMod 2) (i : I) {v t w : List I}
    (h : hom D Sc cutoff (i :: t) w) (b : Old D Sc cutoff v t) :
    tensorSumPair D Sc cutoff p i v w (tensorIn D Sc cutoff i h b) =
      pair D Sc cutoff p i h b := by
  simp [tensorSumPair, tensorIn, pairBilinear]

/-- The pairing descends through the signed old-category balance relations. -/
def balancedForward (p : ZMod 2) (i : I) (v w : List I) :
    BalancedTensor D Sc cutoff p i v w →ₗ[k] Target D Sc cutoff i v w :=
  (balanceRelations D Sc cutoff p i v w).liftQ (tensorSumPair D Sc cutoff p i v w) (by
    apply Submodule.span_le.mpr
    rintro _ ⟨s, t, h, r, b, rfl⟩
    change tensorSumPair D Sc cutoff p i v w _ = 0
    rw [map_sub, tensorSumPair_in, tensorSumPair_in, sub_eq_zero]
    obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v s).mkQ_surjective b
    exact pair_balance D Sc cutoff p i h r b)

@[simp] theorem balancedForward_tmul (p : ZMod 2) (i : I) {v t w : List I}
    (h : hom D Sc cutoff (i :: t) w) (b : Old D Sc cutoff v t) :
    balancedForward D Sc cutoff p i v w (balancedTmul D Sc cutoff p i h b) =
      pair D Sc cutoff p i h b := tensorSumPair_in D Sc cutoff p i h b

private def identityTensor (p : ZMod 2) (i : I) (v w : List I) :
    hom D Sc cutoff (i :: v) w →ₗ[k] BalancedTensor D Sc cutoff p i v w :=
  (balanceRelations D Sc cutoff p i v w).mkQ.comp
    ((DirectSum.lof k (List I) _ v).comp
      ((TensorProduct.mk k _ _).flip ((ideal D Sc cutoff v v).mkQ (𝟙 _))))

private theorem identityTensor_in (p : ZMod 2) (i : I) {v w : List I}
    (h : hom D Sc cutoff (i :: v) w) :
    identityTensor D Sc cutoff p i v w h =
      balancedTmul D Sc cutoff p i h ((ideal D Sc cutoff v v).mkQ (𝟙 _)) := rfl

private theorem identityTensor_kills (p : ZMod 2) (i : I) (v w : List I) :
    relations D Sc cutoff i v w ≤ LinearMap.ker (identityTensor D Sc cutoff p i v w) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨t, r, hr, h, rfl⟩
  change identityTensor D Sc cutoff p i v w _ = 0
  rw [identityTensor_in, balancedTmul_balance, oldCompose_mk, Category.id_comp]
  have hz : (ideal D Sc cutoff v t).mkQ (twist k p r) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (twist_ideal D Sc cutoff p hr)
  rw [hz]
  simp [balancedTmul, tensorIn]

/-- The inverse inserts the old identity class; only the old ideal is killed. -/
def balancedBackward (p : ZMod 2) (i : I) (v w : List I) :
    Target D Sc cutoff i v w →ₗ[k] BalancedTensor D Sc cutoff p i v w :=
  (relations D Sc cutoff i v w).liftQ (identityTensor D Sc cutoff p i v w)
    (identityTensor_kills D Sc cutoff p i v w)

@[simp] theorem balancedBackward_projection (p : ZMod 2) (i : I) {v w : List I}
    (h : hom D Sc cutoff (i :: v) w) :
    balancedBackward D Sc cutoff p i v w (projection D Sc cutoff i v w h) =
      balancedTmul D Sc cutoff p i h ((ideal D Sc cutoff v v).mkQ (𝟙 _)) := rfl

theorem balancedForward_backward (p : ZMod 2) (i : I) (v w : List I)
    (z : Target D Sc cutoff i v w) :
    balancedForward D Sc cutoff p i v w (balancedBackward D Sc cutoff p i v w z) = z := by
  obtain ⟨h, rfl⟩ := projection_surjective D Sc cutoff i v w z
  rw [balancedBackward_projection, balancedForward_tmul, pair_id]

private theorem backward_forward_tmul (p : ZMod 2) (i : I) {v t w : List I}
    (h : hom D Sc cutoff (i :: t) w) (b : Old D Sc cutoff v t) :
    balancedBackward D Sc cutoff p i v w
      (balancedForward D Sc cutoff p i v w (balancedTmul D Sc cutoff p i h b)) =
        balancedTmul D Sc cutoff p i h b := by
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective b
  rw [balancedForward_tmul, pair_mk, balancedBackward_projection,
    balancedTmul_balance, oldCompose_mk, Category.id_comp, twist_twist]

theorem balancedBackward_forward (p : ZMod 2) (i : I) (v w : List I)
    (z : BalancedTensor D Sc cutoff p i v w) :
    balancedBackward D Sc cutoff p i v w (balancedForward D Sc cutoff p i v w z) = z := by
  obtain ⟨z, rfl⟩ := (balanceRelations D Sc cutoff p i v w).mkQ_surjective z
  induction z using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | of t z =>
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul h b => exact backward_forward_tmul D Sc cutoff p i h b

/-- The full-coefficient signed balanced tensor is the old-only cyclotomic target.
No independence or tensor comparison is assumed. -/
def balancedEquiv (p : ZMod 2) (i : I) (v w : List I) :
    BalancedTensor D Sc cutoff p i v w ≃ₗ[k] Target D Sc cutoff i v w :=
  LinearEquiv.ofLinearMap (balancedForward D Sc cutoff p i v w)
    (balancedBackward D Sc cutoff p i v w)
    (LinearMap.ext (balancedForward_backward D Sc cutoff p i v w))
    (LinearMap.ext (balancedBackward_forward D Sc cutoff p i v w))

@[simp] theorem balancedEquiv_tmul (p : ZMod 2) (i : I) {v t w : List I}
    (h : hom D Sc cutoff (i :: t) w) (b : hom D Sc cutoff v t) :
    balancedEquiv D Sc cutoff p i v w
      (balancedTmul D Sc cutoff p i h ((ideal D Sc cutoff v t).mkQ b)) =
        projection D Sc cutoff i v w (insert D Sc cutoff i v t (twist k p b) ≫ h) :=
  balancedForward_tmul D Sc cutoff p i h _

end OddMath.QuiverHecke.ELV
end

end
