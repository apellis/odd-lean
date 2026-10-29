/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BubbleCoefficientGrading
import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientCategory
import StringDiagrams.Super.GSBim

/-! # Integer-graded full ELV coefficients and their bounded truncations

`DeformedGradedAction.md` §1 and the ELV coefficient relations (3.24)–(3.27).
The existing `ELVCoefficientAlgebra` becomes a genuine `GSuperAlg`: its
integer degree is the symmetrizer degree, while its original exterior parity
is retained. The further quotient by `coefficientIdeal N` is homogeneous in
both gradings. For finitely many colours, the proved degree/weight estimate
supplies an upper integer support bound. Low-weight injectivity preserves
nonzero odd coefficients. This is only the coefficient/vacuum algebra, not
positive-content cyclotomic finiteness, a factor action, or nondegeneracy.

The private descent arguments are spelled separately for `ℤ` and `ZMod 2`
to keep their canonical grading-index structures fixed during elaboration.
-/

noncomputable section
open scoped Classical
namespace OddMath.SKM.SYM
variable {k A B : Type*} [CommRing k] [Ring A] [Algebra k A] [Ring B] [Algebra k B]
private theorem coefficient_span_proj_mem (G : ℤ → Submodule k A) [GradedAlgebra G]
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

variable (G : ℤ → Submodule k A) [GradedAlgebra G]
  (q : A →ₐ[k] B) (hq : Function.Surjective q)
  (hker : ∀ x, q x = 0 → ∀ n, q (GradedAlgebra.proj G n x) = 0)

private def quotientDegreeProj (n : ℤ) : B →ₗ[k] B :=
  ((LinearMap.ker q.toLinearMap).liftQ
    (q.toLinearMap.comp (GradedAlgebra.proj G n)) (fun x hx => hker x hx n)).comp
    (q.toLinearMap.quotKerEquivOfSurjective hq).symm.toLinearMap

private theorem quotientDegreeProj_apply (n : ℤ) (x : A) :
    quotientDegreeProj G q hq hker n (q x) = q (GradedAlgebra.proj G n x) := by
  unfold quotientDegreeProj
  change (LinearMap.ker q.toLinearMap).liftQ
    (q.toLinearMap.comp (GradedAlgebra.proj G n)) (fun x hx => hker x hx n)
    ((q.toLinearMap.quotKerEquivOfSurjective hq).symm (q.toLinearMap x)) = _
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

private theorem quotientDegreeProj_mem {n m : ℤ} {x : B}
    (hx : x ∈ (G m).map q.toLinearMap) :
    quotientDegreeProj G q hq hker n x = if m = n then x else 0 := by
  obtain ⟨a, ha, rfl⟩ := hx
  change quotientDegreeProj G q hq hker n (q a) = if m = n then q a else 0
  rw [quotientDegreeProj_apply, GradedAlgebra.proj_apply]
  split_ifs with h
  · subst n
    rw [DirectSum.decompose_of_mem_same G ha]
  · rw [DirectSum.decompose_of_mem_ne G ha h, map_zero]

/-- The image grading of a surjective map with homogeneous kernel. -/
@[instance_reducible]
private def quotientDegreeGrading : GradedAlgebra (fun n => (G n).map q.toLinearMap) := by
  have hi : DirectSum.IsInternal (fun n => (G n).map q.toLinearMap) := by
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
      intro s v hv he n hn
      have hh := congrArg (quotientDegreeProj G q hq hker n) he
      rw [map_sum, map_zero] at hh
      have hh' : (∑ i ∈ s, quotientDegreeProj G q hq hker n (v i)) = v n := by
        calc
          _ = ∑ i ∈ s, if i = n then v i else 0 :=
            Finset.sum_congr rfl (fun i hi => quotientDegreeProj_mem G q hq hker (hv i hi))
          _ = v n := by simp [hn]
      exact hh'.symm.trans hh
    · rw [← Submodule.map_iSup, (DirectSum.Decomposition.isInternal G).submodule_iSup_eq_top]
      rw [Submodule.map_top]
      exact LinearMap.range_eq_top.mpr hq
  exact { hi.chooseDecomposition with
    one_mem := ⟨1, SetLike.GradedOne.one_mem, map_one q⟩
    mul_mem := by
      intro m n x y hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨a * b, SetLike.mul_mem_graded ha hb, map_mul q a b⟩ }

end OddMath.SKM.SYM

namespace OddMath.SKM.SYM
variable {k A B : Type*} [CommRing k] [Ring A] [Algebra k A] [Ring B] [Algebra k B]
variable (G : ZMod 2 → Submodule k A) [GradedAlgebra G]
  (q : A →ₐ[k] B) (hq : Function.Surjective q)
  (hker : ∀ x, q x = 0 → ∀ n, q (GradedAlgebra.proj G n x) = 0)

private def quotientParityProj (n : ZMod 2) : B →ₗ[k] B :=
  ((LinearMap.ker q.toLinearMap).liftQ
    (q.toLinearMap.comp (GradedAlgebra.proj G n)) (fun x hx => hker x hx n)).comp
    (q.toLinearMap.quotKerEquivOfSurjective hq).symm.toLinearMap

private theorem quotientParityProj_apply (n : ZMod 2) (x : A) :
    quotientParityProj G q hq hker n (q x) = q (GradedAlgebra.proj G n x) := by
  unfold quotientParityProj
  change (LinearMap.ker q.toLinearMap).liftQ
    (q.toLinearMap.comp (GradedAlgebra.proj G n)) (fun x hx => hker x hx n)
    ((q.toLinearMap.quotKerEquivOfSurjective hq).symm (q.toLinearMap x)) = _
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

private theorem quotientParityProj_mem {n m : ZMod 2} {x : B}
    (hx : x ∈ (G m).map q.toLinearMap) :
    quotientParityProj G q hq hker n x = if m = n then x else 0 := by
  obtain ⟨a, ha, rfl⟩ := hx
  change quotientParityProj G q hq hker n (q a) = if m = n then q a else 0
  rw [quotientParityProj_apply, GradedAlgebra.proj_apply]
  split_ifs with h
  · subst n
    rw [DirectSum.decompose_of_mem_same G ha]
  · rw [DirectSum.decompose_of_mem_ne G ha h, map_zero]

/-- The image grading of a surjective map with homogeneous kernel. -/
@[instance_reducible]
private def quotientParityGrading : GradedAlgebra (fun n => (G n).map q.toLinearMap) := by
  have hi : DirectSum.IsInternal (fun n => (G n).map q.toLinearMap) := by
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
      intro s v hv he n hn
      have hh := congrArg (quotientParityProj G q hq hker n) he
      rw [map_sum, map_zero] at hh
      have hh' : (∑ i ∈ s, quotientParityProj G q hq hker n (v i)) = v n := by
        calc
          _ = ∑ i ∈ s, if i = n then v i else 0 :=
            Finset.sum_congr rfl (fun i hi => quotientParityProj_mem G q hq hker (hv i hi))
          _ = v n := by simp [hn]
      exact hh'.symm.trans hh
    · rw [← Submodule.map_iSup, (DirectSum.Decomposition.isInternal G).submodule_iSup_eq_top]
      rw [Submodule.map_top]
      exact LinearMap.range_eq_top.mpr hq
  exact { hi.chooseDecomposition with
    one_mem := ⟨1, SetLike.GradedOne.one_mem, map_one q⟩
    mul_mem := by
      intro m n x y hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨a * b, SetLike.mul_mem_graded ha hb, map_mul q a b⟩ }

end OddMath.SKM.SYM

namespace OddMath.SKM.SYM
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : Datum I X) (sy : Symmetrizer D)

local instance : GradedAlgebra (coefficientDegreePart D k sy) := coefficientDegreeGradedAlgebra D k sy

/-- The exact ELV ideal, including the even-cutoff top relation, is integer homogeneous. -/
theorem elvCoefficientIdeal_degree (cutoff : I → ℕ) {x : SYM D k}
    (hx : x ∈ elvCoefficientIdeal D k cutoff) (n : ℤ) :
    GradedAlgebra.proj (coefficientDegreePart D k sy) n x ∈ elvCoefficientIdeal D k cutoff :=
  coefficient_span_proj_mem (k := k) (A := SYM D k) (coefficientDegreePart D k sy)
    {a | ELVCoefficientRelation D k cutoff a}
    (fun _ hx => elvCoefficientRelation_degree D k sy hx) hx n

/-- Integer degree on the existing ELV coefficient algebra. -/
def elvCoefficientDegree (cutoff : I → ℕ) (n : ℤ) :
    Submodule k (ELVCoefficientAlgebra (k := k) D cutoff) :=
  (coefficientDegreePart D k sy n).map (elvCoefficientQuotient D cutoff).toLinearMap

instance elvCoefficientDegreeGrading (cutoff : I → ℕ) :
    GradedAlgebra (elvCoefficientDegree (k := k) D sy cutoff) :=
  quotientDegreeGrading (k := k) (A := SYM D k) (coefficientDegreePart D k sy) (elvCoefficientQuotient D cutoff)
    (RingCon.mkₐ_surjective (α := k) _) (by
      intro x hx n
      apply elvCoefficientQuotient_eq_zero
      exact elvCoefficientIdeal_degree D sy cutoff (Quotient.exact hx) n)

/-- An additional homogeneous weight truncation, not a claim that elementary
rank truncation bounds the surviving polynomial powers. -/
def truncatedELVCoefficientIdeal (cutoff : I → ℕ) (N : ℕ) : TwoSidedIdeal (SYM D k) :=
  elvCoefficientIdeal D k cutoff ⊔ coefficientIdeal D k N

abbrev TruncatedELVCoefficientAlgebra (cutoff : I → ℕ) (N : ℕ) :=
  (truncatedELVCoefficientIdeal (k := k) D cutoff N).ringCon.Quotient

def truncatedELVCoefficientQuotient (cutoff : I → ℕ) (N : ℕ) :
    SYM D k →ₐ[k] TruncatedELVCoefficientAlgebra (k := k) D cutoff N :=
  (truncatedELVCoefficientIdeal D cutoff N).ringCon.mkₐ k

/-- The bounded algebra is a further quotient of the existing ELV algebra. -/
def elvCoefficientTruncation (cutoff : I → ℕ) (N : ℕ) :
    ELVCoefficientAlgebra (k := k) D cutoff →ₐ[k] TruncatedELVCoefficientAlgebra (k := k) D cutoff N :=
  (elvCoefficientIdeal D k cutoff).ringCon.liftₐ (truncatedELVCoefficientQuotient D cutoff N) (by
    intro a b hab
    apply Quotient.sound
    exact (TwoSidedIdeal.rel_iff _ _ _).mpr
      (TwoSidedIdeal.mem_sup_left ((TwoSidedIdeal.rel_iff _ _ _).mp hab)))

@[simp] theorem elvCoefficientTruncation_mk (cutoff : I → ℕ) (N : ℕ) (a : SYM D k) :
    elvCoefficientTruncation D cutoff N (elvCoefficientQuotient D cutoff a) =
      truncatedELVCoefficientQuotient D cutoff N a := rfl

theorem truncatedELVCoefficientIdeal_degree (cutoff : I → ℕ) (N : ℕ) {x : SYM D k}
    (hx : x ∈ truncatedELVCoefficientIdeal D cutoff N) (n : ℤ) :
    GradedAlgebra.proj (coefficientDegreePart D k sy) n x ∈ truncatedELVCoefficientIdeal D cutoff N := by
  obtain ⟨a, ha, b, hb, rfl⟩ := TwoSidedIdeal.mem_sup.mp hx
  rw [map_add]
  exact TwoSidedIdeal.mem_sup.mpr ⟨_, elvCoefficientIdeal_degree D sy cutoff ha n,
    _, coefficientIdeal_degree D k sy N hb n, rfl⟩

def truncatedELVCoefficientDegree (cutoff : I → ℕ) (N : ℕ) (n : ℤ) :
    Submodule k (TruncatedELVCoefficientAlgebra (k := k) D cutoff N) :=
  (coefficientDegreePart D k sy n).map (truncatedELVCoefficientQuotient D cutoff N).toLinearMap

instance truncatedELVCoefficientDegreeGrading (cutoff : I → ℕ) (N : ℕ) :
    GradedAlgebra (truncatedELVCoefficientDegree (k := k) D sy cutoff N) :=
  quotientDegreeGrading (k := k) (A := SYM D k) (coefficientDegreePart D k sy) (truncatedELVCoefficientQuotient D cutoff N)
    (RingCon.mkₐ_surjective (α := k) _) (by
      intro x hx n
      apply Quotient.sound
      exact truncatedELVCoefficientIdeal_degree D sy cutoff N (Quotient.exact hx) n)

/-- Upper support vanishing follows from the proved degree/weight estimate. -/
theorem truncatedELVCoefficientDegree_eq_bot (cutoff : I → ℕ) (N : ℕ)
    (M : ℤ) (hM : 0 ≤ M)
    (hbound : ∀ a, coefficientDegree D sy a ≤ M * coefficientWeight D a)
    (n : ℤ) (hn : M * N < n) :
    truncatedELVCoefficientDegree (k := k) D sy cutoff N n = ⊥ := by
  apply le_antisymm _ bot_le
  rintro _ ⟨x, hx, rfl⟩
  change truncatedELVCoefficientQuotient D cutoff N x = 0
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    apply Quotient.sound
    apply TwoSidedIdeal.mem_sup_right
    rw [mem_coefficientIdeal_iff]
    apply Submodule.subset_span
    refine ⟨a, ?_, rfl⟩
    change N ≤ coefficientWeight D a
    by_contra h
    have hw : (coefficientWeight D a : ℤ) ≤ N := by exact_mod_cast (by omega : coefficientWeight D a ≤ N)
    have hh := mul_le_mul_of_nonneg_left hw hM
    have hb := hbound a
    change coefficientDegree D sy a = n at ha
    omega
  | zero => exact map_zero _
  | add x y _ _ hx hy => simp only [map_add, hx, hy, add_zero]
  | smul c x _ hx => simp only [map_smul, hx, smul_zero]

/-- Finite colour support provides an upper support bound on this coefficient quotient. -/
theorem truncatedELVCoefficientDegree_bounded [Finite I] (cutoff : I → ℕ) (N : ℕ) :
    ∃ b : ℤ, ∀ n, b < n → truncatedELVCoefficientDegree (k := k) D sy cutoff N n = ⊥ := by
  obtain ⟨M, hM, hb⟩ := exists_coefficientDegree_bound D sy
  exact ⟨M * N, fun n hn => truncatedELVCoefficientDegree_eq_bot D sy cutoff N M hM hb n hn⟩

/-- Low-weight coefficients survive both the ELV relations and the further truncation. -/
theorem truncatedELVCoefficient_quotient_injective {cutoff : I → ℕ} {d N : ℕ}
    (hd : ∀ i, d ≤ cutoff i) (hN : d < N) :
    Function.Injective (fun x : CoefficientAtMost D k d =>
      truncatedELVCoefficientQuotient D cutoff N (x : SYM D k)) := by
  intro x y hxy
  apply Subtype.ext
  apply sub_eq_zero.mp
  have hi : truncatedELVCoefficientIdeal D cutoff N ≤ coefficientIdeal D k (d + 1) := by
    apply sup_le (elvCoefficientIdeal_le_weight D k hd)
    intro a ha
    rw [mem_coefficientIdeal_iff] at ha ⊢
    exact coefficientAtLeast_antitone D k (by omega) ha
  have hh : (x : SYM D k) - y ∈ coefficientIdeal D k (d + 1) :=
    hi ((TwoSidedIdeal.rel_iff _ _ _).mp (Quotient.exact hxy))
  exact Submodule.disjoint_def.mp
    (disjoint_coefficientAtMost_coefficientAtLeast D k (Nat.lt_succ_self d)) _
    (Submodule.sub_mem _ x.property y.property) ((mem_coefficientIdeal_iff D k _ _).mp hh)

private theorem image_degree_parity {B : Type u} [Ring B] [Algebra k B]
    (q : SYM D k →ₐ[k] B) (H : ZMod 2 → Submodule k B) [GradedAlgebra H]
    (hbasis : ∀ a, q (coefficientBasis D k a) ∈ H (a.2.card : ZMod 2))
    {n : ℤ} {x : B} (p : ZMod 2)
    (hx : x ∈ (coefficientDegreePart D k sy n).map q.toLinearMap) :
    (DirectSum.decompose H x p : B) ∈ (coefficientDegreePart D k sy n).map q.toLinearMap := by
  obtain ⟨a, ha, rfl⟩ := hx
  change GradedAlgebra.proj H p (q a) ∈ _
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨b, hb, rfl⟩ := ha
    rw [GradedAlgebra.proj_apply]
    by_cases h : (b.2.card : ZMod 2) = p
    · subst p
      rw [DirectSum.decompose_of_mem_same H (hbasis b)]
      exact ⟨_, Submodule.subset_span ⟨b, hb, rfl⟩, rfl⟩
    · rw [DirectSum.decompose_of_mem_ne H (hbasis b) h]
      exact Submodule.zero_mem _
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  | smul c a _ ha => simpa only [map_smul] using Submodule.smul_mem _ c ha

/-- The existing full ELV coefficient quotient, with its original super parity
and the independent symmetrizer-dependent integer degree. -/
def elvCoefficientGSuperAlg (cutoff : I → ℕ) : StringDiagrams.GSuperAlg k where
  carrier := ELVCoefficientAlgebra D cutoff
  grading := elvCoefficientParity D cutoff
  degree := elvCoefficientDegree D sy cutoff
  decompose_mem := by
    intro n a p ha
    apply image_degree_parity D sy (elvCoefficientQuotient D cutoff)
      (elvCoefficientParity D cutoff) ?_ p ha
    intro b
    have hb := elvModelQuotient_mem D (cutoff := cutoff) (coefficientBasis_mem_parity D k b)
    simpa only [elvModelQuotient, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      AlgEquiv.symm_apply_apply] using hb

theorem truncatedELVCoefficientIdeal_parity (cutoff : I → ℕ) (N : ℕ)
    {x : PolynomialExterior D k}
    (hx : (polynomialExteriorEquiv D k).symm x ∈ truncatedELVCoefficientIdeal D cutoff N)
    (p : ZMod 2) :
    (polynomialExteriorEquiv D k).symm (GradedAlgebra.proj (polynomialExteriorParity D k) p x) ∈
      truncatedELVCoefficientIdeal D cutoff N := by
  obtain ⟨a, ha, b, hb, hab⟩ := TwoSidedIdeal.mem_sup.mp hx
  have hx' : x = polynomialExteriorEquiv D k a + polynomialExteriorEquiv D k b := by
    rw [← map_add, hab, AlgEquiv.apply_symm_apply]
  rw [hx', map_add, map_add]
  apply TwoSidedIdeal.mem_sup.mpr
  refine ⟨_, elvCoefficientIdeal_parity D cutoff ?_ p, _, coefficientIdeal_parity D k N ?_ p, rfl⟩
  · simpa only [AlgEquiv.symm_apply_apply] using ha
  · simpa only [AlgEquiv.symm_apply_apply] using hb

private def truncatedELVModelQuotient (cutoff : I → ℕ) (N : ℕ) :
    PolynomialExterior D k →ₐ[k] TruncatedELVCoefficientAlgebra (k := k) D cutoff N :=
  (truncatedELVCoefficientQuotient D cutoff N).comp (polynomialExteriorEquiv D k).symm.toAlgHom

private theorem truncatedELVModelQuotient_surjective (cutoff : I → ℕ) (N : ℕ) :
    Function.Surjective (truncatedELVModelQuotient (k := k) D cutoff N) :=
  (RingCon.mkₐ_surjective (α := k) _).comp (polynomialExteriorEquiv D k).symm.surjective

/-- Exterior parity on the further quotient, independent of integer degree. -/
def truncatedELVCoefficientParity (cutoff : I → ℕ) (N : ℕ) (p : ZMod 2) :
    Submodule k (TruncatedELVCoefficientAlgebra (k := k) D cutoff N) :=
  (polynomialExteriorParity D k p).map (truncatedELVModelQuotient D cutoff N).toLinearMap

instance truncatedELVCoefficientParityGrading (cutoff : I → ℕ) (N : ℕ) :
    GradedAlgebra (truncatedELVCoefficientParity (k := k) D cutoff N) :=
  quotientParityGrading (k := k) (polynomialExteriorParity D k)
    (truncatedELVModelQuotient D cutoff N) (truncatedELVModelQuotient_surjective D cutoff N) (by
      intro x hx p
      apply Quotient.sound
      exact truncatedELVCoefficientIdeal_parity D cutoff N (Quotient.exact hx) p)

theorem truncatedELVCoefficientBasis_mem_parity (cutoff : I → ℕ) (N : ℕ)
    (a : CoefficientIndex D) :
    truncatedELVCoefficientQuotient (k := k) D cutoff N (coefficientBasis D k a) ∈
      truncatedELVCoefficientParity D cutoff N (a.2.card : ZMod 2) := by
  refine ⟨_, coefficientBasis_mem_parity D k a, ?_⟩
  change truncatedELVCoefficientQuotient D cutoff N
    ((polynomialExteriorEquiv D k).symm (polynomialExteriorEquiv D k (coefficientBasis D k a))) = _
  rw [AlgEquiv.symm_apply_apply]

/-- A bounded coefficient/vacuum algebra, still with its exterior coefficients.
This is not a positive-content cyclotomic algebra or a full 2-action. -/
def truncatedELVCoefficientGSuperAlg (cutoff : I → ℕ) (N : ℕ) : StringDiagrams.GSuperAlg k where
  carrier := TruncatedELVCoefficientAlgebra D cutoff N
  grading := truncatedELVCoefficientParity D cutoff N
  degree := truncatedELVCoefficientDegree D sy cutoff N
  decompose_mem := image_degree_parity D sy (truncatedELVCoefficientQuotient D cutoff N)
    (truncatedELVCoefficientParity D cutoff N) (truncatedELVCoefficientBasis_mem_parity D cutoff N)

end OddMath.SKM.SYM
