/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CoefficientExtension
import OddMath.QuiverHecke.CyclotomicSeparation
import OddMath.SKM.BubbleCoefficientBasis

/-!
# Weighted separation in the coefficient-extended affine category

Research issue #345, toward Brundan–Ellis §8. Coefficient weight and native
dot-minus-crossing score are tracked together through actual Koszul composition.
No SKM action or independence hypothesis is used.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
open scoped Classical TensorProduct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

theorem oddExteriorBasis_mem_parity (s : Finset {i : I // D.parity i = 1}) :
    SKM.SYM.oddExteriorBasis D k s ∈ SKM.SYM.exteriorParity D k (s.card : ZMod 2) := by
  let : LinearOrder {i : I // D.parity i = 1} := WellOrderingRel.isWellOrder.linearOrder
  let b : Module.Basis {i : I // D.parity i = 1} k (SKM.SYM.OddModule D k) := Finsupp.basisSingleOne
  change b.ExteriorAlgebra s ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm k (SKM.SYM.OddModule D k)) _
  apply Submodule.mem_iSup_of_mem ⟨s.card, rfl⟩
  change b.ExteriorAlgebra s ∈ ExteriorAlgebra.exteriorPower k s.card (SKM.SYM.OddModule D k)
  have he := ExteriorAlgebra.basis_eq_coe_basis b (Set.powersetCard.ofCard (rfl : s.card = s.card))
  simp only [Set.powersetCard.ofCard] at he
  rw [he]
  exact Subtype.property _

theorem coefficientBasis_mem_parity (a : SKM.SYM.CoefficientIndex D) :
    SKM.SYM.polynomialExteriorEquiv D k (SKM.SYM.coefficientBasis D k a) ∈
      SKM.SYM.polynomialExteriorParity D k (a.2.card : ZMod 2) := by
  rw [SKM.SYM.coefficientBasis_projection]
  change _ ∈ (SKM.SYM.exteriorParity D k (a.2.card : ZMod 2)).baseChange (MvPolynomial (I × ℕ) k)
  exact Submodule.tmul_mem_baseChange_of_mem _ (oddExteriorBasis_mem_parity D a.2)

theorem word_mem_some_parity {t t' : List I} (gs : List PG) (h : SChain t (pl t gs) t') :
    ∃ p : ZMod 2, cl D Sc t t' gs h ∈ Supercategory.parity (R := k) _ _ p :=
  ⟨_, Presentation.diag_mem_homDeg' (degree_parity_mkD D _ _)⟩

/-- Total coefficient weight plus the effective dot-minus-crossing score. -/
def ExtendedScore (t t' : List I) (s : ℤ) :
    Submodule k (coefficientObj D Sc t ⟶ coefficientObj D Sc t') :=
  Submodule.span k {f | ∃ a : SKM.SYM.CoefficientIndex D, ∃ gs h,
    s ≤ (SKM.SYM.coefficientWeight D a : ℤ) + positionedScore t.length gs ∧
      sourceCoefficientHom D Sc (SKM.SYM.coefficientBasis D k a) (cl D Sc t t' gs h) = f}

theorem sourceWord_mem_extendedScore {t t' : List I} (a : SKM.SYM.CoefficientIndex D)
    (gs : List PG) (h : SChain t (pl t gs) t') {s : ℤ}
    (hs : s ≤ (SKM.SYM.coefficientWeight D a : ℤ) + positionedScore t.length gs) :
    sourceCoefficientHom D Sc (SKM.SYM.coefficientBasis D k a) (cl D Sc t t' gs h) ∈
      ExtendedScore D Sc t t' s := Submodule.subset_span ⟨a, gs, h, hs, rfl⟩

@[simp] theorem sourceCoefficientHom_zero {t t' : List I}
    (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :
    sourceCoefficientHom D Sc 0 f = 0 := by
  change SKM.SYM.polynomialExteriorEquiv D k 0 ⊗ₜ[k] f = 0
  simp

@[simp] theorem sourceCoefficientHom_smul {t t' : List I} (c : k) (a : SKM.SYM D k)
    (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :
    sourceCoefficientHom D Sc (c • a) f = c • sourceCoefficientHom D Sc a f := by
  change SKM.SYM.polynomialExteriorEquiv D k (c • a) ⊗ₜ[k] f =
    c • (SKM.SYM.polynomialExteriorEquiv D k a ⊗ₜ[k] f)
  rw [map_smul]
  exact (TensorProduct.smul_tmul' _ _ _).symm

 theorem sourceCoefficientHom_comp {t t' t'' : List I} {p q : ZMod 2}
    {a : SKM.SYM D k}
    (ha : SKM.SYM.polynomialExteriorEquiv D k a ∈ SKM.SYM.polynomialExteriorParity D k p)
    (b : SKM.SYM D k)
    (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t'))
    {g : (pres D Sc).obj (ob D t') ⟶ (pres D Sc).obj (ob D t'')}
    (hg : g ∈ Supercategory.parity (R := k) _ _ q) :
    sourceCoefficientHom D Sc a f ≫ sourceCoefficientHom D Sc b g =
      Supercategory.koszulSign p q • sourceCoefficientHom D Sc (b * a) (f ≫ g) := by
  unfold sourceCoefficientHom
  rw [coefficientHom_comp D Sc ha _ _ hg, map_mul]

 theorem sourceWord_comp_mem {t t₁ t' : List I} (a b : SKM.SYM.CoefficientIndex D)
    (gs hs : List PG) (hg : SChain t (pl t gs) t₁) (hh : SChain t₁ (pl t₁ hs) t')
    {m n : ℤ} (hm : m ≤ (SKM.SYM.coefficientWeight D a : ℤ) + positionedScore t.length gs)
    (hn : n ≤ (SKM.SYM.coefficientWeight D b : ℤ) + positionedScore t₁.length hs) :
    sourceCoefficientHom D Sc (SKM.SYM.coefficientBasis D k a) (cl D Sc t t₁ gs hg) ≫
      sourceCoefficientHom D Sc (SKM.SYM.coefficientBasis D k b) (cl D Sc t₁ t' hs hh) ∈
      ExtendedScore D Sc t t' (m + n) := by
  obtain ⟨q, hq⟩ := word_mem_some_parity D Sc hs hh
  rw [sourceCoefficientHom_comp D Sc (coefficientBasis_mem_parity D a) _ _ hq]
  suffices hprod : sourceCoefficientHom D Sc
      (SKM.SYM.coefficientBasis D k b * SKM.SYM.coefficientBasis D k a)
      (cl D Sc t t₁ gs hg ≫ cl D Sc t₁ t' hs hh) ∈ ExtendedScore D Sc t t' (m + n) by
    simpa only [Int.cast_smul_eq_zsmul] using
      (ExtendedScore D Sc t t' (m + n)).smul_mem
        (Supercategory.koszulSign (a.2.card : ZMod 2) q : k) hprod
  by_cases hd : Disjoint b.2 a.2
  · obtain ⟨c, hc⟩ := SKM.SYM.coefficientBasis_mul_scalar D k hd
    rw [hc, sourceCoefficientHom_smul, cl_comp]
    apply Submodule.smul_mem
    apply sourceWord_mem_extendedScore
    rw [SKM.SYM.coefficientWeight_mul D hd]
    simp only [Nat.cast_add, positionedScore_append]
    have hlen := length_of_sChain hg
    rw [hlen] at hn
    omega
  · rw [SKM.SYM.coefficientBasis_mul_zero D k hd, sourceCoefficientHom_zero]
    exact Submodule.zero_mem _

/-- The weighted filtration is multiplicative for actual signed categorical
composition, including independent odd coefficients and mixed-colour words. -/
theorem extendedScore_comp {t t₁ t' : List I} {m n : ℤ}
    {f : coefficientObj D Sc t ⟶ coefficientObj D Sc t₁}
    {g : coefficientObj D Sc t₁ ⟶ coefficientObj D Sc t'}
    (hf : f ∈ ExtendedScore D Sc t t₁ m) (hg : g ∈ ExtendedScore D Sc t₁ t' n) :
    f ≫ g ∈ ExtendedScore D Sc t t' (m + n) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, gs, hs, hm, rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨b, ht, hu, hn, rfl⟩ := hg
      exact sourceWord_comp_mem D Sc a b gs ht hs hu hm hn
    | zero => simp
    | add g h _ _ hg hh =>
      rw [Preadditive.comp_add]
      exact Submodule.add_mem _ hg hh
    | smul c g _ hg =>
      rw [Linear.comp_smul]
      exact Submodule.smul_mem _ c hg
  | zero => simp
  | add f h _ _ hf hh =>
    rw [Preadditive.add_comp]
    exact Submodule.add_mem _ hf hh
  | smul c f _ hf =>
    rw [Linear.smul_comp]
    exact Submodule.smul_mem _ c hf

/-- Tensor product of the independently proved coefficient and affine PBW bases. -/
def extensionBasis (t t' : List I) :
    Module.Basis (SKM.SYM.CoefficientIndex D × NFIdx t t') k
      (coefficientObj D Sc t ⟶ coefficientObj D Sc t') :=
  ((SKM.SYM.coefficientBasis D k).tensorProduct (basisNF D Sc t t')).map
    (sourceTensorEquiv D Sc t t')

@[simp] theorem extensionBasis_apply (t t' : List I) (a : SKM.SYM.CoefficientIndex D)
    (i : NFIdx t t') : extensionBasis D Sc t t' (a, i) =
      sourceCoefficientHom D Sc (SKM.SYM.coefficientBasis D k a) i.nf := by
  simp [extensionBasis]

def extensionDegree {t t' : List I} (i : SKM.SYM.CoefficientIndex D × NFIdx t t') : ℕ :=
  SKM.SYM.coefficientWeight D i.1 + i.2.1.1.length

def ExtendedAtLeast (t t' : List I) (s : ℤ) :
    Submodule k (coefficientObj D Sc t ⟶ coefficientObj D Sc t') :=
  Submodule.span k (extensionBasis D Sc t t' '' {i | s ≤ (extensionDegree D i : ℤ)})

def ExtendedAtMost (t t' : List I) (d : ℕ) :
    Submodule k (coefficientObj D Sc t ⟶ coefficientObj D Sc t') :=
  Submodule.span k (extensionBasis D Sc t t' '' {i | extensionDegree D i ≤ d})

 theorem extendedAtLeast_antitone {t t' : List I} {s r : ℤ} (h : s ≤ r) :
    ExtendedAtLeast D Sc t t' r ≤ ExtendedAtLeast D Sc t t' s :=
  Submodule.span_mono (Set.image_mono fun _ hi => h.trans hi)

@[simp] theorem sourceCoefficientHom_zero_right {t t' : List I} (a : SKM.SYM D k) :
    sourceCoefficientHom D Sc a (0 : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) = 0 := by
  change SKM.SYM.polynomialExteriorEquiv D k a ⊗ₜ[k]
    (0 : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) = 0
  exact TensorProduct.tmul_zero _ _

@[simp] theorem sourceCoefficientHom_add_right {t t' : List I} (a : SKM.SYM D k)
    (f g : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :
    sourceCoefficientHom D Sc a (f + g) = sourceCoefficientHom D Sc a f + sourceCoefficientHom D Sc a g :=
  TensorProduct.tmul_add _ _ _

@[simp] theorem sourceCoefficientHom_smul_right {t t' : List I} (a : SKM.SYM D k) (c : k)
    (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :
    sourceCoefficientHom D Sc a (c • f) = c • sourceCoefficientHom D Sc a f :=
  TensorProduct.tmul_smul _ _ _

 theorem weightedNF_coefficient_mem_high {t t' : List I} (a : SKM.SYM.CoefficientIndex D)
    {m : ℕ} {r : ℤ} {f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')}
    (hf : f ∈ WeightedNF D Sc t t' m r) :
    sourceCoefficientHom D Sc (SKM.SYM.coefficientBasis D k a) f ∈
      ExtendedAtLeast D Sc t t' ((SKM.SYM.coefficientWeight D a : ℤ) + r) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨l, hl, hfit, w, hw, hs, h, rfl⟩ := hf
    let i : NFIdx t t' := ⟨(l, w), hl, hfit, h⟩
    apply Submodule.subset_span
    refine ⟨(a, i), ?_, ?_⟩
    · change (SKM.SYM.coefficientWeight D a : ℤ) + r ≤
        ((SKM.SYM.coefficientWeight D a + l.length : ℕ) : ℤ)
      push_cast
      omega
    · exact extensionBasis_apply D Sc t t' a i
  | zero => simp
  | add f g _ _ hf hg =>
    rw [sourceCoefficientHom_add_right]
    exact Submodule.add_mem _ hf hg
  | smul c f _ hf =>
    rw [sourceCoefficientHom_smul_right]
    exact Submodule.smul_mem _ c hf

/-- Signed weighted words straighten into the genuine tensor PBW basis
without decreasing total coefficient weight plus dot-minus-crossing score. -/
theorem extendedScore_le_extendedAtLeast (t t' : List I) (s : ℤ) :
    ExtendedScore D Sc t t' s ≤ ExtendedAtLeast D Sc t t' s := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, gs, h, hs, rfl⟩
  exact extendedAtLeast_antitone D Sc hs
    (weightedNF_coefficient_mem_high D Sc a (word_mem_weightedNF D Sc gs h))

 theorem extensionBasis_mem_score (t t' : List I) (i : SKM.SYM.CoefficientIndex D × NFIdx t t') :
    extensionBasis D Sc t t' i ∈ ExtendedScore D Sc t t' (-(t.length.choose 2 : ℤ)) := by
  rcases i with ⟨a, i⟩
  rw [extensionBasis_apply]
  apply sourceWord_mem_extendedScore
  simp only [positionedScore_append]
  rw [positionedScore_dots i.2.2.1,
    positionedScore_cw (Categorification.TypeA.validWord_canWord t.length i.1.2),
    Categorification.TypeA.length_canWord]
  have := permutation_length_le_choose_two t.length i.1.2
  omega

/-- Every affine multiplier has uniformly bounded score, regardless of its
unreduced crossing count, after expanding in the actual tensor PBW basis. -/
theorem every_mem_extendedScore (t t' : List I)
    (f : coefficientObj D Sc t ⟶ coefficientObj D Sc t') :
    f ∈ ExtendedScore D Sc t t' (-(t.length.choose 2 : ℤ)) := by
  rw [← (extensionBasis D Sc t t').linearCombination_repr f, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  exact extensionBasis_mem_score D Sc t t' i

 theorem disjoint_extendedAtMost_extendedAtLeast {t t' : List I} {d : ℕ} {s : ℤ} (h : (d : ℤ) < s) :
    Disjoint (ExtendedAtMost D Sc t t' d) (ExtendedAtLeast D Sc t t' s) := by
  apply (extensionBasis D Sc t t').linearIndependent.disjoint_span_image
  rw [Set.disjoint_left]
  intro i hi hj
  simp only [Set.mem_ofPred_eq] at hi hj
  omega

/-- Two-sided relation span in a fixed strand number, generated by arbitrary
endomorphisms of weighted score at least `N`. This includes homogeneous
coefficient-valued cyclotomic polynomials once their term weights are checked. -/
def WeightedRelationSpan (t t' : List I) (N : ℕ) :
    Submodule k (coefficientObj D Sc t ⟶ coefficientObj D Sc t') :=
  Submodule.span k {f | ∃ v : List I, v.length = t.length ∧
    ∃ r : coefficientObj D Sc v ⟶ coefficientObj D Sc v, r ∈ ExtendedScore D Sc v v (N : ℤ) ∧
    ∃ a : coefficientObj D Sc t ⟶ coefficientObj D Sc v,
    ∃ b : coefficientObj D Sc v ⟶ coefficientObj D Sc t', a ≫ r ≫ b = f}

/-- All products of weighted cyclotomic relations with arbitrary genuine
coefficient-extended affine multipliers have high total PBW weight. -/
theorem weightedRelationSpan_le_extendedAtLeast (t t' : List I) (N : ℕ) :
    WeightedRelationSpan D Sc t t' N ≤
      ExtendedAtLeast D Sc t t' ((N : ℤ) - 2 * (t.length.choose 2 : ℤ)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨v, hv, r, hr, a, b, rfl⟩
  have ha := every_mem_extendedScore D Sc t v a
  have hb := every_mem_extendedScore D Sc v t' b
  have hchoose : v.length.choose 2 = t.length.choose 2 := congrArg (fun n => n.choose 2) hv
  rw [hchoose] at hb
  have hcomp := extendedScore_comp D Sc (extendedScore_comp D Sc ha hr) hb
  have he : (-(t.length.choose 2 : ℤ) + N) + -(t.length.choose 2 : ℤ) =
      (N : ℤ) - 2 * (t.length.choose 2 : ℤ) := by omega
  rw [he, Category.assoc] at hcomp
  exact extendedScore_le_extendedAtLeast D Sc t t' _ hcomp

/-- Bounded weighted separation in the actual signed coefficient-extended
category. No independence of an SKM image or existence of an SKM action is assumed. -/
theorem weighted_quotient_injective_on_extendedAtMost {t t' : List I} {d N : ℕ}
    (hN : d + 2 * t.length.choose 2 < N) :
    Function.Injective (fun x : ExtendedAtMost D Sc t t' d =>
      (WeightedRelationSpan D Sc t t' N).mkQ
        (x : coefficientObj D Sc t ⟶ coefficientObj D Sc t')) := by
  intro x y hxy
  apply Subtype.ext
  apply sub_eq_zero.mp
  have hmem : (x : coefficientObj D Sc t ⟶ coefficientObj D Sc t') - y ∈
      WeightedRelationSpan D Sc t t' N := (Submodule.Quotient.eq _).mp hxy
  exact Submodule.disjoint_def.mp
    (disjoint_extendedAtMost_extendedAtLeast D Sc (by omega)) _
    (Submodule.sub_mem _ x.property y.property)
    (weightedRelationSpan_le_extendedAtLeast D Sc t t' N hmem)

@[simp] theorem sourceCoefficientHom_add_left {t t' : List I} (a b : SKM.SYM D k)
    (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :
    sourceCoefficientHom D Sc (a + b) f = sourceCoefficientHom D Sc a f + sourceCoefficientHom D Sc b f := by
  change SKM.SYM.polynomialExteriorEquiv D k (a + b) ⊗ₜ[k] f = _
  rw [map_add]
  exact TensorProduct.add_tmul _ _ _

 theorem highCoefficient_word_mem_score {t t' : List I} {a : SKM.SYM D k} {m : ℕ}
    (ha : a ∈ SKM.SYM.CoefficientAtLeast D k m) (gs : List PG) (h : SChain t (pl t gs) t') :
    sourceCoefficientHom D Sc a (cl D Sc t t' gs h) ∈
      ExtendedScore D Sc t t' ((m : ℤ) + positionedScore t.length gs) := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨b, hb, rfl⟩ := ha
    apply sourceWord_mem_extendedScore
    simp only [Set.mem_ofPred_eq] at hb
    omega
  | zero => simp
  | add a b _ _ ha hb =>
    rw [sourceCoefficientHom_add_left]
    exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    rw [sourceCoefficientHom_smul]
    exact Submodule.smul_mem _ c ha

/-- A coefficient-valued cyclotomic polynomial in the first dot. The entry
`c j` is the coefficient of `x^j`, including its chosen sign. -/
def deformedCyclotomic (t : List I) (N : ℕ) (c : Fin (N + 1) → SKM.SYM D k) :
    coefficientObj D Sc t ⟶ coefficientObj D Sc t :=
  ∑ j : Fin (N + 1), sourceCoefficientHom D Sc (c j) (firstDotPower D Sc t j.val)

/-- The actual coefficient-valued polynomial lies in score `N` if its
coefficient of `x^j` has weight at least `N-j`. This includes independent odd
coefficients and never sets them equal or to zero. -/
theorem deformedCyclotomic_mem_score (t : List I) (N : ℕ)
    (c : Fin (N + 1) → SKM.SYM D k) (ht : 0 < t.length)
    (hc : ∀ j, c j ∈ SKM.SYM.CoefficientAtLeast D k (N - j.val)) :
    deformedCyclotomic D Sc t N c ∈ ExtendedScore D Sc t t (N : ℤ) := by
  apply Submodule.sum_mem
  intro j _
  have hm : ∀ p ∈ List.replicate j.val 0, p < t.length := by
    intro p hp
    have : p = 0 := (List.mem_replicate.mp hp).2
    omega
  have he := highCoefficient_word_mem_score D Sc (hc j)
    ((List.replicate j.val 0).map PG.dot)
    (show SChain t (pl t ((List.replicate j.val 0).map PG.dot)) t from
      by simpa only [tgt_map_dot] using sChain_pl t ((List.replicate j.val 0).map PG.dot))
  rw [positionedScore_dots hm, List.length_replicate] at he
  have hval : ((N - j.val : ℕ) : ℤ) + j.val = N := by have := j.isLt; omega
  rw [hval] at he
  exact he

/-- Such a deformed polynomial is one of the genuine generators consumed by
`weighted_quotient_injective_on_extendedAtMost`. -/
theorem deformedCyclotomic_mem_relationSpan (t : List I) (N : ℕ)
    (c : Fin (N + 1) → SKM.SYM D k) (ht : 0 < t.length)
    (hc : ∀ j, c j ∈ SKM.SYM.CoefficientAtLeast D k (N - j.val)) :
    deformedCyclotomic D Sc t N c ∈ WeightedRelationSpan D Sc t t N := by
  apply Submodule.subset_span
  exact ⟨t, rfl, deformedCyclotomic D Sc t N c, deformedCyclotomic_mem_score D Sc t N c ht hc,
    𝟙 _, 𝟙 _, by simp⟩

/-- Every actual coefficient-extended morphism has finite total PBW weight. -/
theorem exists_mem_extendedAtMost (t t' : List I)
    (f : coefficientObj D Sc t ⟶ coefficientObj D Sc t') :
    ∃ d, f ∈ ExtendedAtMost D Sc t t' d := by
  let c := (extensionBasis D Sc t t').repr f
  refine ⟨c.support.sup (extensionDegree D), ?_⟩
  rw [← (extensionBasis D Sc t t').linearCombination_repr f, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨i, Finset.le_sup (f := extensionDegree D) hi, rfl⟩

/-- The weighted deformed quotient family detects every nonzero affine
morphism with full abstract bubble coefficients. This is not yet an SKM action. -/
theorem weighted_quotients_jointly_detect {t t' : List I}
    (f : coefficientObj D Sc t ⟶ coefficientObj D Sc t')
    (hf : ∀ N, (WeightedRelationSpan D Sc t t' N).mkQ f = 0) : f = 0 := by
  obtain ⟨d, hd⟩ := exists_mem_extendedAtMost D Sc t t' f
  let N := d + 2 * t.length.choose 2 + 1
  have hinj := weighted_quotient_injective_on_extendedAtMost D Sc
    (t := t) (t' := t') (d := d) (N := N) (by omega)
  have h := hinj (a₁ := ⟨f, hd⟩) (a₂ := 0) (by simpa using hf N)
  exact congrArg Subtype.val h

end OddMath.QuiverHecke
