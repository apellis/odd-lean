/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.BoundedCyclicRecovery
import OddMath.QuiverHecke.UpwardMatchingIndependence
import OddMath.SKM.UpwardNondegeneracyReduction

/-! # Signed bounded recovery from a vacuum evaluation

This module formalizes §4 of `docs/Nondegeneracy/SwappedNondegeneracy.md`
(evaluation of the vacuum, bubble substitution and signed bounded recovery)
and its composition with the existing reductions of §5–6, for the
Brundan–Ellis super Kac–Moody presentation.

`SwappedVacuumEvaluation` packages exactly the properties of the swapped
action that the recovery argument uses, at one external weight `μ`, one
upward word pair and one joint coefficient/PBW degree bound `d`:

* a cyclic module with a source action and an action of the upward Hom
  space respecting source composition, and a vacuum vector;
* a raw coefficient action of the abstract coefficient algebra `SYM`;
* a coefficient substitution `θ`, an algebra automorphism of `SYM` which
  preserves the coefficient-weight filtration, such that the source-placed
  normalized bubbles `betaSYM` act as the raw coefficients composed with `θ`;
* a quotient `K` of the coefficient-extended Hom space, contained in the
  span of PBW monomials of degree at least a bound exceeding `d`;
* a placement isomorphism `σ` preserving the degree-`d` window;
* a coordinate map to the quotient by `K` with the literal evaluation
  identity `coord(act(α f)(raw(b) vac)) = q_K(σ(b ⊗ f))`.

Over a field these data give a `BoundedCyclicRecovery`
(`SwappedVacuumEvaluation.toBoundedCyclicRecovery`):
`recover = q ∘ θ⁻¹ ∘ σ⁻¹ ∘ incl ∘ L_d ∘ coord`, where `L_d` is a linear left
inverse of `q_K` on the window. The recovered identity holds before taking
any quotient, so the target quotient `q` is the standard first-boundary
ELV quotient `ELVRelationSpan` at any cutoff for which it is injective on
the window. The conclusion `nondegeneracy_of_vacuum_evaluations` is the
field theorem `NondegeneracyConjecture cs` conditional on these data at
every equal-weight upward pair, weight and degree.

No vacuum evaluation is constructed here, and the explicit substitution
and placement sign of the written proof are not yet instantiated.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
open scoped Classical TensorProduct
universe u

section CommRing
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

/-- A linear map of `SYM` preserves the coefficient-weight filtration. -/
def PreservesCoefficientWeight (θ : SKM.SYM D k →ₗ[k] SKM.SYM D k) : Prop :=
  ∀ n : ℕ, ∀ x ∈ SKM.SYM.CoefficientAtMost D k n, θ x ∈ SKM.SYM.CoefficientAtMost D k n

/-- Substitute coefficients through an automorphism of `SYM`, leaving the
affine factor unchanged. -/
def coefficientSubstitution (θ : SKM.SYM D k ≃ₐ[k] SKM.SYM D k) (t t' : List I) :
    (coefficientObj D Sc t ⟶ coefficientObj D Sc t') ≃ₗ[k]
      (coefficientObj D Sc t ⟶ coefficientObj D Sc t') :=
  (sourceTensorEquiv D Sc t t').symm.trans
    ((TensorProduct.congr θ.toLinearEquiv (LinearEquiv.refl k _)).trans
      (sourceTensorEquiv D Sc t t'))

@[simp] theorem coefficientSubstitution_source (θ : SKM.SYM D k ≃ₐ[k] SKM.SYM D k)
    {t t' : List I} (a : SKM.SYM D k)
    (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :
    coefficientSubstitution D Sc θ t t' (sourceCoefficientHom D Sc a f) =
      sourceCoefficientHom D Sc (θ a) f := by
  rw [← sourceTensorEquiv_tmul, ← sourceTensorEquiv_tmul]
  simp only [coefficientSubstitution, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply]
  rfl

/-- A coefficient of weight at most `n` times a PBW normal form of length `l`
lies in the window of degree `n + l`. -/
theorem sourceCoefficientHom_mem_extendedAtMost {t t' : List I} {n : ℕ} {a : SKM.SYM D k}
    (ha : a ∈ SKM.SYM.CoefficientAtMost D k n) (i : NFIdx t t') {d : ℕ}
    (hd : n + i.1.1.length ≤ d) :
    sourceCoefficientHom D Sc a (i.nf (D := D) (Sc := Sc)) ∈ ExtendedAtMost D Sc t t' d := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    rw [← extensionBasis_apply]
    apply Submodule.subset_span
    refine ⟨(b, i), ?_, rfl⟩
    change SKM.SYM.coefficientWeight D b + i.1.1.length ≤ d
    have : SKM.SYM.coefficientWeight D b ≤ n := hb
    omega
  | zero =>
    rw [← sourceTensorEquiv_tmul, TensorProduct.zero_tmul, map_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [← sourceTensorEquiv_tmul, TensorProduct.add_tmul, map_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [← sourceTensorEquiv_tmul, ← TensorProduct.smul_tmul', map_smul]
    exact Submodule.smul_mem _ c hx

/-- A weight-preserving substitution preserves every bounded PBW window. -/
theorem coefficientSubstitution_mem_extendedAtMost {θ : SKM.SYM D k ≃ₐ[k] SKM.SYM D k}
    (hθ : PreservesCoefficientWeight D θ.toLinearMap) {t t' : List I} {d : ℕ}
    {x : coefficientObj D Sc t ⟶ coefficientObj D Sc t'} (hx : x ∈ ExtendedAtMost D Sc t t' d) :
    coefficientSubstitution D Sc θ t t' x ∈ ExtendedAtMost D Sc t t' d := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨a, i⟩, hi, rfl⟩ := hx
    rw [extensionBasis_apply, coefficientSubstitution_source]
    have ha : SKM.SYM.coefficientBasis D k a ∈
        SKM.SYM.CoefficientAtMost D k (SKM.SYM.coefficientWeight D a) :=
      Submodule.subset_span ⟨a, Set.mem_ofPred.mpr le_rfl, rfl⟩
    exact sourceCoefficientHom_mem_extendedAtMost D Sc (hθ _ _ ha) i hi
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul c x _ hx => simpa only [map_smul] using Submodule.smul_mem _ c hx

end CommRing

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cs : SKM.CScalars Sc)

/-- The properties of the swapped action used by the vacuum recovery of
`SwappedNondegeneracy.md` §4, at one weight, word pair and degree bound.
The substitution is the triangular bubble substitution `θ`, the placement
is the ordered-source sign `σ`, and the ideal is the transformed
last-boundary ideal `K_(N,T)`; here they are retained abstractly with
exactly the properties the recovery argument needs. -/
structure SwappedVacuumEvaluation (μ : X) (t t' : List I) (d : ℕ) where
  V : Type u
  W : Type u
  [addV : AddCommGroup V]
  [moduleV : Module k V]
  [addW : AddCommGroup W]
  [moduleW : Module k W]
  sourceAct : UpwardHom D Sc μ t t →ₗ[k] Module.End k V
  act : UpwardHom D Sc μ t t' →ₗ[k] (V →ₗ[k] W)
  act_comp : ∀ (f : UpwardHom D Sc μ t t) (g : UpwardHom D Sc μ t t'),
    act (f ≫ g) = (act g).comp (sourceAct f)
  vacuum : V
  /-- The raw action of the reservoir coefficients. -/
  coefficientAct : SKM.SYM D k →ₐ[k] Module.End k V
  /-- The bubble substitution. -/
  substitution : SKM.SYM D k ≃ₐ[k] SKM.SYM D k
  substitution_weight : PreservesCoefficientWeight D substitution.toLinearMap
  /-- Source-placed normalized bubbles are substituted raw coefficients. -/
  bubbles_eq : ∀ a, sourceAct (SKM.bubAt D Sc μ (upWord t) (SKM.betaSYM cs μ a)) =
    coefficientAct (substitution a)
  /-- The quotient ideal of the vacuum coordinates. -/
  ideal : Submodule k (coefficientObj D Sc t ⟶ coefficientObj D Sc t')
  bound : ℤ
  degree_lt_bound : (d : ℤ) < bound
  ideal_le : ideal ≤ ExtendedAtLeast D Sc t t' bound
  /-- The placement sign. -/
  placement : (coefficientObj D Sc t ⟶ coefficientObj D Sc t') ≃ₗ[k]
    (coefficientObj D Sc t ⟶ coefficientObj D Sc t')
  placement_bounded : ∀ x ∈ ExtendedAtMost D Sc t t' d, placement x ∈ ExtendedAtMost D Sc t t' d
  coordinate : W →ₗ[k] ((coefficientObj D Sc t ⟶ coefficientObj D Sc t') ⧸ ideal)
  /-- Literal evaluation of the vacuum. -/
  evaluation : ∀ (b : SKM.SYM D k) (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')),
    coordinate (act ((alpha D Sc μ).map f) (coefficientAct b vacuum)) =
      ideal.mkQ (placement (sourceCoefficientHom D Sc b f))

attribute [instance] SwappedVacuumEvaluation.addV SwappedVacuumEvaluation.moduleV
  SwappedVacuumEvaluation.addW SwappedVacuumEvaluation.moduleW

namespace SwappedVacuumEvaluation
variable {D Sc cs} {μ : X} {t t' : List I} {d : ℕ}
  (E : SwappedVacuumEvaluation D Sc cs μ t t' d)

/-- The vacuum quotient restricted to the degree-`d` window. -/
def windowQuotient : ExtendedAtMost D Sc t t' d →ₗ[k]
    ((coefficientObj D Sc t ⟶ coefficientObj D Sc t') ⧸ E.ideal) :=
  E.ideal.mkQ.comp (ExtendedAtMost D Sc t t' d).subtype

theorem ker_windowQuotient : LinearMap.ker E.windowQuotient = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro x hx
  apply Subtype.ext
  have hmem : (x : coefficientObj D Sc t ⟶ coefficientObj D Sc t') ∈ E.ideal :=
    (Submodule.Quotient.mk_eq_zero _).mp hx
  exact Submodule.disjoint_def.mp
    (disjoint_extendedAtMost_extendedAtLeast D Sc E.degree_lt_bound) _ x.property
    (E.ideal_le hmem)

end SwappedVacuumEvaluation

section Field
variable {I X k : Type u} [AddCommGroup X] [Field k]
  {D : SKM.Datum I X} {Sc : SKM.Scalars D k} {cs : SKM.CScalars Sc}

namespace SwappedVacuumEvaluation
variable {μ : X} {t t' : List I} {d : ℕ} (E : SwappedVacuumEvaluation D Sc cs μ t t' d)

/-- A linear left inverse `L_d` of the vacuum quotient on the window. -/
def windowSplitting : ((coefficientObj D Sc t ⟶ coefficientObj D Sc t') ⧸ E.ideal) →ₗ[k]
    ExtendedAtMost D Sc t t' d :=
  Classical.choose (E.windowQuotient.exists_leftInverse_of_injective E.ker_windowQuotient)

theorem windowSplitting_mk (x : coefficientObj D Sc t ⟶ coefficientObj D Sc t')
    (hx : x ∈ ExtendedAtMost D Sc t t' d) :
    (E.windowSplitting (E.ideal.mkQ x) : coefficientObj D Sc t ⟶ coefficientObj D Sc t') = x := by
  have h := Classical.choose_spec
    (E.windowQuotient.exists_leftInverse_of_injective E.ker_windowQuotient)
  have := LinearMap.congr_fun h ⟨x, hx⟩
  exact congrArg Subtype.val this

/-- The signed bounded recovery
`q ∘ θ⁻¹ ∘ σ⁻¹ ∘ incl ∘ L_d ∘ coord`, into the standard ELV quotient at any cutoff. -/
def recover (cutoff : I → ℕ) : E.W →ₗ[k]
    ((coefficientObj D Sc t ⟶ coefficientObj D Sc t') ⧸ ELVRelationSpan D Sc cutoff t t') :=
  (ELVRelationSpan D Sc cutoff t t').mkQ ∘ₗ
    (coefficientSubstitution D Sc E.substitution t t').symm.toLinearMap ∘ₗ
    E.placement.symm.toLinearMap ∘ₗ (ExtendedAtMost D Sc t t' d).subtype ∘ₗ
    E.windowSplitting ∘ₗ E.coordinate

/-- Recovery returns the bounded coefficient exactly, before any quotient. -/
theorem recover_coordinates (cutoff : I → ℕ) (a : SKM.SYM D k)
    (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t'))
    (hf : sourceCoefficientHom D Sc a f ∈ ExtendedAtMost D Sc t t' d) :
    E.recover cutoff (E.act ((alpha D Sc μ).map f)
        ((E.coefficientAct.comp E.substitution.toAlgHom) a E.vacuum)) =
      (ELVRelationSpan D Sc cutoff t t').mkQ (sourceCoefficientHom D Sc a f) := by
  have hθ : sourceCoefficientHom D Sc (E.substitution a) f ∈ ExtendedAtMost D Sc t t' d := by
    rw [← coefficientSubstitution_source]
    exact coefficientSubstitution_mem_extendedAtMost D Sc E.substitution_weight hf
  have hσ := E.placement_bounded _ hθ
  simp only [recover, LinearMap.coe_comp, Function.comp_apply, AlgHom.coe_comp,
    AlgEquiv.coe_toAlgHom, E.evaluation, E.windowSplitting_mk _ hσ, Submodule.subtype_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  congr 1
  rw [LinearEquiv.symm_apply_eq, coefficientSubstitution_source]

/-- The vacuum evaluation yields bounded cyclic recovery at every cutoff. -/
def toBoundedCyclicRecovery (cutoff : I → ℕ) :
    BoundedCyclicRecovery D Sc cs μ t t' d cutoff where
  V := E.V
  W := E.W
  sourceAct := E.sourceAct
  act := E.act
  act_comp := E.act_comp
  vacuum := E.vacuum
  bubbles := E.coefficientAct.comp E.substitution.toAlgHom
  bubbles_eq a := (E.bubbles_eq a).symm
  reservoir := E.coefficientAct.comp E.substitution.toAlgHom
  elementary _ _ := rfl
  exterior _ := rfl
  recover := E.recover cutoff
  affine_coordinates a f hf := E.recover_coordinates cutoff a f hf

end SwappedVacuumEvaluation

/-- Vacuum evaluations at every degree give upward coefficient injectivity. -/
theorem upwardCoefficientMap_injective_of_vacuum_evaluations (μ : X) (t t' : List I)
    (h : ∀ d, Nonempty (SwappedVacuumEvaluation D Sc cs μ t t' d)) :
    Function.Injective (upwardCoefficientMap D Sc cs μ t t') := by
  apply upwardCoefficientMap_injective_of_bounded_cyclic_recovery D Sc cs μ t t'
  intro d
  obtain ⟨E⟩ := h d
  refine ⟨fun _ => d + 2 * t.length.choose 2 + 1, d + 2 * t.length.choose 2 + 1,
    fun _ => le_rfl, by omega, ⟨E.toBoundedCyclicRecovery _⟩⟩

/-- **Conditional field theorem.** Over a field, vacuum evaluations of the
swapped action at every equal-weight upward word pair, external weight and
degree bound imply the full nondegeneracy conjecture. -/
theorem nondegeneracy_of_vacuum_evaluations
    (h : ∀ (t t' : List I), SKM.wt D 0 (SKM.ups t) = SKM.wt D 0 (SKM.ups t') →
      ∀ (μ : X) (d : ℕ), Nonempty (SwappedVacuumEvaluation D Sc cs μ t t' d)) :
    SKM.NondegeneracyConjecture cs := by
  apply SKM.nondegeneracy_of_upward_independence cs
  apply upward_independence_of_coefficientMap D Sc cs
  intro t t' hw μ
  exact upwardCoefficientMap_injective_of_vacuum_evaluations μ t t' (h t t' hw μ)

end Field

end OddMath.QuiverHecke
