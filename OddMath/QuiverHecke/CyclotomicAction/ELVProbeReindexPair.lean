import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReindexTensors

/-! # Two append inductions under OLD representative changes

Brundan–Ellis (1.7)–(1.8), (1.12)–(1.14): the pair comparison is
the composite of the specified lower and upper append-adjunction
comparisons. It is even and retains both arrows of every nested tensor.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction
universe u

private theorem moduleMap_total_even
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {M N : Superfunctor k C (SVec k)} (f : M ⟶ N)
    (hf : f ∈ parity (R := k) _ _ 0) (w : A) :
    (moduleMap J f).total w = mapComponent J f 0 w := by
  change mapComponent J f 0 w + mapComponent J f 1 w = _
  have h : mapComponent J f 1 w = 0 := by
    apply hom_ext J M.toFunctor (w := w)
    intro s g b
    rw [mapComponent_tensor, Superfunctor.app_eq_zero_of_mem hf (q := 1) (by decide),
      LinearMap.zero_apply, tensor_zero_right]
    rfl
  rw [h, add_zero]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  {ν₀ μ₀ : List I} (q₀ : ν₀.Perm μ₀) (i j : I)
  {ν₁ μ₁ ν₂ μ₂ : List I}
  (a₁ : (i :: ν₀).Perm ν₁) (b₁ : (i :: μ₀).Perm μ₁) (q₁ : ν₁.Perm μ₁)
  (a₂ : (j :: ν₁).Perm ν₂) (b₂ : (j :: μ₁).Perm μ₂) (q₂ : ν₂.Perm μ₂)
local notation "J" => oldContentAppendTo D Sc cutoff ν₀ i ν₁ a₁
local notation "K" => oldContentAppendTo D Sc cutoff μ₀ i μ₁ b₁
local notation "L" => oldContentAppendTo D Sc cutoff ν₁ j ν₂ a₂
local notation "M" => oldContentAppendTo D Sc cutoff μ₁ j μ₂ b₂
local notation "R₀" => oldModuleReindex D Sc cutoff q₀
local notation "R₁" => oldModuleReindex D Sc cutoff q₁
local notation "R₂" => oldModuleReindex D Sc cutoff q₂
local notation "e₁" => oldAppendReindexIso D Sc cutoff q₀ i a₁ b₁ q₁
local notation "e₂" => oldAppendReindexIso D Sc cutoff q₁ j a₂ b₂ q₂

/-- The chosen forward append comparison with its module endpoints specified. -/
def oldAppendReindexModuleHom
    (N : Superfunctor k (OldContentCategory D Sc cutoff ν₀) (SVec k)) :
    (R₁).obj (induced J N) ⟶ induced K ((R₀).obj N) := (e₁).hom.app N

local notation "c₁" => oldAppendReindexModuleHom D Sc cutoff q₀ i a₁ b₁ q₁
local notation "c₂" => oldAppendReindexModuleHom D Sc cutoff q₁ j a₂ b₂ q₂

/-- Insert an inner tensor into the upper coend, with its raw domain specified. -/
def oldAppendReindexOuterTensorLinear
    (N : Superfunctor k (OldContentCategory D Sc cutoff ν₀) (SVec k))
    (t : OldContentCategory D Sc cutoff μ₁) (w : OldContentCategory D Sc cutoff μ₂)
    (g : (M).obj t ⟶ w) :
    Obj K ((R₀).obj N).toFunctor t →ₗ[k] Obj M (induced K ((R₀).obj N)).toFunctor w :=
  inclusion M (induced K ((R₀).obj N)).toFunctor w t ∘ₗ TensorProduct.mk k _ _ g

attribute [local irreducible] oldAppendReindexLinear oldAppendReindexModuleHom oldAppendReindexIso

/-- Compose the chosen upper and lower adjunction comparisons, without a new gauge. -/
def oldAppendPairReindexIso :
    (induction J ⋙ induction L) ⋙ R₂ ≅ R₀ ⋙ (induction K ⋙ induction M) :=
  Functor.isoWhiskerLeft (induction J) e₂ ≪≫ Functor.isoWhiskerRight e₁ (induction M)

/-- Fix both nested coend carriers before evaluating the pair comparison. -/
def oldAppendPairReindexLinear
    (N : Superfunctor k (OldContentCategory D Sc cutoff ν₀) (SVec k))
    (w : OldContentCategory D Sc cutoff μ₂) :
    Obj L (induced J N).toFunctor ((oldContentReindex D Sc cutoff q₂.symm).obj w) →ₗ[k]
      Obj M (induced K ((R₀).obj N)).toFunctor w :=
  ((oldAppendPairReindexIso D Sc cutoff q₀ i j a₁ b₁ q₁ a₂ b₂ q₂).hom.app N).total w

end OddMath.QuiverHecke

namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  {ν₀ μ₀ : List I} (q₀ : ν₀.Perm μ₀) (i j : I)
  {ν₁ μ₁ ν₂ μ₂ : List I}
  (a₁ : (i :: ν₀).Perm ν₁) (b₁ : (i :: μ₀).Perm μ₁) (q₁ : ν₁.Perm μ₁)
  (a₂ : (j :: ν₁).Perm ν₂) (b₂ : (j :: μ₁).Perm μ₂) (q₂ : ν₂.Perm μ₂)
local notation "cut" => probeCutoff D m
local notation "e" => oldAppendPairReindexIso D Sc cut q₀ i j a₁ b₁ q₁ a₂ b₂ q₂

/-- Restrict exactly the selected pair comparison to the full evaluated categories. -/
def probeAppendPairReindexIso :
    (probeEvaluatedAppendTo D Sc m ν₀ i ν₁ a₁ ⋙
      probeEvaluatedAppendTo D Sc m ν₁ j ν₂ a₂) ⋙ probeEvaluatedReindex D Sc m q₂ ≅
      probeEvaluatedReindex D Sc m q₀ ⋙
        (probeEvaluatedAppendTo D Sc m μ₀ i μ₁ b₁ ⋙
          probeEvaluatedAppendTo D Sc m μ₁ j μ₂ b₂) :=
  NatIso.ofComponents
    (fun N => ObjectProperty.isoMk (ProbeEvaluatesCoefficients D m Sc μ₂) ((e).app N.obj))
    (by
      intro N N' f
      apply InducedCategory.hom_ext
      exact (e).hom.naturality f.hom)

end OddMath.QuiverHecke
