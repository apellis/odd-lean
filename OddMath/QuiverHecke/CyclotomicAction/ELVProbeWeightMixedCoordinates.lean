import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightMixedMate

/-! # Supported mixed OLD probe weight coordinates

Brundan–Ellis (1.12): identify the prescribed source and target of the
weight mixed mate with the actual four stored-target append functors.
Every target permutation and selected predecessor is retained.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction CyclotomicAction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)

/-- The stored target permutation determined by an actual weight predecessor. -/
theorem probeOldBlockTarget_perm (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)
    (β : WeightBlocks D Λ x) (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ) :
    (i :: β.1.toList).Perm δ.1.toList := by
  apply Multiset.coe_eq_coe.mp
  rw [Multiset.coe_toList]
  change {i} + (β.1.toList : Multiset I) = δ.1
  rw [Multiset.coe_toList]
  exact congrArg Subtype.val hβ

/-- The selected block induction with its target kept as the literal output block. -/
abbrev probeOldBlockIndTo (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)
    (β : WeightBlocks D Λ x) (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ) :
    Superfunctor k (ProbeCanonicalModules D Sc m β.1) (ProbeCanonicalModules D Sc m δ.1) :=
  ⟨probeEvaluatedAppendTo D Sc m β.1.toList i δ.1.toList
    (probeOldBlockTarget_perm D i Λ h β δ hβ)⟩

theorem probeOldInductionComponent_obj_of (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)
    (β : WeightBlocks D Λ x) (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ)
    (M : ProbeOldWeightProduct D Sc m Λ x) :
    (probeOldInductionComponent D Sc m i Λ h δ).obj M =
      (probeOldBlockIndTo D Sc m i Λ h β δ hβ).obj (M β) := by
  subst δ
  exact probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β M

theorem probeOldInductionComponent_map_of (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)
    (β : WeightBlocks D Λ x) (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ)
    {M N : ProbeOldWeightProduct D Sc m Λ x} (f : M ⟶ N) :
    (probeOldInductionComponent D Sc m i Λ h δ).map f =
      eqToHom (probeOldInductionComponent_obj_of D Sc m i Λ h β δ hβ M) ≫
        (probeOldBlockIndTo D Sc m i Λ h β δ hβ).map (f β) ≫
          eqToHom (probeOldInductionComponent_obj_of D Sc m i Λ h β δ hβ N).symm := by
  subst δ
  exact probeOldInductionComponent_map_blockSucc D Sc m i Λ h β f

variable (i j : I) (Λ : X) {x₀ xj xi xu : X}
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
  (β : WeightBlocks D Λ x₀)
local notation "δj" => blockSucc D Λ j h₁ β
local notation "δi" => blockSucc D Λ i h₃ β
local notation "ε" => blockSucc D Λ j h₄ (blockSucc D Λ i h₃ β)
local notation "hComm" => blockSucc_comm D Λ i j h₁ h₂ h₃ h₄ β
local notation "hj" => probeOldBlockTarget_perm D j Λ h₁ β δj rfl
local notation "hi" => probeOldBlockTarget_perm D i Λ h₃ β δi rfl
local notation "hL" => probeOldBlockTarget_perm D i Λ h₂ δj ε hComm
local notation "hU" => probeOldBlockTarget_perm D j Λ h₄ δi ε rfl
local notation "Fj" => probeOldF D Sc m j Λ h₁
local notation "Ei" => probeOldE D Sc m i Λ h₃

/-- The supported source is the stored-target lower restriction-induction. -/
theorem probeOldWeightMixedSource_obj (M : ProbeOldWeightProduct D Sc m Λ xj) :
    (((probeOldF D Sc m j Λ h₁ ≫ probeOldE D Sc m i Λ h₃).obj M) δi) =
      (probeAppendToDistinctMateSource D Sc m β.1.toList i j hj hi).obj (M δj) :=
  probeOldInductionComponent_obj_blockSucc D Sc m i Λ h₃ β ((Fj).obj M)

/-- The supported target uses the same literal common upper block. -/
theorem probeOldWeightMixedTarget_obj (M : ProbeOldWeightProduct D Sc m Λ xj) :
    (((probeOldE D Sc m i Λ h₂ ≫ probeOldF D Sc m j Λ h₄).obj M) δi) =
      (probeAppendToDistinctMateTarget D Sc m i j hL hU).obj (M δj) := by
  exact congrArg (fun P => (probeOldBlockRes D Sc m j Λ h₄ δi).obj P)
    (probeOldInductionComponent_obj_of D Sc m i Λ h₂ δj ε hComm M)

end OddMath.QuiverHecke
