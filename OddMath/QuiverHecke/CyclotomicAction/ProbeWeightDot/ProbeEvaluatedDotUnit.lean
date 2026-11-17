import OddMath.QuiverHecke.CyclotomicAction.ProbeMixed.ProbeContentReindex
import OddMath.QuiverHecke.CyclotomicAction.ProbeVacuumCharts.ProbeCanonicalContent
import OddMath.QuiverHecke.SwappedAssembly.ProductDenominatorUnits

/-!
# Probe weight dot

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Whole signed dot unit on the evaluated old probe category

`SwappedNondegeneracy` §3 and `SwappedActionAssembly` F2 require a natural
probe-dot inverse on the actual factor category. The full scalar-evaluated
old module subcategory supplies the actual algebra-quotient inverse for
every object. Pointwise homogeneous inverses assemble into an isomorphism
of the prescribed induction superfunctor, including odd colour parity.

The hypothesis `[Fact Sc.PureNilpotent]` on declarations here is a route-only intermediate
hypothesis for parameters with pure terms: homogeneous parameters supply it
(`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction
universe u
private theorem transform_total
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ v, J.obj v ⟶ J.obj v} (hα : IsSupernatural k p α)
    (N : Superfunctor k C (SVec k)) (t : A) :
    (transformComponent hα N).total t = transformLinear hα N t := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp only [SuperNatTrans.total, transformComponent_app,
      ite_true, ite_false, zero_ne_one, one_ne_zero, add_zero, zero_add]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I) (i : I)
local notation "J" => oldContentAppend D Sc (probeCutoff D m) ν i
local notation "hDot" => probeOldContentAppendDot_supernatural D Sc m ν i
local notation "E" => probeEvaluatedInduction D Sc m ν i

/-- The chosen signed dot, retaining its whole module morphism. -/
def probeEvaluatedDotComponent (N : ProbeEvaluatedModules D Sc m ν) :
    (E).obj N ⟶ (E).obj N := ⟨transformComponent hDot N.obj⟩

theorem probeEvaluatedDotComponent_supernatural :
    IsSupernatural k (D.parity i) (F := E) (G := E)
      (probeEvaluatedDotComponent D Sc m ν i) where
  mem N := transformComponent_mem hDot N.obj
  naturality := by
    intro M N p f hf
    apply InducedCategory.hom_ext
    change f.hom ∈ parity (R := k) _ _ p at hf
    exact (transformComponent_supernatural hDot).naturality hf

/-- The whole signed dot on the actual evaluated induction functor. -/
def probeEvaluatedInductionDot :
    End (⟨E⟩ : Superfunctor k (ProbeEvaluatedModules D Sc m ν)
      (ProbeEvaluatedModules D Sc m (i :: ν))) :=
  (probeEvaluatedDotComponent_supernatural D Sc m ν i).toSuperNatTrans

theorem probeEvaluatedInductionDot_mem :
    probeEvaluatedInductionDot D Sc m ν i ∈ parity (R := k) _ _ (D.parity i) :=
  Superfunctor.IsSupernatural.toSuperNatTrans_mem
    (probeEvaluatedDotComponent_supernatural D Sc m ν i)

/-- The whole functor dot has exactly the prescribed native module component. -/
theorem probeEvaluatedInductionDot_total (N : ProbeEvaluatedModules D Sc m ν) :
    (probeEvaluatedInductionDot D Sc m ν i).total N = probeEvaluatedDotComponent D Sc m ν i N :=
  OddMath.HomogeneousSuperfunctorIso.homogeneous_total
    (F := (⟨E⟩ : Superfunctor k (ProbeEvaluatedModules D Sc m ν) (ProbeEvaluatedModules D Sc m (i :: ν))))
    (G := (⟨E⟩ : Superfunctor k (ProbeEvaluatedModules D Sc m ν) (ProbeEvaluatedModules D Sc m (i :: ν))))
    (probeEvaluatedDotComponent_supernatural D Sc m ν i) N

variable [Fintype I]

/-- Every evaluated old probe module has the prescribed dot isomorphism;
the inverse comes from the actual scalar quotient, with no inverse premise. -/
def probeEvaluatedDotModuleIso [Fact Sc.PureNilpotent] (N : ProbeEvaluatedModules D Sc m ν) :
    induced J N.obj ≅ induced J N.obj :=
  OddMath.HomogeneousSuperfunctorIso.ofBijectiveTotals
    (transformComponent hDot N.obj) (transformComponent_mem hDot N.obj) (by
      intro t
      rw [transform_total]
      change Function.Bijective (probeOldContentInductionDot D Sc m ν i N.obj t)
      have h := probeOldContentInductionDot_isUnit D Sc m ν i N.obj N.property t
      exact (Module.End.isUnit_iff _).mp h)

/-- The dot isomorphism retains the exact specified module forward. -/
theorem probeEvaluatedDotModuleIso_hom [Fact Sc.PureNilpotent] (N : ProbeEvaluatedModules D Sc m ν) :
    (probeEvaluatedDotModuleIso D Sc m ν i N).hom = transformComponent hDot N.obj :=
  OddMath.HomogeneousSuperfunctorIso.ofBijectiveTotals_hom _ _ _

/-- The pointwise inverse is a morphism of the same full evaluated category. -/
def probeEvaluatedDotIso [Fact Sc.PureNilpotent] (N : ProbeEvaluatedModules D Sc m ν) : (E).obj N ≅ (E).obj N :=
  ObjectProperty.isoMk (ProbeEvaluatesCoefficients D m Sc (i :: ν)) (probeEvaluatedDotModuleIso D Sc m ν i N)

private theorem evaluatedDotIso_hom_total [Fact Sc.PureNilpotent] (N : ProbeEvaluatedModules D Sc m ν) :
    (probeEvaluatedDotIso D Sc m ν i N).hom = (probeEvaluatedInductionDot D Sc m ν i).total N := by
  rw [probeEvaluatedInductionDot_total]
  apply InducedCategory.hom_ext
  exact probeEvaluatedDotModuleIso_hom D Sc m ν i N

/-- The actual dot inverse is natural on the entire evaluated probe category. -/
def probeEvaluatedInductionDotIso [Fact Sc.PureNilpotent] :
    (⟨E⟩ : Superfunctor k (ProbeEvaluatedModules D Sc m ν)
      (ProbeEvaluatedModules D Sc m (i :: ν))) ≅ ⟨E⟩ :=
  OddMath.HomogeneousSuperfunctorIso.ofHom
    (probeEvaluatedInductionDot D Sc m ν i) (probeEvaluatedInductionDot_mem D Sc m ν i)
    (probeEvaluatedDotIso D Sc m ν i) (evaluatedDotIso_hom_total D Sc m ν i)

@[simp] theorem probeEvaluatedInductionDotIso_hom [Fact Sc.PureNilpotent] :
    (probeEvaluatedInductionDotIso D Sc m ν i).hom = probeEvaluatedInductionDot D Sc m ν i :=
  OddMath.HomogeneousSuperfunctorIso.ofHom_hom _ _ _ _

end OddMath.QuiverHecke
end

end

section

/-! # The prescribed right adjunction on evaluated old probes

For SwappedActionAssembly F1–F2 and BE (1.10), restrict the actual balanced
unit and counit to the scalar-evaluated full categories. Their evenness
and both triangles are inherited. The whole dot unit retains the existing
native old-content induction dot, with no change of sign or adjunction.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I) (i : I)
local notation "J" => oldContentAppend D Sc (probeCutoff D m) ν i
local notation "E" => probeEvaluatedInduction D Sc m ν i
local notation "F" => probeEvaluatedRestriction D Sc m ν i

/-- The same chosen balanced unit, on the full evaluated subcategory. -/
def probeEvaluatedUnit : 𝟭 (ProbeEvaluatedModules D Sc m ν) ⟶ E ⋙ F where
  app N := ⟨(adjunction J).unit.app N.obj⟩
  naturality := by
    intro A B f
    exact InducedCategory.hom_ext ((adjunction J).unit.naturality f.hom)

/-- The same chosen multiplication counit, with every module map retained. -/
def probeEvaluatedCounit : F ⋙ E ⟶ 𝟭 (ProbeEvaluatedModules D Sc m (i :: ν)) where
  app N := ⟨(adjunction J).counit.app N.obj⟩
  naturality := by
    intro A B f
    exact InducedCategory.hom_ext ((adjunction J).counit.naturality f.hom)

/-- Restrict the actual right adjunction; both triangle identities are inherited. -/
def probeEvaluatedAdjunction : E ⊣ F where
  unit := probeEvaluatedUnit D Sc m ν i
  counit := probeEvaluatedCounit D Sc m ν i
  left_triangle_components N := InducedCategory.hom_ext ((adjunction J).left_triangle_components N.obj)
  right_triangle_components N := InducedCategory.hom_ext ((adjunction J).right_triangle_components N.obj)

theorem probeEvaluatedAdjunction_unit_mem (N : ProbeEvaluatedModules D Sc m ν) :
    (probeEvaluatedAdjunction D Sc m ν i).unit.app N ∈ parity (R := k) _ _ 0 :=
  adjunctionUnit_mem J N.obj

theorem probeEvaluatedAdjunction_counit_mem (N : ProbeEvaluatedModules D Sc m (i :: ν)) :
    (probeEvaluatedAdjunction D Sc m ν i).counit.app N ∈ parity (R := k) _ _ 0 :=
  adjunctionCounit_mem J N.obj

/-- The actual evaluated module category in the target of the swapped factors. -/
abbrev probeEvaluatedTarget (ν : List I) : PiSCat.{u,u,u+1} k :=
  letI := probeEvaluatedPiSupercategory D Sc m ν
  PiSCat.of k (ProbeEvaluatedModules D Sc m ν)

abbrev probeEvaluatedE : probeEvaluatedTarget D Sc m ν ⟶ probeEvaluatedTarget D Sc m (i :: ν) := ⟨E⟩
abbrev probeEvaluatedF : probeEvaluatedTarget D Sc m (i :: ν) ⟶ probeEvaluatedTarget D Sc m ν := ⟨F⟩

/-- The right adjunction uses precisely the restricted native unit and counit. -/
def probeEvaluatedRightAdjunction :
    SKM.SuperAdjunction (k := k) (probeEvaluatedE D Sc m ν i) (probeEvaluatedF D Sc m ν i) :=
  ordinaryEvenSuperAdjunction (probeEvaluatedE D Sc m ν i) (probeEvaluatedF D Sc m ν i)
    (probeEvaluatedAdjunction D Sc m ν i) (probeEvaluatedAdjunction_unit_mem D Sc m ν i)
    (probeEvaluatedAdjunction_counit_mem D Sc m ν i)

end OddMath.QuiverHecke
end

end

section

/-! # The prescribed adjunction for stored OLD probe contents

SwappedActionAssembly F1–F2 and BE (1.10): the full evaluated append
and restriction functors retain their specified target permutation. The
right unit, counit, evenness and triangles are the actual balanced ones.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I) (i : I) (μ : List I) (h : (i :: ν).Perm μ)
local notation "J" => oldContentAppendTo D Sc (probeCutoff D m) ν i μ h
local notation "E" => probeEvaluatedAppendTo D Sc m ν i μ h
local notation "F" => probeEvaluatedRestrictTo D Sc m ν i μ h

/-- The same chosen balanced unit, on the full evaluated subcategory. -/
def probeAppendToUnit : 𝟭 (ProbeEvaluatedModules D Sc m ν) ⟶ E ⋙ F where
  app N := ⟨(adjunction J).unit.app N.obj⟩
  naturality := by
    intro A B f
    exact InducedCategory.hom_ext ((adjunction J).unit.naturality f.hom)

/-- The same chosen multiplication counit, with every module map retained. -/
def probeAppendToCounit : F ⋙ E ⟶ 𝟭 (ProbeEvaluatedModules D Sc m μ) where
  app N := ⟨(adjunction J).counit.app N.obj⟩
  naturality := by
    intro A B f
    exact InducedCategory.hom_ext ((adjunction J).counit.naturality f.hom)

/-- Restrict the actual right adjunction; both triangle identities are inherited. -/
def probeAppendToAdjunction : E ⊣ F where
  unit := probeAppendToUnit D Sc m ν i μ h
  counit := probeAppendToCounit D Sc m ν i μ h
  left_triangle_components N := InducedCategory.hom_ext ((adjunction J).left_triangle_components N.obj)
  right_triangle_components N := InducedCategory.hom_ext ((adjunction J).right_triangle_components N.obj)

theorem probeAppendToAdjunction_unit_mem (N : ProbeEvaluatedModules D Sc m ν) :
    (probeAppendToAdjunction D Sc m ν i μ h).unit.app N ∈ parity (R := k) _ _ 0 :=
  adjunctionUnit_mem J N.obj

theorem probeAppendToAdjunction_counit_mem (N : ProbeEvaluatedModules D Sc m μ) :
    (probeAppendToAdjunction D Sc m ν i μ h).counit.app N ∈ parity (R := k) _ _ 0 :=
  adjunctionCounit_mem J N.obj

abbrev probeAppendToE : probeEvaluatedTarget D Sc m ν ⟶ probeEvaluatedTarget D Sc m μ := ⟨E⟩
abbrev probeAppendToF : probeEvaluatedTarget D Sc m μ ⟶ probeEvaluatedTarget D Sc m ν := ⟨F⟩

/-- The right adjunction uses precisely the restricted native unit and counit. -/
def probeAppendToRightAdjunction :
    SKM.SuperAdjunction (k := k) (probeAppendToE D Sc m ν i μ h) (probeAppendToF D Sc m ν i μ h) :=
  ordinaryEvenSuperAdjunction (probeAppendToE D Sc m ν i μ h) (probeAppendToF D Sc m ν i μ h)
    (probeAppendToAdjunction D Sc m ν i μ h) (probeAppendToAdjunction_unit_mem D Sc m ν i μ h)
    (probeAppendToAdjunction_counit_mem D Sc m ν i μ h)

end OddMath.QuiverHecke
end

end

section

/-! # The selected right adjunction of the global OLD probe

`SwappedActionAssembly` F1: assemble the exact balanced old append
unit and counit over all original-weight content blocks, including absent
predecessors. Both triangles and evenness are proved for all evaluated
module inputs; no factor-action or local-inversion premise is supplied.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke
open ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)

abbrev probeOldBlockAdj (β : WeightBlocks D Λ x) :
    (probeOldBlockInd D Sc m i Λ h β).toFunctor ⊣
      (probeOldBlockRes D Sc m i Λ h β).toFunctor :=
  probeAppendToAdjunction D Sc m β.1.toList i
    (blockSucc D Λ i h β).1.toList _

/-- The unit component at a block of weight `x`. -/
def probeOldWeightUnitApp (β : WeightBlocks D Λ x) (M : ProbeOldWeightProduct D Sc m Λ x) :
    M β ⟶ (probeOldBlockRes D Sc m i Λ h β).obj
      ((probeOldInductionComponent D Sc m i Λ h (blockSucc D Λ i h β)).obj M) :=
  (probeOldBlockAdj D Sc m i Λ h β).unit.app (M β) ≫
    (probeOldBlockRes D Sc m i Λ h β).map
      (eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β M).symm)

theorem probeOldWeightUnitApp_naturality (β : WeightBlocks D Λ x)
    {M M' : ProbeOldWeightProduct D Sc m Λ x} (f : M ⟶ M') :
    f β ≫ probeOldWeightUnitApp D Sc m i Λ h β M' =
      probeOldWeightUnitApp D Sc m i Λ h β M ≫ (probeOldBlockRes D Sc m i Λ h β).map
        ((probeOldInductionComponent D Sc m i Λ h (blockSucc D Λ i h β)).map f) := by
  rw [probeOldInductionComponent_map_blockSucc]
  simp only [probeOldWeightUnitApp, Superfunctor.map, Category.assoc, ← Functor.map_comp,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [Functor.map_comp, ← Adjunction.unit_naturality_assoc]

/-- The unit on weight spaces. -/
def probeOldWeightUnit : 𝟭 (ProbeOldWeightProduct D Sc m Λ x) ⟶
    probeOldEFunctor D Sc m i Λ h ⋙ (probeOldF D Sc m i Λ h).toFunctor where
  app M β := probeOldWeightUnitApp D Sc m i Λ h β M
  naturality _ _ f := funext fun β => probeOldWeightUnitApp_naturality D Sc m i Λ h β f

/-- The counit at a block with a chosen predecessor. -/
def probeOldWeightCounitVia (N : ProbeOldWeightProduct D Sc m Λ y) (β : WeightBlocks D Λ x)
    (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ) :
    (probeOldInductionComponent D Sc m i Λ h δ).obj ((probeOldF D Sc m i Λ h).obj N) ⟶ N δ := by
  subst hβ
  exact eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β _) ≫
    (probeOldBlockAdj D Sc m i Λ h β).counit.app (N (blockSucc D Λ i h β))

theorem probeOldWeightCounitVia_eq (N : ProbeOldWeightProduct D Sc m Λ y) (β β' : WeightBlocks D Λ x)
    (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ) (hβ' : blockSucc D Λ i h β' = δ) :
    probeOldWeightCounitVia D Sc m i Λ h N β δ hβ =
      probeOldWeightCounitVia D Sc m i Λ h N β' δ hβ' := by
  obtain rfl := blockSucc_injective D Λ i h (hβ.trans hβ'.symm)
  subst hβ
  rfl

open scoped Classical in
/-- The counit component at a block: through the predecessor, or zero. -/
def probeOldWeightCounitComponent (N : ProbeOldWeightProduct D Sc m Λ y) (δ : WeightBlocks D Λ y) :
    (probeOldInductionComponent D Sc m i Λ h δ).obj ((probeOldF D Sc m i Λ h).obj N) ⟶ N δ :=
  if hδ : ∃ β, blockSucc D Λ i h β = δ then
    probeOldWeightCounitVia D Sc m i Λ h N hδ.choose δ hδ.choose_spec
  else 0

theorem probeOldWeightCounitComponent_blockSucc (N : ProbeOldWeightProduct D Sc m Λ y)
    (β : WeightBlocks D Λ x) :
    probeOldWeightCounitComponent D Sc m i Λ h N (blockSucc D Λ i h β) =
      eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β
        ((probeOldF D Sc m i Λ h).obj N)) ≫
        (probeOldBlockAdj D Sc m i Λ h β).counit.app (N (blockSucc D Λ i h β)) := by
  unfold probeOldWeightCounitComponent
  split
  · rename_i hc
    exact probeOldWeightCounitVia_eq D Sc m i Λ h N _ β _ hc.choose_spec rfl
  · rename_i hc
    exact absurd (⟨β, rfl⟩ : ∃ c, blockSucc D Λ i h c = blockSucc D Λ i h β) hc

theorem probeOldWeightCounitComponent_naturality (β : WeightBlocks D Λ x)
    {N N' : ProbeOldWeightProduct D Sc m Λ y} (g : N ⟶ N') :
    (probeOldInductionComponent D Sc m i Λ h (blockSucc D Λ i h β)).map
        ((probeOldF D Sc m i Λ h).map g) ≫
      probeOldWeightCounitComponent D Sc m i Λ h N' (blockSucc D Λ i h β) =
    probeOldWeightCounitComponent D Sc m i Λ h N (blockSucc D Λ i h β) ≫
      g (blockSucc D Λ i h β) := by
  rw [probeOldInductionComponent_map_blockSucc, probeOldWeightCounitComponent_blockSucc,
    probeOldWeightCounitComponent_blockSucc]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  congr 1
  exact (probeOldBlockAdj D Sc m i Λ h β).counit_naturality (g (blockSucc D Λ i h β))

/-- The counit on weight spaces. -/
def probeOldWeightCounit : (probeOldF D Sc m i Λ h).toFunctor ⋙ probeOldEFunctor D Sc m i Λ h ⟶
    𝟭 (ProbeOldWeightProduct D Sc m Λ y) where
  app N δ := probeOldWeightCounitComponent D Sc m i Λ h N δ
  naturality N N' g := by
    funext δ
    by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
    · obtain ⟨β, rfl⟩ := hδ
      exact probeOldWeightCounitComponent_naturality D Sc m i Λ h β g
    · exact (probeOldInductionComponent_isZero D Sc m i Λ h δ hδ _).eq_of_src _ _

theorem probeOldWeight_left_triangle (β : WeightBlocks D Λ x) (M : ProbeOldWeightProduct D Sc m Λ x) :
    (probeOldInductionComponent D Sc m i Λ h (blockSucc D Λ i h β)).map
        ((probeOldWeightUnit D Sc m i Λ h).app M) ≫
      probeOldWeightCounitComponent D Sc m i Λ h ((probeOldEFunctor D Sc m i Λ h).obj M)
        (blockSucc D Λ i h β) = 𝟙 _ := by
  rw [probeOldInductionComponent_map_blockSucc, probeOldWeightCounitComponent_blockSucc]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  change eqToHom _ ≫ (probeOldBlockInd D Sc m i Λ h β).map (probeOldWeightUnitApp D Sc m i Λ h β M) ≫
    _ = _
  simp only [probeOldWeightUnitApp, Superfunctor.map, Functor.map_comp, Category.assoc]
  erw [Adjunction.counit_naturality, Adjunction.left_triangle_components_assoc]
  simp

theorem probeOldWeight_right_triangle (β : WeightBlocks D Λ x) (N : ProbeOldWeightProduct D Sc m Λ y) :
    probeOldWeightUnitApp D Sc m i Λ h β ((probeOldF D Sc m i Λ h).obj N) ≫
      (probeOldBlockRes D Sc m i Λ h β).map
        (probeOldWeightCounitComponent D Sc m i Λ h N (blockSucc D Λ i h β)) = 𝟙 _ := by
  rw [probeOldWeightCounitComponent_blockSucc]
  simp only [probeOldWeightUnitApp, Superfunctor.map, Category.assoc, ← Functor.map_comp,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  exact (probeOldBlockAdj D Sc m i Λ h β).right_triangle_components _

/-- **Induction is left adjoint to restriction on weight spaces.** -/
def probeOldWeightAdjunction :
    probeOldEFunctor D Sc m i Λ h ⊣ (probeOldF D Sc m i Λ h).toFunctor where
  unit := probeOldWeightUnit D Sc m i Λ h
  counit := probeOldWeightCounit D Sc m i Λ h
  left_triangle_components M := by
    funext δ
    by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
    · obtain ⟨β, rfl⟩ := hδ
      exact probeOldWeight_left_triangle D Sc m i Λ h β M
    · exact (probeOldInductionComponent_isZero D Sc m i Λ h δ hδ _).eq_of_src _ _
  right_triangle_components N := funext fun β => probeOldWeight_right_triangle D Sc m i Λ h β N

theorem probeOldBlockAdj_unit_mem (β : WeightBlocks D Λ x)
    (M : ProbeCanonicalModules D Sc m β.1) :
    (probeOldBlockAdj D Sc m i Λ h β).unit.app M ∈ parity (R := k) _ _ 0 :=
  probeAppendToAdjunction_unit_mem D Sc m β.1.toList i
    (blockSucc D Λ i h β).1.toList _ M

theorem probeOldBlockAdj_counit_mem (β : WeightBlocks D Λ x)
    (M : ProbeCanonicalModules D Sc m (blockSucc D Λ i h β).1) :
    (probeOldBlockAdj D Sc m i Λ h β).counit.app M ∈ parity (R := k) _ _ 0 :=
  probeAppendToAdjunction_counit_mem D Sc m β.1.toList i
    (blockSucc D Λ i h β).1.toList _ M

theorem probeOldWeightUnitApp_mem (β : WeightBlocks D Λ x) (M : ProbeOldWeightProduct D Sc m Λ x) :
    probeOldWeightUnitApp D Sc m i Λ h β M ∈ parity (R := k) _ _ 0 := by
  unfold probeOldWeightUnitApp
  rw [← zero_add (0 : ZMod 2)]
  exact comp_mem (probeOldBlockAdj_unit_mem D Sc m i Λ h β (M β))
    (IsSuperfunctor.map_mem (F := (probeOldBlockRes D Sc m i Λ h β).toFunctor)
      (eqToHom_mem_parity_zero (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β M).symm))

theorem probeOldWeightUnit_mem (M : ProbeOldWeightProduct D Sc m Λ x) :
    (probeOldWeightUnit D Sc m i Λ h).app M ∈ parity (R := k) _ _ 0 := fun β =>
  probeOldWeightUnitApp_mem D Sc m i Λ h β M

theorem probeOldWeightCounit_mem (M : ProbeOldWeightProduct D Sc m Λ y) :
    (probeOldWeightCounit D Sc m i Λ h).app M ∈ parity (R := k) _ _ 0 := fun δ => by
  by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
  · obtain ⟨β, rfl⟩ := hδ
    change probeOldWeightCounitComponent D Sc m i Λ h M (blockSucc D Λ i h β) ∈ _
    rw [probeOldWeightCounitComponent_blockSucc, ← zero_add (0 : ZMod 2)]
    exact comp_mem (eqToHom_mem_parity_zero (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β
        ((probeOldF D Sc m i Λ h).obj M)))
      (probeOldBlockAdj_counit_mem D Sc m i Λ h β (M (blockSucc D Λ i h β)))
  · rw [(probeOldInductionComponent_isZero D Sc m i Λ h δ hδ _).eq_of_src
      ((probeOldWeightCounit D Sc m i Λ h).app M δ) 0]
    exact Submodule.zero_mem _

/-- The actual OLD probe weight functors carry the prescribed even right adjunction. -/
def probeOldActionAdjunction :
    SKM.SuperAdjunction (k := k) (probeOldE D Sc m i Λ h) (probeOldF D Sc m i Λ h) :=
  ELV.ordinaryEvenSuperAdjunction (probeOldE D Sc m i Λ h) (probeOldF D Sc m i Λ h)
    (probeOldWeightAdjunction D Sc m i Λ h) (probeOldWeightUnit_mem D Sc m i Λ h)
    (probeOldWeightCounit_mem D Sc m i Λ h)

end OddMath.QuiverHecke
end

end

section

/-! # Whole signed dot unit with stored OLD probe contents

SwappedActionAssembly F2: every prescribed retargeted append induction
has its natural signed-dot inverse on all scalar-evaluated OLD modules.
Only the content certificate changes; the old coend and physical arrow
are retained. No component invertibility premise is supplied.

The hypothesis `[Fact Sc.PureNilpotent]` on declarations here is a route-only intermediate
hypothesis for parameters with pure terms: homogeneous parameters supply it
(`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction
universe u
private theorem appendTo_transform_total
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ v, J.obj v ⟶ J.obj v} (hα : IsSupernatural k p α)
    (N : Superfunctor k C (SVec k)) (t : A) :
    (transformComponent hα N).total t = transformLinear hα N t := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp only [SuperNatTrans.total, transformComponent_app,
      ite_true, ite_false, zero_ne_one, one_ne_zero, add_zero, zero_add]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I) (i : I) (μ : List I) (h : (i :: ν).Perm μ)
local notation "J" => oldContentAppendTo D Sc (probeCutoff D m) ν i μ h
/-- The unchanged physical quotient dot at the specified target content. -/
def probeAppendToDot (v : OldContentCategory D Sc (probeCutoff D m) ν) :
    (J).obj v ⟶ (J).obj v :=
  CyclotomicCrossingTensor.oldAppendDotComponent D Sc (probeCutoff D m) i v.obj

theorem probeAppendToDot_supernatural : IsSupernatural k (D.parity i) (probeAppendToDot D Sc m ν i μ h) where
  mem v := (CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc (probeCutoff D m) i).mem v.obj
  naturality hf := (CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc (probeCutoff D m) i).naturality hf
local notation "hDot" => probeAppendToDot_supernatural D Sc m ν i μ h
local notation "E" => probeEvaluatedAppendTo D Sc m ν i μ h

/-- The chosen signed dot, retaining its whole module morphism. -/
def probeAppendToDotComponent (N : ProbeEvaluatedModules D Sc m ν) :
    (E).obj N ⟶ (E).obj N := ⟨transformComponent hDot N.obj⟩

theorem probeAppendToDotComponent_supernatural :
    IsSupernatural k (D.parity i) (F := E) (G := E)
      (probeAppendToDotComponent D Sc m ν i μ h) where
  mem N := transformComponent_mem hDot N.obj
  naturality := by
    intro M N p f hf
    apply InducedCategory.hom_ext
    change f.hom ∈ parity (R := k) _ _ p at hf
    exact (transformComponent_supernatural hDot).naturality hf

/-- The whole signed dot on the actual evaluated induction functor. -/
def probeAppendToInductionDot :
    End (⟨E⟩ : Superfunctor k (ProbeEvaluatedModules D Sc m ν)
      (ProbeEvaluatedModules D Sc m μ)) :=
  (probeAppendToDotComponent_supernatural D Sc m ν i μ h).toSuperNatTrans

theorem probeAppendToInductionDot_mem :
    probeAppendToInductionDot D Sc m ν i μ h ∈ parity (R := k) _ _ (D.parity i) :=
  Superfunctor.IsSupernatural.toSuperNatTrans_mem
    (probeAppendToDotComponent_supernatural D Sc m ν i μ h)

/-- The whole functor dot has exactly the prescribed native module component. -/
theorem probeAppendToInductionDot_total (N : ProbeEvaluatedModules D Sc m ν) :
    (probeAppendToInductionDot D Sc m ν i μ h).total N = probeAppendToDotComponent D Sc m ν i μ h N :=
  OddMath.HomogeneousSuperfunctorIso.homogeneous_total
    (F := (⟨E⟩ : Superfunctor k (ProbeEvaluatedModules D Sc m ν) (ProbeEvaluatedModules D Sc m μ)))
    (G := (⟨E⟩ : Superfunctor k (ProbeEvaluatedModules D Sc m ν) (ProbeEvaluatedModules D Sc m μ)))
    (probeAppendToDotComponent_supernatural D Sc m ν i μ h) N

private theorem appendTo_dot_eq (N : Superfunctor k (OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
    (t : OldContentCategory D Sc (probeCutoff D m) μ) :
    transformLinear hDot N t = probeOldContentInductionDot D Sc m ν i N
      ((oldContentReindex D Sc (probeCutoff D m) h.symm).obj t) := rfl

variable [Fintype I]

/-- Every evaluated old probe module has the prescribed dot isomorphism;
the inverse comes from the actual scalar quotient, with no inverse premise. -/
def probeAppendToDotModuleIso [Fact Sc.PureNilpotent] (N : ProbeEvaluatedModules D Sc m ν) :
    induced J N.obj ≅ induced J N.obj :=
  OddMath.HomogeneousSuperfunctorIso.ofBijectiveTotals
    (transformComponent hDot N.obj) (transformComponent_mem hDot N.obj) (by
      intro t
      rw [appendTo_transform_total]
      rw [appendTo_dot_eq]
      have h := probeOldContentInductionDot_isUnit D Sc m ν i N.obj N.property
        ((oldContentReindex D Sc (probeCutoff D m) h.symm).obj t)
      exact (Module.End.isUnit_iff _).mp h)

/-- The dot isomorphism retains the exact specified module forward. -/
theorem probeAppendToDotModuleIso_hom [Fact Sc.PureNilpotent] (N : ProbeEvaluatedModules D Sc m ν) :
    (probeAppendToDotModuleIso D Sc m ν i μ h N).hom = transformComponent hDot N.obj :=
  OddMath.HomogeneousSuperfunctorIso.ofBijectiveTotals_hom _ _ _

/-- The pointwise inverse is a morphism of the same full evaluated category. -/
def probeAppendToDotIso [Fact Sc.PureNilpotent] (N : ProbeEvaluatedModules D Sc m ν) : (E).obj N ≅ (E).obj N :=
  ObjectProperty.isoMk (ProbeEvaluatesCoefficients D m Sc μ) (probeAppendToDotModuleIso D Sc m ν i μ h N)

private theorem appendToDotIso_hom_total [Fact Sc.PureNilpotent] (N : ProbeEvaluatedModules D Sc m ν) :
    (probeAppendToDotIso D Sc m ν i μ h N).hom = (probeAppendToInductionDot D Sc m ν i μ h).total N := by
  rw [probeAppendToInductionDot_total]
  apply InducedCategory.hom_ext
  exact probeAppendToDotModuleIso_hom D Sc m ν i μ h N

/-- The actual dot inverse is natural on the entire evaluated probe category. -/
def probeAppendToInductionDotIso [Fact Sc.PureNilpotent] :
    (⟨E⟩ : Superfunctor k (ProbeEvaluatedModules D Sc m ν)
      (ProbeEvaluatedModules D Sc m μ)) ≅ ⟨E⟩ :=
  OddMath.HomogeneousSuperfunctorIso.ofHom
    (probeAppendToInductionDot D Sc m ν i μ h) (probeAppendToInductionDot_mem D Sc m ν i μ h)
    (probeAppendToDotIso D Sc m ν i μ h) (appendToDotIso_hom_total D Sc m ν i μ h)

@[simp] theorem probeAppendToInductionDotIso_hom [Fact Sc.PureNilpotent] :
    (probeAppendToInductionDotIso D Sc m ν i μ h).hom = probeAppendToInductionDot D Sc m ν i μ h :=
  OddMath.HomogeneousSuperfunctorIso.ofHom_hom _ _ _ _

/-- Whole-functor invertibility is proved, rather than assumed componentwise. -/
theorem probeAppendToInductionDot_isUnit [Fact Sc.PureNilpotent] : IsUnit (End.of (probeAppendToInductionDot D Sc m ν i μ h)) := by
  apply (isUnit_iff_isIso _).2
  rw [← probeAppendToInductionDotIso_hom]
  infer_instance

end OddMath.QuiverHecke
end

end

section

/-! # The prescribed signed dot on the global OLD probe

`SwappedActionAssembly` F2: the actual old append dot acts on every
original-weight block. Its only nonzero parity component is the moving
colour parity. Absent predecessors contribute the zero module. No
invertibility statement is made for arbitrary unevaluated old modules.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke
open ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)

/-- The exact chosen stored-target OLD dot, without a comparison isomorphism. -/
abbrev probeOldBlockDot (β : WeightBlocks D Λ x) :=
  probeAppendToInductionDot D Sc m β.1.toList i
    (blockSucc D Λ i h β).1.toList
    (by
      apply Multiset.coe_eq_coe.mp
      rw [Multiset.coe_toList]
      change {i} + (β.1.toList : Multiset I) = (blockSucc D Λ i h β).1
      rw [Multiset.coe_toList, blockSucc_val])

theorem probeOldBlockDot_mem (β : WeightBlocks D Λ x) :
    probeOldBlockDot D Sc m i Λ h β ∈ parity (R := k)
      (probeOldBlockInd D Sc m i Λ h β) (probeOldBlockInd D Sc m i Λ h β) (D.parity i) :=
  probeAppendToInductionDot_mem D Sc m β.1.toList i
    (blockSucc D Λ i h β).1.toList _

theorem probeOldBlockDot_homogeneous (β : WeightBlocks D Λ x) :
    (probeOldBlockDot D Sc m i Λ h β).IsHomogeneous (D.parity i) :=
  Superfunctor.mem_parity_iff_isHomogeneous.1 (probeOldBlockDot_mem D Sc m i Λ h β)

/-- The dot component at a block with a chosen predecessor. -/
def probeOldWeightDotVia (p : ZMod 2) (M : ProbeOldWeightProduct D Sc m Λ x) (β : WeightBlocks D Λ x)
    (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ) :
    (probeOldInductionComponent D Sc m i Λ h δ).obj M ⟶ (probeOldInductionComponent D Sc m i Λ h δ).obj M := by
  subst hβ
  exact eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β M) ≫
    (probeOldBlockDot D Sc m i Λ h β).app p (M β) ≫
      eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β M).symm

theorem probeOldWeightDotVia_eq (p : ZMod 2) (M : ProbeOldWeightProduct D Sc m Λ x)
    (β β' : WeightBlocks D Λ x) (δ : WeightBlocks D Λ y) (hβ : blockSucc D Λ i h β = δ)
    (hβ' : blockSucc D Λ i h β' = δ) :
    probeOldWeightDotVia D Sc m i Λ h p M β δ hβ =
      probeOldWeightDotVia D Sc m i Λ h p M β' δ hβ' := by
  obtain rfl := blockSucc_injective D Λ i h (hβ.trans hβ'.symm)
  subst hβ
  rfl

open scoped Classical in
/-- The dot component at a block: through the predecessor, or zero. -/
def probeOldWeightDotComponent (p : ZMod 2) (M : ProbeOldWeightProduct D Sc m Λ x)
    (δ : WeightBlocks D Λ y) :
    (probeOldInductionComponent D Sc m i Λ h δ).obj M ⟶ (probeOldInductionComponent D Sc m i Λ h δ).obj M :=
  if hδ : ∃ β, blockSucc D Λ i h β = δ then
    probeOldWeightDotVia D Sc m i Λ h p M hδ.choose δ hδ.choose_spec
  else 0

theorem probeOldWeightDotComponent_blockSucc (p : ZMod 2) (M : ProbeOldWeightProduct D Sc m Λ x)
    (β : WeightBlocks D Λ x) :
    probeOldWeightDotComponent D Sc m i Λ h p M (blockSucc D Λ i h β) =
      eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β M) ≫
        (probeOldBlockDot D Sc m i Λ h β).app p (M β) ≫
          eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β M).symm := by
  unfold probeOldWeightDotComponent
  split
  · rename_i hc
    exact probeOldWeightDotVia_eq D Sc m i Λ h p M _ β _ hc.choose_spec rfl
  · rename_i hc
    exact absurd (⟨β, rfl⟩ : ∃ c, blockSucc D Λ i h c = blockSucc D Λ i h β) hc

theorem probeOldWeightDotComponent_mem (p : ZMod 2) (M : ProbeOldWeightProduct D Sc m Λ x)
    (δ : WeightBlocks D Λ y) :
    probeOldWeightDotComponent D Sc m i Λ h p M δ ∈ parity (R := k) _ _ p := by
  by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
  · obtain ⟨β, rfl⟩ := hδ
    rw [probeOldWeightDotComponent_blockSucc]
    have hm := comp_mem (eqToHom_mem_parity_zero
        (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β M))
      (comp_mem ((probeOldBlockDot D Sc m i Λ h β).app_mem p (M β))
        (eqToHom_mem_parity_zero (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β M).symm))
    simpa only [zero_add, add_zero] using hm
  · rw [(probeOldInductionComponent_isZero D Sc m i Λ h δ hδ M).eq_of_src
      (probeOldWeightDotComponent D Sc m i Λ h p M δ) 0]
    exact Submodule.zero_mem _

theorem probeOldWeightDotComponent_naturality (p : ZMod 2) (β : WeightBlocks D Λ x)
    {M M' : ProbeOldWeightProduct D Sc m Λ x} {q : ZMod 2} (f : M ⟶ M')
    (hf : f ∈ parity (R := k) M M' q) :
    (probeOldInductionComponent D Sc m i Λ h (blockSucc D Λ i h β)).map f ≫
        probeOldWeightDotComponent D Sc m i Λ h p M' (blockSucc D Λ i h β) =
      koszulSign p q • (probeOldWeightDotComponent D Sc m i Λ h p M (blockSucc D Λ i h β) ≫
        (probeOldInductionComponent D Sc m i Λ h (blockSucc D Λ i h β)).map f) := by
  rw [probeOldInductionComponent_map_blockSucc, probeOldWeightDotComponent_blockSucc,
    probeOldWeightDotComponent_blockSucc]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have hn := (probeOldBlockDot D Sc m i Λ h β).naturality p (f β) (hf β)
  rw [← Category.assoc ((probeOldBlockInd D Sc m i Λ h β).map (f β)), Superfunctor.map, hn,
    Linear.smul_comp, Linear.comp_smul, Category.assoc]

/-- **The dot on weight-space induction.** -/
def probeOldWeightDot :
    SuperNatTrans k (probeOldEFunctor D Sc m i Λ h) (probeOldEFunctor D Sc m i Λ h) where
  app p M δ := probeOldWeightDotComponent D Sc m i Λ h p M δ
  app_mem p M δ := probeOldWeightDotComponent_mem D Sc m i Λ h p M δ
  naturality p M M' q f hf := by
    funext δ
    by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
    · obtain ⟨β, rfl⟩ := hδ
      exact probeOldWeightDotComponent_naturality D Sc m i Λ h p β f hf
    · exact (probeOldInductionComponent_isZero D Sc m i Λ h δ hδ _).eq_of_src _ _

/-- Only the component of the colour parity is nonzero. -/
theorem probeOldWeightDot_homogeneous :
    (probeOldWeightDot D Sc m i Λ h).IsHomogeneous (D.parity i) := by
  intro q hq
  funext M
  funext δ
  by_cases hδ : ∃ β, blockSucc D Λ i h β = δ
  · obtain ⟨β, rfl⟩ := hδ
    change probeOldWeightDotComponent D Sc m i Λ h q M (blockSucc D Λ i h β) = 0
    rw [probeOldWeightDotComponent_blockSucc,
      congrFun (probeOldBlockDot_homogeneous D Sc m i Λ h β q hq)
        (M β)]
    simp
  · exact (probeOldInductionComponent_isZero D Sc m i Λ h δ hδ M).eq_of_src _ _

/-- The dot as a 2-endomorphism of weight-space induction in the action target. -/
def probeOldActionDot : probeOldE D Sc m i Λ h ⟶ probeOldE D Sc m i Λ h :=
  probeOldWeightDot D Sc m i Λ h

/-- The dot has the parity of its colour, including for odd colours. -/
theorem probeOldActionDot_mem :
    probeOldActionDot D Sc m i Λ h ∈
      parity (R := k) (probeOldE D Sc m i Λ h) (probeOldE D Sc m i Λ h)
        (D.parity i) :=
  Superfunctor.mem_parity_iff_isHomogeneous.2 (probeOldWeightDot_homogeneous D Sc m i Λ h)

end OddMath.QuiverHecke
end

end
