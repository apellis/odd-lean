import OddMath.QuiverHecke.CyclotomicAction.ELVContentEFChartTensors

/-! # Evenness of the selected content E/F charts

The parity-shifted summands in Brundan--Ellis (1.13)--(1.14) use the chosen
content extension/restriction comparisons. Their forward and inverse maps
are even, so the canonical parity comparison retains each prescribed row.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor
universe u v w
private theorem even_comp
    {k : Type u} {A : Type v} [CommRing k] [Category.{w} A]
    [Preadditive A] [Linear k A] [Supercategory k A]
    {P Q R : A} {f : P ⟶ Q} {g : Q ⟶ R}
    (hf : f ∈ parity (R := k) _ _ 0) (hg : g ∈ parity (R := k) _ _ 0) :
    f ≫ g ∈ parity (R := k) _ _ 0 := by
  simpa only [zero_add] using comp_mem hf hg

private theorem even_of_app_one_zero
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {M N : Superfunctor k C (SVec k)} (f : M ⟶ N) (h : ∀ w, f.app 1 w = 0) :
    f ∈ parity (R := k) _ _ 0 := by
  apply Superfunctor.mem_parity_iff_isHomogeneous.mpr
  intro q hq
  rcases parity_eq_zero_or_one q with rfl | rfl
  · exact (hq rfl).elim
  · funext w
    exact h w

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i : I)
local notation "J₀" => oldContentAppend D Sc cutoff ν i
local notation "Q₀" => oldContentInclusion D Sc cutoff ν
local notation "Q₁" => oldContentInclusion D Sc cutoff (i :: ν)
local notation "J" => append D Sc cutoff i

/-- The selected one-letter extension comparison is even. -/
theorem oldContentAppendExtensionIso_hom_mem
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k)) :
    (oldContentAppendExtensionIso D Sc cutoff ν i).hom.app M ∈ parity (R := k) _ _ 0 := by
  apply even_of_app_one_zero
  intro w
  have hf := comp_mem (BalancedInduction.inductionComp_hom_mem J₀ Q₁ M)
    (BalancedInduction.inductionComp_inv_mem Q₀ J M)
  have hz := Superfunctor.app_eq_zero_of_mem hf (by decide : (1 : ZMod 2) ≠ 0 + 0) w
  have he := congrArg (fun f => f.app 1 w)
    (oldContentAppendExtensionIso_hom D Sc cutoff ν i M)
  exact he.trans hz

/-- The selected restriction-extension comparison is even. -/
theorem oldContentRestrictionExtensionIso_hom_mem
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k)) :
    (oldContentRestrictionExtensionIso D Sc cutoff ν i N).hom ∈ parity (R := k) _ _ 0 := by
  apply even_of_app_one_zero
  intro w
  exact oldContentRestrictionExtensionComponent_one D Sc cutoff ν i N w

/-- The selected induction comparison after restriction is even, including
its fully faithful inclusion unit. -/
theorem oldContentAppendRestrictionIso_hom_mem
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k)) :
    (oldContentAppendRestrictionIso D Sc cutoff ν i M).hom ∈ parity (R := k) _ _ 0 := by
  have hu : (oldContentExtensionUnitIso D Sc cutoff (i :: ν)
      (BalancedInduction.induced J₀ M)).hom ∈ parity (R := k) _ _ 0 := by
    rw [oldContentExtensionUnitIso, BalancedInduction.fullyFaithfulUnitIso_hom]
    exact BalancedInduction.adjunctionUnit_mem Q₁ _
  have he := map_mem (BalancedInduction.restriction Q₁)
    (oldContentAppendExtensionIso_hom_mem D Sc cutoff ν i M)
  dsimp only [oldContentAppendRestrictionIso, Iso.trans_hom, Functor.mapIso_hom]
  exact even_comp hu he

/-- The chosen preceding-composite chart is even. -/
theorem oldContentEFRestrictionNaturalIso_hom_mem
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k)) :
    (oldContentEFRestrictionNaturalIso D Sc cutoff ν i).hom.app N ∈ parity (R := k) _ _ 0 := by
  rw [oldContentEFRestrictionNaturalIso_hom_app]
  exact even_comp
    (oldContentAppendRestrictionIso_hom_mem D Sc cutoff ν i
      ((BalancedInduction.restriction J₀).obj N))
    (map_mem (BalancedInduction.restriction Q₁)
      (map_mem (BalancedInduction.induction J)
        (oldContentRestrictionExtensionIso_hom_mem D Sc cutoff ν i N)))

/-- The chosen following-composite chart is even. -/
theorem oldContentFERestrictionNaturalIso_hom_mem
    (M : Superfunctor k (OldContentCategory D Sc cutoff ν) (SVec k)) :
    (oldContentFERestrictionNaturalIso D Sc cutoff ν i).hom.app M ∈ parity (R := k) _ _ 0 := by
  rw [oldContentFERestrictionNaturalIso_hom_app]
  exact map_mem (BalancedInduction.restriction J₀)
    (oldContentAppendRestrictionIso_hom_mem D Sc cutoff ν i M)

end OddMath.QuiverHecke.ELVOld
