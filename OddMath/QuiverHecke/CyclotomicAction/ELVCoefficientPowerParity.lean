import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerModules
import OddMath.QuiverHecke.CyclotomicAction.ELVContentSingleLetterRelations
import OddMath.QuiverHecke.CyclotomicAction.PiWeightSpaces

/-! # Parity closure of coefficient-power modules

The coefficient-power module category of `SwappedNondegeneracy.md`, §2
is stable under the chosen module parity shift. Its full Pi-supercategory
structure retains the same odd comparison isomorphism. Even coefficient
annihilation is invariant under arbitrary old-module isomorphisms.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Even coefficient annihilation transports along the exact supplied
module isomorphism; its components need not be even. -/
theorem killsCoefficient_of_iso
    (M N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (e : M ≅ N)
    {a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff}
    (ha : a ∈ SKM.SYM.elvCoefficientParity D cutoff 0)
    (hM : KillsCoefficient D Sc cutoff M a) : KillsCoefficient D Sc cutoff N a := by
  intro v
  apply LinearMap.ext
  intro z
  apply (moduleIsoLinearEquiv e (⟨v⟩ : OldCategory D Sc cutoff)).symm.injective
  have h := LinearMap.congr_fun (moduleMap_evenCoefficient D Sc cutoff N M e.inv v ha) z
  change e.inv.total ⟨v⟩ (N.map (X := ⟨v⟩) (Y := ⟨v⟩)
      (coefficientEndomorphism D Sc cutoff v a) z) =
    M.map (X := ⟨v⟩) (Y := ⟨v⟩) (coefficientEndomorphism D Sc cutoff v a)
      (e.inv.total ⟨v⟩ z) at h
  rw [hM v, LinearMap.zero_apply] at h
  change e.inv.total ⟨v⟩ (N.map (X := ⟨v⟩) (Y := ⟨v⟩)
    (coefficientEndomorphism D Sc cutoff v a) z) = e.inv.total ⟨v⟩ 0
  simpa only [map_zero] using h

variable {J : Type u}
  (c : J → SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (L : J → ℕ)
  (hc : ∀ j, c j ∈ SKM.SYM.elvCoefficientParity D cutoff 0)

include hc in
/-- The exact power-ideal annihilator is invariant under any supplied
old-module isomorphism, by its generator characterization. -/
theorem coefficientPowerProperty_of_iso
    (M N : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (e : M ≅ N)
    (hM : coefficientPowerProperty D Sc cutoff c L M) :
    coefficientPowerProperty D Sc cutoff c L N := by
  apply (coefficientPowerProperty_iff D Sc cutoff c L N).mpr
  intro j
  have hp : c j ^ L j ∈ SKM.SYM.elvCoefficientParity D cutoff 0 := by
    simpa only [nsmul_zero] using SetLike.pow_mem_graded (L j) (hc j)
  exact killsCoefficient_of_iso D Sc cutoff M N e hp
    ((coefficientPowerProperty_iff D Sc cutoff c L M).mp hM j)

include hc in
/-- The chosen module parity shift preserves annihilation by the exact
coefficient-power ideal, including the odd exterior part of that ideal. -/
theorem coefficientPowerProperty_parity
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : coefficientPowerProperty D Sc cutoff c L M) :
    coefficientPowerProperty D Sc cutoff c L (supermoduleParityObj M) :=
  coefficientPowerProperty_of_iso D Sc cutoff c L hc M (supermoduleParityObj M)
    (supermoduleParityIso M).symm hM

/-- The power-annihilated full module category carries the inherited
chosen Pi structure, with exactly the old odd comparison maps. -/
@[instance_reducible]
def coefficientPowerPi : PiSupercategory k (CoefficientPowerModules D Sc cutoff c L) :=
  letI := supermodulePiSupercategory (k := k) (C := OldCategory D Sc cutoff)
  CyclotomicAction.fullPiSupercategory (coefficientPowerProperty D Sc cutoff c L)
    (fun M hM => coefficientPowerProperty_parity D Sc cutoff c L hc M hM)

end OddMath.QuiverHecke.ELVOld
