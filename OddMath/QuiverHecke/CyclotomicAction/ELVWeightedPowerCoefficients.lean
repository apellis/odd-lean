import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedCoefficientMaps

/-! # Full coefficient action on the actual weighted power vacuum

`SwappedVacuumCoordinates.md`, §§1, 3 and 6 retains the literal A/T
coefficient action through weighted descent. The given empty coordinate
commutes with that action. The actual inverse coefficient cap therefore
has its full signed A/T-linearity, in the original left multiplication order.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor
universe u

private theorem even_module_total_apply
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {F G : Superfunctor k C (SVec k)} (f : F ⟶ G)
    (hf : f ∈ parity (R := k) F G 0) {v w : C} (g : v ⟶ w) (b : F.obj v) :
    f.total w (F.map g b) = G.map g (f.total v b) := by
  have ht (t : C) : f.total t = f.app 0 t := by
    rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (by decide : (1 : ZMod 2) ≠ 0) t,
      add_zero]
  rw [ht v, ht w]
  have h := ((Superfunctor.toSuperNatTrans f).isSupernatural 0).naturality_zero g
  simpa only [SVec.comp_apply] using congrArg (fun a : F.obj v ⟶ G.obj w => a b) h

private theorem homogeneous_module_total_apply
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {F G : Superfunctor k C (SVec k)} (f : F ⟶ G) {p : ZMod 2}
    (hf : f ∈ parity (R := k) F G p) {v w : C} {q : ZMod 2}
    (g : v ⟶ w) (hg : g ∈ parity (R := k) v w q) (b : F.obj v) :
    f.total w (F.map g b) = koszulSign p q • G.map g (f.total v b) := by
  have ht (t : C) : f.total t = f.app p t := by
    rcases parity_eq_zero_or_one p with rfl | rfl
    · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (by decide : (1 : ZMod 2) ≠ 0) t,
        add_zero]
    · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (by decide : (0 : ZMod 2) ≠ 1) t,
        zero_add]
  rw [ht v, ht w]
  exact LinearMap.congr_fun (f.naturality p g hg) b

namespace PowerVacuumCoefficient
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  [Fintype I] (L : I × ℕ → ℕ)
local notation "bound" => SKM.SYM.elvPowerWeightBound D cutoff L + 1
local notation "WM" => weightedVacuum D Sc cutoff L
local notation "OM" => coefficientPowerVacuum D Sc cutoff L
local notation "RM" => weightedRestriction D Sc cutoff bound WM
local notation "Q" => oldTruncateFunctor D Sc cutoff bound
local notation "AQ" => CoefficientPowerQuotient (k := k) D cutoff L
/-- The class in the literal full coefficient power quotient. -/
abbrev coefficientClass (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) : AQ :=
  (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k a

private theorem powerVacuum_killsWeighted : KillsWeightedCoefficients D Sc cutoff bound OM :=
  (coefficientWeightedIdeal_le_annihilator_iff D Sc cutoff bound OM).mp
    ((weighted_le_elementaryPowerIdeal D cutoff L).trans
      (coefficientPowerVacuumObject D Sc cutoff L).property)

/-- The actual identity-component restriction/descent comparison already
used by the typed weighted empty coordinate. -/
def weightedRestrictionIso : RM ≅ OM :=
  weightedRestrictionModuleIso D Sc cutoff bound OM (powerVacuum_killsWeighted D Sc cutoff L)

private theorem weightedRestrictionIso_inv_mem :
    (weightedRestrictionIso D Sc cutoff L).inv ∈ parity (R := k) OM RM 0 := by
  exact moduleIsoOfEvenNatIso_inv_mem _ _ _ _ _

/-- The original typed empty coordinate uses the inverse of that same
selected descent comparison, without a scalar or a coefficient reversal. -/
theorem weightedEmptyEquiv_apply (x : AQ) :
    weightedEmptyEquiv D Sc cutoff L x =
      (weightedRestrictionIso D Sc cutoff L).inv.total (⟨[]⟩ : OldCategory D Sc cutoff)
        (coefficientPowerVacuumEmptyEquiv D Sc cutoff L x) := rfl

/-- The literal full coefficient arrow in the actual weighted category. -/
def weightedCoefficientEnd (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    ((Q).obj (⟨[]⟩ : OldCategory D Sc cutoff)) ⟶ ((Q).obj (⟨[]⟩ : OldCategory D Sc cutoff)) :=
  (Q).map (coefficientEndomorphism D Sc cutoff [] a)

/-- The actual weighted empty coordinate intertwines every full coefficient
with its original left action on the literal power quotient. -/
theorem weightedEmptyEquiv_coefficient_action
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (x : AQ) :
    (WM).map (weightedCoefficientEnd D Sc cutoff L a) (weightedEmptyEquiv D Sc cutoff L x) =
      weightedEmptyEquiv D Sc cutoff L (coefficientClass D cutoff L a * x) := by
  have hn := even_module_total_apply (weightedRestrictionIso D Sc cutoff L).inv
    (weightedRestrictionIso_inv_mem D Sc cutoff L)
    (coefficientEndomorphism D Sc cutoff [] a) (coefficientPowerVacuumEmptyEquiv D Sc cutoff L x)
  have ha := empty_coefficient_action D Sc cutoff L a x
  rw [weightedEmptyEquiv_apply, weightedEmptyEquiv_apply]
  exact hn.symm.trans (congrArg ((weightedRestrictionIso D Sc cutoff L).inv.total ⟨[]⟩) ha)

private theorem weightedEmptyEquiv_coefficient_decode
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (x : (WM).obj ((Q).obj (⟨[]⟩ : OldCategory D Sc cutoff))) :
    (weightedEmptyEquiv D Sc cutoff L).symm ((WM).map (weightedCoefficientEnd D Sc cutoff L a) x) =
      coefficientClass D cutoff L a * (weightedEmptyEquiv D Sc cutoff L).symm x := by
  let e := weightedEmptyEquiv D Sc cutoff L
  have h := weightedEmptyEquiv_coefficient_action D Sc cutoff L a (e.symm x)
  rw [e.apply_symm_apply] at h
  exact (congrArg e.symm h).trans (e.symm_apply_apply _)

/-- The weighted inverse cap has the full A/T-superlinearity of its
prescribed degree, on the actual weighted F/E coefficient action and
with coefficient multiplication in the original left order. -/
theorem weightedFunctional_coefficient (i : I) (hN : 0 < cutoff i) {q : ZMod 2}
    {a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff}
    (ha : a ∈ SKM.SYM.elvCoefficientParity D cutoff q)
    (z : (((restriction (truncatedAppend D Sc cutoff bound [i])).obj
      ((induction (truncatedAppend D Sc cutoff bound [i])).obj WM)).obj
        ((Q).obj (⟨[]⟩ : OldCategory D Sc cutoff)))) :
    weightedFunctional D Sc cutoff L i hN
      (((restriction (truncatedAppend D Sc cutoff bound [i])).obj
        ((induction (truncatedAppend D Sc cutoff bound [i])).obj WM)).map
          (weightedCoefficientEnd D Sc cutoff L a) z) =
      koszulSign ((cutoff i - 1) • D.parity i) q •
        (coefficientClass D cutoff L a * weightedFunctional D Sc cutoff L i hN z) := by
  let s : ContentCategory D Sc cutoff bound 0 := ⟨⟨[]⟩, rfl⟩
  let g : s ⟶ s := weightedCoefficientEnd D Sc cutoff L a
  have hg : g ∈ parity (R := k) s s q :=
    IsSuperfunctor.map_mem (F := Q) (coefficientEndomorphism_mem D Sc cutoff [] ha)
  have hn := homogeneous_module_total_apply (weightedCoefficientCap D Sc cutoff i L hN)
    (weightedCoefficientCap_mem D Sc cutoff i L hN) g hg z
  have hd := weightedEmptyEquiv_coefficient_decode D Sc cutoff L a
    ((weightedCoefficientCap D Sc cutoff i L hN).total s z)
  rw [weightedFunctional_coefficientCap, weightedFunctional_coefficientCap]
  calc
    _ = (weightedEmptyEquiv D Sc cutoff L).symm
        (koszulSign ((cutoff i - 1) • D.parity i) q •
          (WM).map (weightedCoefficientEnd D Sc cutoff L a)
            ((weightedCoefficientCap D Sc cutoff i L hN).total s z)) :=
      congrArg (weightedEmptyEquiv D Sc cutoff L).symm hn
    _ = koszulSign ((cutoff i - 1) • D.parity i) q •
        (weightedEmptyEquiv D Sc cutoff L).symm
          ((WM).map (weightedCoefficientEnd D Sc cutoff L a)
            ((weightedCoefficientCap D Sc cutoff i L hN).total s z)) := by rw [map_zsmul]
    _ = _ := congrArg (fun y : AQ => koszulSign ((cutoff i - 1) • D.parity i) q • y) hd

end PowerVacuumCoefficient
end OddMath.QuiverHecke.ELVOld
