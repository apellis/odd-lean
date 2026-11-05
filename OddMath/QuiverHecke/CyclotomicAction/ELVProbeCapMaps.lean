import OddMath.QuiverHecke.CyclotomicAction.ELVContentCoefficientCaps
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeVacuumCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVUnitCoefficientRows
import OddMath.QuiverHecke.CyclotomicAction.ELVFullyFaithfulInduction

/-! # Inverse-defined caps on the regular vacuum probe

The normalized probe cap needed in `SwappedVacuumNonpositiveBubbles.md`,
§2, must be a module morphism with target the original regular T₀.
We use the selected native F/E chart, the prescribed last inverse row,
and the inverse fully faithful inclusion unit. No final mixed slide or
identification with a separate action's left counit is asserted here.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.ProbeVacuumCap
open BalancedInduction CyclotomicCrossingTensor
universe u

private theorem total_mem
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {F G : Superfunctor k C (SVec k)} {f : F ⟶ G} {p : ZMod 2}
    (hf : f ∈ parity (R := k) _ _ p) (t : C) :
    f.total t ∈ parity (R := k) (F.obj t) (G.obj t) p := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (by decide : (1 : ZMod 2) ≠ 0) t,
      add_zero]
    exact f.app_mem 0 t
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (by decide : (0 : ZMod 2) ≠ 1) t,
      zero_add]
    exact f.app_mem 1 t

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ)
local notation "cut" => probeCutoff D m
local notation "N" => probeOldVacuumRegular D Sc m
local notation "K" => oldContentAppend D Sc cut []
local notation "s" => probeOldVacuumObject D Sc m

omit [Fintype I] in
private theorem height (i : I) :
    0 ≤ contentCrossingHeight D cut i (([] : List I) : Multiset I) := by
  simp [contentCrossingHeight]

private def topIndex (i : I) (hP : 0 < cut i) :
    Fin (contentUnitCount D cut i (([] : List I) : Multiset I)) :=
  ⟨cut i - 1, by rw [VacuumCoefficient.count]; omega⟩

/-- The native F/E module of the original regular probe T₀. -/
abbrev source (i : I) : Superfunctor k (OldContentCategory D Sc cut []) (SVec k) :=
  (restriction (K i)).obj ((induction (K i)).obj N)

/-- The inverse-defined last coefficient cap, now with the original regular
probe as target rather than its full-old extension. -/
def cap (i : I) (hP : 0 < cut i) : source D Sc m i ⟶ N :=
  contentCoefficientCap D Sc cut [] i N (height D m i) (topIndex D m i hP)

/-- The probe cap has the prescribed last-row degree (P-1)*p. -/
theorem cap_mem (i : I) (hP : 0 < cut i) :
    cap D Sc m i hP ∈ parity (R := k) _ _ ((cut i - 1) • D.parity i) :=
  contentCoefficientCap_mem D Sc cut [] i N (height D m i) (topIndex D m i hP)

end OddMath.QuiverHecke.ELVOld.ProbeVacuumCap
