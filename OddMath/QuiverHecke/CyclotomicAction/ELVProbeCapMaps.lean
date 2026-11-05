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

private theorem nonzero_of_total_surjective
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {F G : Superfunctor k C (SVec k)} (f : F ⟶ G) (t : C)
    (hf : Function.Surjective (f.total t)) (v : G.obj t) (hv : v ≠ 0) : f ≠ 0 := by
  intro h0
  obtain ⟨z, hz⟩ := hf v
  have he : f.total t z = 0 := by
    rw [h0]
    simp only [SuperNatTrans.total, Superfunctor.zero_app, zero_add, SVec.zero_apply]
  exact hv (hz.symm.trans he)

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

private theorem ground_decoder_mem
    {k : Type u} [CommRing k] (V : SVec k) (f : V →ₗ[k] k)
    (heven : ∀ v : V, v ∈ V.part 0) :
    SVec.ofHom f ∈ parity (R := k) V (SVec.unit : SVec k) 0 := by
  apply SVec.mem_parityHom_of_apply_mem
  intro q v hv
  rcases parity_eq_zero_or_one q with rfl | rfl
  · change f v ∈ (SVec.unit : SVec k).part 0
    rw [SVec.mem_part_zero_iff]
    rfl
  · have h0 := (SVec.mem_part_zero_iff V).mp (heven v)
    have h1 := (SVec.mem_part_one_iff V).mp hv
    have hz : v = 0 := h1.symm.trans h0
    subst v
    change f 0 ∈ (SVec.unit : SVec k).part (1 + 0)
    rw [map_zero]
    exact Submodule.zero_mem _

private theorem ground_comp_mem
    {k : Type u} [CommRing k] (V W : SVec k)
    (f : V →ₗ[k] W) (g : W →ₗ[k] k) {p : ZMod 2}
    (hf : f ∈ parity (R := k) V W p)
    (hg : SVec.ofHom g ∈ parity (R := k) W (SVec.unit : SVec k) 0) :
    SVec.ofHom (g.comp f) ∈ parity (R := k) V (SVec.unit : SVec k) p := by
  apply SVec.mem_parityHom_of_apply_mem
  intro q v hv
  have h := SVec.apply_mem_part hg (SVec.apply_mem_part hf hv)
  simpa only [add_zero, SVec.ofHom_apply, LinearMap.comp_apply] using h

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

/-- Every component of this specified module cap is surjective. -/
theorem cap_total_surjective (i : I) (hP : 0 < cut i)
    (t : OldContentCategory D Sc cut []) : Function.Surjective ((cap D Sc m i hP).total t) :=
  contentCoefficientCap_total_surjective D Sc cut [] i N
    (height D m i) (topIndex D m i hP) t

/-- The inverse-defined cap is nonzero on the actual probe module. -/
theorem cap_ne_zero [Nontrivial k] (i : I) (hP : 0 < cut i) : cap D Sc m i hP ≠ 0 :=
  nonzero_of_total_surjective _ s (cap_total_surjective D Sc m i hP s)
    (probeOldVacuumVector D Sc m) (probeOldVacuumVector_ne_zero D Sc m)

/-- Ground decoding of this native module cap uses the original empty
coordinate, with no extra cap scalar. -/
def groundRow (i : I) (hP : 0 < cut i) : (source D Sc m i).obj s →ₗ[k] k :=
  (probeVacuumScalarEquiv D Sc m).symm.toLinearMap.comp ((cap D Sc m i hP).total s)

/-- The scalar row retains the native cap's full homogeneous degree. -/
theorem groundRow_mem (i : I) (hP : 0 < cut i) :
    SVec.ofHom (groundRow D Sc m i hP) ∈ parity (R := k)
      ((source D Sc m i).obj s) (SVec.unit : SVec k) ((cut i - 1) • D.parity i) := by
  unfold groundRow
  apply ground_comp_mem
  · exact total_mem (cap_mem D Sc m i hP) s
  · exact ground_decoder_mem ((N).obj s) (probeVacuumScalarEquiv D Sc m).symm.toLinearMap
      (probeVacuum_even D Sc m)

/-- Every scalar is extracted by the native probe cap's ground coordinate. -/
theorem groundRow_surjective (i : I) (hP : 0 < cut i) :
    Function.Surjective (groundRow D Sc m i hP) := by
  intro c
  obtain ⟨v, hv⟩ := (probeVacuumScalarEquiv D Sc m).symm.surjective c
  obtain ⟨z, hz⟩ := cap_total_surjective D Sc m i hP s v
  refine ⟨z, ?_⟩
  change (probeVacuumScalarEquiv D Sc m).symm ((cap D Sc m i hP).total s z) = c
  rw [hz]
  exact hv

end OddMath.QuiverHecke.ELVOld.ProbeVacuumCap
