import OddMath.QuiverHecke.CyclotomicAction.ELVProbeExtensionRows

/-! # Parity of the ground-valued probe inverse row

The probe coefficient extractor in `SwappedVacuumNonpositiveBubbles.md`,
§2, retains the last inverse row's parity. Its target is the even ground
ring. For an odd colour the positive probe cutoff is even, so the row is
odd; this statement concerns the prescribed full-old inverse matrix.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.ProbeExtensionCoefficient
open BalancedInduction CyclotomicCrossingTensor CyclotomicCrossingTensor.TensorMatrixCoordinates
universe u

private theorem groundMap_even
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

private theorem groundComposite_mem
    {k : Type u} [CommRing k] (V W : SVec k)
    (f : V →ₗ[k] W) (g : W →ₗ[k] k) {p : ZMod 2}
    (hf : SVec.ofHom f ∈ parity (R := k) V W p)
    (hg : SVec.ofHom g ∈ parity (R := k) W (SVec.unit : SVec k) 0) :
    SVec.ofHom (g.comp f) ∈ parity (R := k) V (SVec.unit : SVec k) p := by
  apply SVec.mem_parityHom_of_apply_mem
  intro q v hv
  have h := SVec.apply_mem_part hg (SVec.apply_mem_part hf hv)
  simpa only [add_zero, SVec.ofHom_apply, LinearMap.comp_apply] using h

private theorem unitCoefficient_ground_mem
    {I X k : Type u} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
    (N : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (i : I) (v : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (v.word : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (v.word : Multiset I)))
    (decode : N.obj v →ₗ[k] k)
    (hdecode : SVec.ofHom decode ∈ parity (R := k) (N.obj v) (SVec.unit : SVec k) 0) :
    SVec.ofHom (decode.comp (moduleUnitCoefficient D Sc cutoff N i v hh r)) ∈
      parity (R := k) (mateTargetSpace D Sc cutoff i N v) (SVec.unit : SVec k)
        (r.val • D.parity i) :=
  groundComposite_mem _ _ _ _ (moduleUnitCoefficient_mem D Sc cutoff N i v hh r) hdecode

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ)
local notation "cut" => probeCutoff D m
local notation "M" => probeOldVacuumRegular D Sc m
local notation "s" => probeOldVacuumObject D Sc m
local notation "J" => oldContentInclusion D Sc cut []
local notation "L" => induced J M
local notation "t" => OldContentCategory.obj (probeOldVacuumObject D Sc m)

/-- The canonical full extension has an entirely even empty component,
since its fully faithful unit identifies it with the regular probe vacuum. -/
theorem extension_empty_even (z : (L).obj t) : z ∈ ((L).obj t).part 0 := by
  have he := probeVacuum_even D Sc m (fullyFaithfulUnitInverse J (M).toFunctor s z)
  have hu := SVec.apply_mem_part (unit_mem J M s) he
  have hz := LinearMap.congr_fun (unit_fullyFaithfulUnitInverse J (M).toFunctor s) z
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at hz
  change unit J (M).toFunctor s (fullyFaithfulUnitInverse J (M).toFunctor s z) = z at hz
  change unit J (M).toFunctor s (fullyFaithfulUnitInverse J (M).toFunctor s z) ∈
    ((L).obj t).part (0 + 0) at hu
  rw [hz] at hu
  simpa only [zero_add] using hu

/-- Scalar decoding is even, including on every vector of the canonical extension. -/
theorem scalarCoordinate_mem :
    SVec.ofHom (scalarCoordinate D Sc m) ∈
      parity (R := k) ((L).obj t) (SVec.unit : SVec k) 0 :=
  groundMap_even ((L).obj t) (scalarCoordinate D Sc m) (extension_empty_even D Sc m)

/-- The ground-valued last inverse row retains its prescribed top-row parity. -/
theorem functional_mem (i : I) (hN : 0 < cut i) :
    SVec.ofHom (functional D Sc m i hN) ∈
      parity (R := k) (mateTargetSpace D Sc cut i L t) (SVec.unit : SVec k)
        ((cut i - 1) • D.parity i) := by
  unfold functional
  have hh : 0 ≤ contentCrossingHeight D cut i (([] : List I) : Multiset I) := by
    simp [contentCrossingHeight]
  let r : Fin (contentUnitCount D cut i (([] : List I) : Multiset I)) :=
    ⟨cut i - 1, by rw [VacuumCoefficient.count]; omega⟩
  exact unitCoefficient_ground_mem D Sc cut L i t hh r (scalarCoordinate D Sc m)
    (scalarCoordinate_mem D Sc m)

end OddMath.QuiverHecke.ELVOld.ProbeExtensionCoefficient
