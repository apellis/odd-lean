import OddMath.QuiverHecke.CyclotomicAction.ELVContentHomVacuum
import Mathlib.Data.Finsupp.Multiset

/-! # Formal sectors of the replete supported Hom action

The exact-content categories of F4 and (A1) of `SwappedActionAssembly.md`,
indexed by the existing formal probe/reservoir sectors. Original-weight
collisions remain separate formal components. These indices supply the
restriction of the native generator functors to supported Hom objects.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
open scoped Classical
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : Datum I X) (Sc : Scalars D k) (m : I → ℕ) (cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)

theorem sum_content (b : I →₀ ℕ) :
    (b.toMultiset.map D.α).sum = contentWeight D b := by
  refine b.induction ?_ ?_
  · simp [contentWeight]
  · intro i n b _ _ ih
    rw [Finsupp.toMultiset_add, Multiset.map_add, Multiset.sum_add, ih, map_add]
    rw [Finsupp.toMultiset_single, ← Multiset.coe_mapAddMonoidHom,
      (Multiset.mapAddMonoidHom D.α).map_nsmul, Multiset.sum_nsmul]
    simp [contentWeight, Finsupp.weight_single]

def probeWeight (t : Sector I) : X := -(ΛP - contentWeight D t.1)
def reservoirWeight (t : Sector I) : X := -ΛR + contentWeight D t.2

/-- The chosen formal probe block inside its whole original-weight fibre. -/
def probeBlock (t : Sector I) : WeightBlocks D ΛP (probeWeight D ΛP t) :=
  ⟨t.1.toMultiset, by rw [blockWeight, sum_content]; dsimp [probeWeight]; abel⟩

/-- The chosen formal reservoir block inside its whole original-weight fibre. -/
def reservoirBlock (t : Sector I) : WeightBlocks D ΛR (reservoirWeight D ΛR t) :=
  ⟨t.2.toMultiset, by rw [blockWeight, sum_content]; dsimp [reservoirWeight]; abel⟩

/-- The unrestricted ambient Hom in which the supported object is realized. -/
abbrev Ambient (t : Sector I) :=
  probeOldWeightSpace D Sc m ΛP (probeWeight D ΛP t) ⟶
    elvWeightSpace D Sc cutoff bound ΛR (reservoirWeight D ΛR t)

/-- The supported full Hom category at a formal sector. -/
abbrev H (t : Sector I) := ContentHomSupport.SupportedHom D Sc m cutoff bound
  (probeBlock D ΛP t) (reservoirBlock D ΛR t)

/-- The canonical full inclusion preserves every supernatural arrow. -/
def inclusion (t : Sector I) : H D Sc m cutoff bound ΛP ΛR t ⥤
    Ambient D Sc m cutoff bound ΛP ΛR t := ObjectProperty.ι _

instance inclusion_additive (t : Sector I) :
    (inclusion D Sc m cutoff bound ΛP ΛR t).Additive := by
  dsimp [inclusion]
  infer_instance
instance inclusion_linear (t : Sector I) :
    (inclusion D Sc m cutoff bound ΛP ΛR t).Linear k := by
  dsimp [inclusion]
  infer_instance
instance inclusion_super (t : Sector I) :
    IsSuperfunctor k (inclusion D Sc m cutoff bound ΛP ΛR t) where
  map_mem hf := hf
instance inclusion_full (t : Sector I) :
    (inclusion D Sc m cutoff bound ΛP ΛR t).Full := by
  dsimp [inclusion]
  infer_instance
instance inclusion_faithful (t : Sector I) :
    (inclusion D Sc m cutoff bound ΛP ΛR t).Faithful := by
  dsimp [inclusion]
  infer_instance

@[instance_reducible]
def homPi (t : Sector I) : PiSupercategory k (H D Sc m cutoff bound ΛP ΛR t) :=
  ContentHomSupport.supportedPi D Sc m cutoff bound (probeBlock D ΛP t) (reservoirBlock D ΛR t)

/-- The supported sector as a literal parity-supercategory. -/
def target (t : Sector I) : PiSCat.{u, u + 1, u + 1} k :=
  letI := homPi D Sc m cutoff bound ΛP ΛR t
  PiSCat.of k (H D Sc m cutoff bound ΛP ΛR t)

theorem mem_content (b : I →₀ ℕ) (i : I) : i ∈ b.toMultiset ↔ 1 ≤ b i := by
  rw [Finsupp.mem_toMultiset, Finsupp.mem_support_iff]
  omega

theorem probe_valid_iff (i : I) (t : Sector I) :
    StepValid (false, i) true t ↔ i ∈ (probeBlock D ΛP t).1 :=
  (mem_content t.1 i).symm

theorem reservoir_valid_iff (i : I) (t : Sector I) :
    StepValid (true, i) false t ↔ i ∈ (reservoirBlock D ΛR t).1 :=
  (mem_content t.2 i).symm

theorem probeUp_edge (i : I) (t : Sector I) :
    probeWeight D ΛP t + D.α i = probeWeight D ΛP (nextSector (true, i) true t) := by
  dsimp [probeWeight, nextSector]
  rw [contentWeight_add_single]
  abel

theorem probeDown_edge (i : I) {t : Sector I} (hv : StepValid (false, i) true t) :
    probeWeight D ΛP (nextSector (false, i) true t) + D.α i = probeWeight D ΛP t := by
  have hc := contentWeight_sub_single (D := D) hv
  dsimp [probeWeight, nextSector]
  rw [← hc]
  abel

theorem reservoirDown_edge (i : I) (t : Sector I) :
    reservoirWeight D ΛR t + D.α i = reservoirWeight D ΛR (nextSector (false, i) false t) := by
  dsimp [reservoirWeight, nextSector]
  rw [contentWeight_add_single]
  abel

theorem reservoirUp_edge (i : I) {t : Sector I} (hv : StepValid (true, i) false t) :
    reservoirWeight D ΛR (nextSector (true, i) false t) + D.α i = reservoirWeight D ΛR t := by
  dsimp [reservoirWeight, nextSector]
  rw [add_assoc, contentWeight_sub_single hv]

/-- The selected probe successor is the actual block successor. -/
theorem probeBlock_up (i : I) (t : Sector I) :
    blockSucc D ΛP i (probeUp_edge D ΛP i t) (probeBlock D ΛP t) =
      probeBlock D ΛP (nextSector (true, i) true t) := by
  apply Subtype.ext
  change {i} + t.1.toMultiset = (t.1 + Finsupp.single i 1).toMultiset
  simp [Finsupp.toMultiset_add, Finsupp.toMultiset_single, add_comm]

private theorem content_pred (b : I →₀ ℕ) (i : I) (hi : 1 ≤ b i) :
    {i} + (b - Finsupp.single i 1).toMultiset = b.toMultiset := by
  have hle : Finsupp.single i 1 ≤ b := (Finsupp.single_le_iff).mpr hi
  have hh := congrArg Finsupp.toMultiset (tsub_add_cancel_of_le hle)
  simpa only [Finsupp.toMultiset_add, Finsupp.toMultiset_single, one_nsmul, add_comm] using hh

/-- The selected probe predecessor has the exact block-successor certificate. -/
theorem probeBlock_down (i : I) {t : Sector I} (hv : StepValid (false, i) true t) :
    blockSucc D ΛP i (probeDown_edge D ΛP i hv)
      (probeBlock D ΛP (nextSector (false, i) true t)) = probeBlock D ΛP t := by
  apply Subtype.ext
  exact content_pred t.1 i hv

/-- The selected reservoir successor is the actual block successor. -/
theorem reservoirBlock_down (i : I) (t : Sector I) :
    blockSucc D ΛR i (reservoirDown_edge D ΛR i t) (reservoirBlock D ΛR t) =
      reservoirBlock D ΛR (nextSector (false, i) false t) := by
  apply Subtype.ext
  change {i} + t.2.toMultiset = (t.2 + Finsupp.single i 1).toMultiset
  simp [Finsupp.toMultiset_add, Finsupp.toMultiset_single, add_comm]

/-- The selected reservoir predecessor has the exact successor certificate. -/
theorem reservoirBlock_up (i : I) {t : Sector I} (hv : StepValid (true, i) false t) :
    blockSucc D ΛR i (reservoirUp_edge D ΛR i hv)
      (reservoirBlock D ΛR (nextSector (true, i) false t)) = reservoirBlock D ΛR t := by
  apply Subtype.ext
  exact content_pred t.2 i hv

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
