import OddMath.QuiverHecke.SwappedAssembly.SupportedRestriction

/-! # The native step functors on supported formal sectors

The four functors of F4/(A1)–(A3) in `SwappedActionAssembly.md` restrict
through the canonical full inclusions. The inherited left-adjunction and
content parity shifts remain in their prescribed input/output order.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : Datum I X) (Sc : Scalars D k) (m : I → ℕ) (cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)

/-- The exact support property defining the formal sector category. -/
def support (t : Sector I) : ObjectProperty (Ambient D Sc m cutoff bound ΛP ΛR t) :=
  ContentHomSupport.Supported D Sc m cutoff bound (probeBlock D ΛP t) (reservoirBlock D ΛR t)
local instance (x y : X) : PiSupercategory k
    (probeOldWeightSpace D Sc m ΛP x ⟶ elvWeightSpace D Sc cutoff bound ΛR y) :=
  PiTwoSupercategory.homPiLeft _ _

/-- The native OLD/ELV step, before restricting its objects to exact support. -/
def nativeStep : (l : Letter I) → (side : Bool) → (t : Sector I) → StepValid l side t →
    Superfunctor k (Ambient D Sc m cutoff bound ΛP ΛR (nextSector l side t))
      (Ambient D Sc m cutoff bound ΛP ΛR t)
  | (true, i), true, t, _ =>
    ⟨homPre (k := k) (probeOldE D Sc m i ΛP (probeUp_edge D ΛP i t))⟩
  | (true, i), false, t, hv =>
    ⟨homPost (k := k) (elvE D Sc cutoff bound i ΛR (reservoirUp_edge D ΛR i hv)) ⋙
      homParityShift (k := k) (homContentShift D i t.1)⟩
  | (false, i), true, t, hv =>
    ⟨homPre (k := k) (probeOldF D Sc m i ΛP (probeDown_edge D ΛP i hv)) ⋙
      homParityShift (k := k) (leftAdjParity D i (probeWeight D ΛP (nextSector (false, i) true t)))⟩
  | (false, i), false, t, _ =>
    ⟨homParityShift (k := k) (homContentShift D i t.1) ⋙
      homPost (k := k) (elvF D Sc cutoff bound i ΛR (reservoirDown_edge D ΛR i t))⟩

/-- All four native steps preserve the replete exact-content object property. -/
theorem step_closed (l : Letter I) (side : Bool) (t : Sector I) (hv : StepValid l side t)
    (Z : Ambient D Sc m cutoff bound ΛP ΛR (nextSector l side t))
    (hZ : support D Sc m cutoff bound ΛP ΛR (nextSector l side t) Z) :
    support D Sc m cutoff bound ΛP ΛR t ((nativeStep D Sc m cutoff bound ΛP ΛR l side t hv).obj Z) := by
  obtain ⟨up, i⟩ := l
  cases up <;> cases side
  · have hs := ContentHomSupport.shift_supported D Sc m cutoff bound
      (probeBlock D ΛP t) (reservoirBlock D ΛR (nextSector (false, i) false t))
      (homContentShift D i t.1) hZ
    have hi : ContentHomSupport.Supported D Sc m cutoff bound (probeBlock D ΛP t)
        (blockSucc D ΛR i (reservoirDown_edge D ΛR i t) (reservoirBlock D ΛR t))
        ((homParityShift (k := k) (homContentShift D i t.1)).obj Z) := by
      rw [reservoirBlock_down]
      exact hs
    exact ContentHomSupport.postF_supported D Sc m cutoff bound
      (probeBlock D ΛP t) (reservoirBlock D ΛR t) i (reservoirDown_edge D ΛR i t) hi
  · have hs := ContentHomSupport.preF_supported D Sc m cutoff bound
      (probeBlock D ΛP (nextSector (false, i) true t)) (reservoirBlock D ΛR t)
      i (probeDown_edge D ΛP i hv) hZ
    rw [probeBlock_down D ΛP i hv] at hs
    exact ContentHomSupport.shift_supported D Sc m cutoff bound
      (probeBlock D ΛP t) (reservoirBlock D ΛR t)
      (leftAdjParity D i (probeWeight D ΛP (nextSector (false, i) true t))) hs
  · have hs := ContentHomSupport.postE_supported D Sc m cutoff bound
      (probeBlock D ΛP t) (reservoirBlock D ΛR (nextSector (true, i) false t))
      i (reservoirUp_edge D ΛR i hv) hZ
    rw [reservoirBlock_up D ΛR i hv] at hs
    exact ContentHomSupport.shift_supported D Sc m cutoff bound
      (probeBlock D ΛP t) (reservoirBlock D ΛR t) (homContentShift D i t.1) hs
  · have hi : ContentHomSupport.Supported D Sc m cutoff bound
        (blockSucc D ΛP i (probeUp_edge D ΛP i t) (probeBlock D ΛP t))
        (reservoirBlock D ΛR t) Z := by
      rw [probeBlock_up]
      exact hZ
    exact ContentHomSupport.preE_supported D Sc m cutoff bound
      (reservoirBlock D ΛR t) i (probeUp_edge D ΛP i t) (probeBlock D ΛP t) hi

/-- The supported-sector step, keeping every native arrow between supported endpoints. -/
def step (l : Letter I) (side : Bool) (t : Sector I) (hv : StepValid l side t) :
    Superfunctor k (H D Sc m cutoff bound ΛP ΛR (nextSector l side t))
      (H D Sc m cutoff bound ΛP ΛR t) :=
  SupportedRestriction.functor
    (support D Sc m cutoff bound ΛP ΛR (nextSector l side t))
    (support D Sc m cutoff bound ΛP ΛR t)
    (nativeStep D Sc m cutoff bound ΛP ΛR l side t hv)
    (step_closed D Sc m cutoff bound ΛP ΛR l side t hv)

/-- The full inclusion recovers the literal native step on every supported object and map. -/
theorem step_inclusion (l : Letter I) (side : Bool) (t : Sector I) (hv : StepValid l side t) :
    (step D Sc m cutoff bound ΛP ΛR l side t hv).toFunctor ⋙
      inclusion D Sc m cutoff bound ΛP ΛR t =
    inclusion D Sc m cutoff bound ΛP ΛR (nextSector l side t) ⋙
      (nativeStep D Sc m cutoff bound ΛP ΛR l side t hv).toFunctor := rfl

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
