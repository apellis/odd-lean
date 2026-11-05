import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorRows
import OddMath.QuiverHecke.SwappedAssembly.SupportedMatrixLayers

/-! # Literal layer postcomposition on the supported tensor source row

SwappedVacuumCoordinates §5: observing the specified source row of the
existing supported local interpretation gives chronological postcomposition
by its literal `compLayer`. A target-family equality only normalizes the
chosen terminal object; the concrete tensor specialization supplies this
equality from its constructed family. No presentation or inverse premise
is used for the layer calculation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
local instance tensorRowLayersHomPi {k : Type u} [CommRing k] (A C : PiSCat.{u,u,u + 1} k) :
    PiSupercategory k (A ⟶ C) := PiTwoSupercategory.homPiLeft A C
namespace MatrixSourceRow
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (bound : ℕ) (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
  (Gs Ys : ∀ t, H D (parameterTwist D Sc) m cutoff bound ΛP ΛR t)
  (sl : Sector I)
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR
local notation "Q" => interpretation D Sc m cutoff bound ΛP ΛR hP hR Gs Ys

/-- The actual supported one-layer operation becomes postcomposition by the literal matrix entry. -/
theorem projection_layer (gens : (P).Generators) (A : Layer (SKM.sig D)) (hA : A.Valid)
    (hEnd : (ΛP - contentWeight D (0 : I →₀ ℕ)) + (-ΛR + contentWeight D (0 : I →₀ ℕ)) = A.cod.endR)
    (p : SPath A.dom.word sl (0,0)) (q : SPath A.cod.word sl (0,0))
    (hup : ∀ c ∈ A.dom.word, c.l.1 = true)
    (x : matrixModule D Sc m cutoff bound ΛP ΛR Gs Ys A.dom) :
    projection D Sc m cutoff bound ΛP ΛR hP hR Gs Ys sl (a := A.cod) hEnd q
      ((Q gens).res A.cod ((Q gens).op A ((Q gens).ext A.dom x))) =
      projection D Sc m cutoff bound ΛP ΛR hP hR Gs Ys sl (a := A.dom)
        (hEnd.trans hA.endR_eq) p x ≫ (P).compLayer gens A p q (Ys (0,0)).obj := by
  change (matrixEquiv D Sc m cutoff bound ΛP ΛR hP hR Gs Ys A.cod
    ((Q gens).res A.cod ((Q gens).op A ((Q gens).ext A.dom x)))) sl ⟨(0,0),hEnd⟩ q = _
  rw [interpretation_layer]
  exact (P).layerMap_reservoir gens A hA hup
    (matrixEquiv D Sc m cutoff bound ΛP ΛR hP hR Gs Ys A.dom x)
    sl ⟨(0,0),hEnd⟩ rfl p q

/-- Normalize the terminal family value by its specified equality, keeping the entire source Hom. -/
def projectionAt {a : Obj (SKM.sig D)}
    (hEnd : (ΛP - contentWeight D (0 : I →₀ ℕ)) + (-ΛR + contentWeight D (0 : I →₀ ℕ)) = a.endR)
    (p : SPath a.word sl (0,0)) (Z : (P).H (0,0)) (hZ : (Ys (0,0)).obj = Z) :=
  (Linear.homCongr k (Iso.refl (Gs sl).obj)
    (eqToIso (congrArg ((P).pathFunctor p).obj hZ))).toLinearMap.comp
      (projection D Sc m cutoff bound ΛP ΛR hP hR Gs Ys sl hEnd p)

/-- A specified terminal family value gives its literal one-layer postcomposition square.
The concrete tensor family supplies the equality used here. -/
theorem projectionAt_layer (gens : (P).Generators) (A : Layer (SKM.sig D)) (hA : A.Valid)
    (hEnd : (ΛP - contentWeight D (0 : I →₀ ℕ)) + (-ΛR + contentWeight D (0 : I →₀ ℕ)) = A.cod.endR)
    (p : SPath A.dom.word sl (0,0)) (q : SPath A.cod.word sl (0,0))
    (hup : ∀ c ∈ A.dom.word, c.l.1 = true)
    (Z : (P).H (0,0)) (hZ : (Ys (0,0)).obj = Z)
    (x : matrixModule D Sc m cutoff bound ΛP ΛR Gs Ys A.dom) :
    projectionAt D Sc m cutoff bound ΛP ΛR hP hR Gs Ys sl (a := A.cod) hEnd q Z hZ
      ((Q gens).res A.cod ((Q gens).op A ((Q gens).ext A.dom x))) =
      projectionAt D Sc m cutoff bound ΛP ΛR hP hR Gs Ys sl (a := A.dom)
        (hEnd.trans hA.endR_eq) p Z hZ x ≫ (P).compLayer gens A p q Z := by
  cases hZ
  simpa [projectionAt,Linear.homCongr_apply] using
    projection_layer D Sc m cutoff bound ΛP ΛR hP hR Gs Ys sl gens A hA hEnd p q hup x
end MatrixSourceRow

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (ΛP ΛR : X) (L : I × ℕ → ℕ)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR) (s : List I)
  {a : Obj (SKM.sig D)}
  (hEnd : (ΛP - contentWeight D (0 : I →₀ ℕ)) + (-ΛR + contentWeight D (0 : I →₀ ℕ)) = a.endR)
  (p : SPath a.word (0,tensorSourceContent D ΛP ΛR s) (0,0))

/-- Actual matrix-row observation at the literal constructed tensor vacuum. -/
def tensorVacuumRowProjection :=
  MatrixSourceRow.projectionAt D Sc m cutoff (PowerWordContent.powerBound D cutoff L) ΛP ΛR hP hR
    (tensorSourceFamily D Sc m cutoff ΛP ΛR L s) (tensorTargetFamily D Sc m cutoff ΛP ΛR L)
    (0,tensorSourceContent D ΛP ΛR s) hEnd p (tensorVacuum D Sc m cutoff L ΛP ΛR).obj
    (congrArg (fun Z : H D (parameterTwist D Sc) m cutoff (PowerWordContent.powerBound D cutoff L)
      ΛP ΛR (0,0) => Z.obj) (tensorTargetFamily_zero D Sc m cutoff ΛP ΛR L))

/-- The constructed supported tensor matrix action is literal postcomposition at its chosen vacuum. -/
theorem tensorVacuumRowProjection_layer
    (gens : (elvProbeReservoir D Sc m cutoff (PowerWordContent.powerBound D cutoff L) ΛP ΛR hP hR).Generators)
    (A : Layer (SKM.sig D)) (hA : A.Valid)
    (hEndA : (ΛP - contentWeight D (0 : I →₀ ℕ)) + (-ΛR + contentWeight D (0 : I →₀ ℕ)) = A.cod.endR)
    (pA : SPath A.dom.word (0,tensorSourceContent D ΛP ΛR s) (0,0))
    (qA : SPath A.cod.word (0,tensorSourceContent D ΛP ΛR s) (0,0))
    (hup : ∀ c ∈ A.dom.word, c.l.1 = true)
    (x : matrixModule D Sc m cutoff (PowerWordContent.powerBound D cutoff L) ΛP ΛR
      (tensorSourceFamily D Sc m cutoff ΛP ΛR L s) (tensorTargetFamily D Sc m cutoff ΛP ΛR L) A.dom) :
    tensorVacuumRowProjection D Sc m cutoff ΛP ΛR L hP hR s (a := A.cod) hEndA qA
      ((interpretation D Sc m cutoff (PowerWordContent.powerBound D cutoff L) ΛP ΛR hP hR
        (tensorSourceFamily D Sc m cutoff ΛP ΛR L s) (tensorTargetFamily D Sc m cutoff ΛP ΛR L) gens).res A.cod
        ((interpretation D Sc m cutoff (PowerWordContent.powerBound D cutoff L) ΛP ΛR hP hR
          (tensorSourceFamily D Sc m cutoff ΛP ΛR L s) (tensorTargetFamily D Sc m cutoff ΛP ΛR L) gens).op A
          ((interpretation D Sc m cutoff (PowerWordContent.powerBound D cutoff L) ΛP ΛR hP hR
            (tensorSourceFamily D Sc m cutoff ΛP ΛR L s) (tensorTargetFamily D Sc m cutoff ΛP ΛR L) gens).ext A.dom x))) =
      tensorVacuumRowProjection D Sc m cutoff ΛP ΛR L hP hR s (a := A.dom)
        (hEndA.trans hA.endR_eq) pA x ≫
        (elvProbeReservoir D Sc m cutoff (PowerWordContent.powerBound D cutoff L) ΛP ΛR hP hR).compLayer
          gens A pA qA (tensorVacuum D Sc m cutoff L ΛP ΛR).obj :=
  MatrixSourceRow.projectionAt_layer D Sc m cutoff (PowerWordContent.powerBound D cutoff L) ΛP ΛR hP hR
    (tensorSourceFamily D Sc m cutoff ΛP ΛR L s) (tensorTargetFamily D Sc m cutoff ΛP ΛR L)
    (0,tensorSourceContent D ΛP ΛR s) gens A hA hEndA pA qA hup
    (tensorVacuum D Sc m cutoff L ΛP ΛR).obj
    (congrArg (fun Z : H D (parameterTwist D Sc) m cutoff (PowerWordContent.powerBound D cutoff L)
      ΛP ΛR (0,0) => Z.obj) (tensorTargetFamily_zero D Sc m cutoff ΛP ΛR L)) x

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
