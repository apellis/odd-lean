import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorContexts

/-! # Chosen dot matrix entries in the selected tensor Hom

SwappedVacuumCoordinates §§2–6: the literal `compLayer` of the chosen
upward generators, on its occupied reservoir path, is the prescribed
`ReservoirLayerCells.dotRaw` through the selected tensor-context chart.
Both outer labelled paths and the original middle weight certificate are
retained. No central inverse or presentation relation is assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM BicategoryStruct
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
local instance tensorDotHomPi {k : Type u} [CommRing k] (A C : PiSCat.{u,u,u + 1} k) :
    PiSupercategory k (A ⟶ C) := PiTwoSupercategory.homPiLeft A C
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (L : I × ℕ → ℕ)
  (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "Sc'" => parameterTwist D Sc
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "P" => elvProbeReservoir D Sc m cutoff N ΛP ΛR hP hR

section Dot
variable (ν : X) (u v : List (Letter I)) (i : I)
  {cL c : I →₀ ℕ} (hv : StepValid (true,i) false (0,c))
  (pL : SPath (SKM.lay D ν u (.dot i) v).left (0,cL) (0,c))
  (hl : ∀ a ∈ (SKM.lay D ν u (.dot i) v).left, a.l.1 = true)
  (pR : SPath (SKM.lay D ν u (.dot i) v).right (0,c - Finsupp.single i 1) (0,0))
  (hr : ∀ a ∈ (SKM.lay D ν u (.dot i) v).right, a.l.1 = true)
local notation "pg" => SPath.cons (Col.mk (up i) (SKM.wt D ν v)) false (0,c) hv (SPath.nil _)
local notation "p" => SPath.append (SPath.append pL pg) pR
local notation "Z" => ObjectProperty.FullSubcategory.obj (tensorVacuum D Sc m cutoff L ΛP ΛR)
local notation "h" => ProbeReservoir.reservoirVacuumEdge (P) i c hv

/-- The chosen dot path, with its prescribed middle-strand and tensor-context charts. -/
def tensorLayerDotIso :
    ((P).pathFunctor p).obj Z ≅
      (tensorHomEquivalence D Sc m cutoff L ΛP ΛR (ReservoirWord.weight D ΛR cL)).functor.obj
        (ReservoirLayerCells.dotRawHom D Sc m cutoff L ΛP ΛR pL hl pR hr i h) :=
  (P).reservoirLayerDotIso ν u v i hv pL pR Z ≪≫
    tensorContextIso D Sc m cutoff L ΛP ΛR hP hR pL hl pR hr ((P).W.E i h)

/-- The literal chosen upward dot matrix entry has the selected tensor-Hom dot square. -/
theorem tensorLayerDot_square (a : (P).CrossCoeff) :
    (P).compLayer ((P).upwardGens a) (SKM.lay D ν u (.dot i) v) p p Z ≫
        (tensorLayerDotIso D Sc m cutoff L ΛP ΛR hP hR ν u v i hv pL hl pR hr).hom =
      (tensorLayerDotIso D Sc m cutoff L ΛP ΛR hP hR ν u v i hv pL hl pR hr).hom ≫
        (tensorHomEquivalence D Sc m cutoff L ΛP ΛR (ReservoirWord.weight D ΛR cL)).functor.map
          (ReservoirLayerCells.dotRaw D Sc m cutoff L ΛP ΛR pL hl pR hr i h) := by
  let F := (P).pathFunctor pL
  let Y := ((P).pathFunctor pR).obj Z
  let e := reservoirVacuumPostIso (P).T.obj (P).W i ((P).muP (0,c)) h Y
  let q := (P).pathFunctor_append_append_obj pL pg pR Z
  have hm := congrArg F.map ((P).dotImage_reservoirVacuum i (SKM.wt D ν v) c hv hv Y)
  simp only [Functor.map_comp, SKM.wt_nil] at hm
  have hs : (P).compLayer ((P).upwardGens a) (SKM.lay D ν u (.dot i) v) p p Z ≫
      ((P).reservoirLayerDotIso ν u v i hv pL pR Z).hom =
    ((P).reservoirLayerDotIso ν u v i hv pL pR Z).hom ≫ F.map (Y ◁ (P).W.dot i h) := by
    rw [(P).compLayer_eq ((P).upwardGens a) _ pL pg pg pR Z]
    change (eqToHom q ≫ F.map ((P).dotImage i (SKM.wt D ν v) pg pg Y) ≫ eqToHom q.symm) ≫
      (eqToHom q ≫ F.map e.hom) = (eqToHom q ≫ F.map e.hom) ≫ F.map (Y ◁ (P).W.dot i h)
    simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] using
      congrArg (fun f => eqToHom q ≫ f) hm
  let e₀ := (P).reservoirLayerDotIso ν u v i hv pL pR Z
  let e₁ := tensorContextIso D Sc m cutoff L ΛP ΛR hP hR pL hl pR hr ((P).W.E i h)
  let E := (tensorHomEquivalence D Sc m cutoff L ΛP ΛR (ReservoirWord.weight D ΛR cL)).functor
  let b := ReservoirLayerCells.dotRaw D Sc m cutoff L ΛP ΛR pL hl pR hr i h
  change (P).compLayer ((P).upwardGens a) (SKM.lay D ν u (.dot i) v) p p Z ≫
    (e₀.hom ≫ e₁.hom) = (e₀.hom ≫ e₁.hom) ≫ E.map b
  calc
    _ = ((P).compLayer ((P).upwardGens a) (SKM.lay D ν u (.dot i) v) p p Z ≫ e₀.hom) ≫
        e₁.hom := (Category.assoc _ _ _).symm
    _ = (e₀.hom ≫ F.map (Y ◁ (P).W.dot i h)) ≫ e₁.hom :=
      congrArg (fun f => f ≫ e₁.hom) hs
    _ = e₀.hom ≫ (F.map (Y ◁ (P).W.dot i h) ≫ e₁.hom) := Category.assoc _ _ _
    _ = e₀.hom ≫ (e₁.hom ≫ E.map b) := congrArg (fun f => e₀.hom ≫ f)
      (tensorContext_square D Sc m cutoff L ΛP ΛR hP hR pL hl pR hr ((P).W.dot i h))
    _ = _ := (Category.assoc _ _ _).symm

end Dot
end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
