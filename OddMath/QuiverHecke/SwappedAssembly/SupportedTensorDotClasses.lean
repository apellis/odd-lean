import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorDotEntries

/-! # Literal supported tensor dot entries in quotient classes

SwappedVacuumCoordinates §§2–7: pull the literal chosen dot entry back
through its derived selected-Hom chart and the proved endpoint transport.
This identifies the entry used by every quotient-class observation without
a supplied generator-comparison hypothesis.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM BicategoryStruct
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
local instance tensorDotClassHomPi {k : Type u} [CommRing k] (A C : PiSCat.{u,u,u + 1} k) :
    PiSupercategory k (A ⟶ C) := PiTwoSupercategory.homPiLeft A C
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (L : I × ℕ → ℕ)
  (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "Sc'" => parameterTwist D Sc
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "P" => elvProbeReservoir D Sc m cutoff N ΛP ΛR hP hR

private def tensorEndpointCell {x y : X} (h : x = y)
    {F G : probeOldWeightSpace D (parameterTwist D Sc) m ΛP (-ΛP) ⟶
      elvWeightSpace D (parameterTwist D Sc) cutoff N ΛR x} (a : F ⟶ G) :
    (h ▸ F) ⟶ (h ▸ G) := by
  cases h
  exact a

section Dot
variable (ν : X) (u v : List (Letter I)) (i : I)
  {cL c : I →₀ ℕ} (hv : StepValid (true,i) false (0,c))
  (pL : SPath (SKM.lay D ν u (SKM.Shape.dot i) v).left (0,cL) (0,c))
  (hl : ∀ a ∈ (SKM.lay D ν u (SKM.Shape.dot i) v).left, a.l.1 = true)
  (pR : SPath (SKM.lay D ν u (SKM.Shape.dot i) v).right (0,c - Finsupp.single i 1) (0,0))
  (hr : ∀ a ∈ (SKM.lay D ν u (SKM.Shape.dot i) v).right, a.l.1 = true)
local notation "pg" => SPath.cons (Col.mk (up i) (SKM.wt D ν v)) false (0,c) hv (SPath.nil _)
local notation "p" => SPath.append (SPath.append pL pg) pR
local notation "Z" => ObjectProperty.FullSubcategory.obj (tensorVacuum D Sc m cutoff L ΛP ΛR)
local notation "h" => ProbeReservoir.reservoirVacuumEdge (P) i c hv

/-- The literal chosen dot cell pulled back through its selected tensor-Hom chart. -/
def tensorLayerDotRaw (a : (P).CrossCoeff) :
    End (ReservoirLayerCells.dotRawHom D Sc m cutoff L ΛP ΛR pL hl pR hr i h) :=
  (tensorHomEquivalence D Sc m cutoff L ΛP ΛR (ReservoirWord.weight D ΛR cL)).functor.preimage
    ((tensorLayerDotIso D Sc m cutoff L ΛP ΛR hP hR ν u v i hv pL hl pR hr).inv ≫
      (P).compLayer ((P).upwardGens a) (SKM.lay D ν u (SKM.Shape.dot i) v) p p Z ≫
        (tensorLayerDotIso D Sc m cutoff L ΛP ΛR hP hR ν u v i hv pL hl pR hr).hom)

/-- The pulled-back literal matrix entry is the original contextual factor dot. -/
theorem tensorLayerDotRaw_eq (a : (P).CrossCoeff) :
    tensorLayerDotRaw D Sc m cutoff L ΛP ΛR hP hR ν u v i hv pL hl pR hr a =
      ReservoirLayerCells.dotRaw D Sc m cutoff L ΛP ΛR pL hl pR hr i h := by
  let e := tensorLayerDotIso D Sc m cutoff L ΛP ΛR hP hR ν u v i hv pL hl pR hr
  let E := (tensorHomEquivalence D Sc m cutoff L ΛP ΛR (ReservoirWord.weight D ΛR cL)).functor
  have he := tensorLayerDot_square D Sc m cutoff L ΛP ΛR hP hR ν u v i hv pL hl pR hr a
  change (P).compLayer ((P).upwardGens a) (SKM.lay D ν u (SKM.Shape.dot i) v) p p Z ≫ e.hom =
    e.hom ≫ E.map (ReservoirLayerCells.dotRaw D Sc m cutoff L ΛP ΛR pL hl pR hr i h) at he
  have hc : e.inv ≫ (P).compLayer ((P).upwardGens a) (SKM.lay D ν u (SKM.Shape.dot i) v) p p Z ≫ e.hom =
      E.map (ReservoirLayerCells.dotRaw D Sc m cutoff L ΛP ΛR pL hl pR hr i h) := by
    rw [he]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  change E.preimage _ = _
  rw [hc,Functor.preimage_map]

local notation "νR" => (List.reverse (List.map (fun a => Prod.snd (SKM.Col.l a)) (Layer.right (SKM.lay D ν u (SKM.Shape.dot i) v))))
local notation "ηL" => (List.reverse (List.map (fun a => Prod.snd (SKM.Col.l a)) (Layer.left (SKM.lay D ν u (SKM.Shape.dot i) v))))

omit [Fintype I] in
private theorem dotEndpoint
    (pL : SPath (SKM.lay D ν u (SKM.Shape.dot i) v).left (0,cL) (0,c))
    (hl : ∀ a ∈ (SKM.lay D ν u (SKM.Shape.dot i) v).left, a.l.1 = true)
    (pR : SPath (SKM.lay D ν u (SKM.Shape.dot i) v).right (0,c - Finsupp.single i 1) (0,0))
    (hr : ∀ a ∈ (SKM.lay D ν u (SKM.Shape.dot i) v).right, a.l.1 = true)
    (hDot : ReservoirWord.weight D ΛR (c - Finsupp.single i 1) + D.α i =
      ReservoirWord.weight D ΛR c) : ReservoirWord.weight D ΛR cL =
    PowerWordWeightContexts.contextWeight D (PowerWordWeight.wordWeight D ΛR (νR ++ [i])) ηL :=
  (ReservoirContexts.word_weight D ΛR pL hl).trans
    (congrArg (fun x => PowerWordWeightContexts.contextWeight D x ηL)
      (hDot.symm.trans ((congrArg (fun x => x + D.α i)
        (TensorReservoirWords.path_weight D ΛR pR hr)).trans
          (PowerWordWeight.wordWeight_append D ΛR νR i))))

/-- The literal dot entry after only its proved outer endpoint-weight transport. -/
def tensorLayerDotAt (a : (P).CrossCoeff) :
    End (ReservoirLayerCells.dotHomAt D Sc m cutoff L ΛP ΛR pL hl pR hr i h) :=
  tensorEndpointCell D Sc m cutoff L ΛP ΛR
    (dotEndpoint D ΛR ν u v i pL hl pR hr h)
      (tensorLayerDotRaw D Sc m cutoff L ΛP ΛR hP hR ν u v i hv pL hl pR hr a)

/-- The literal selected-Hom matrix cell equals the original-weight dot cell. -/
theorem tensorLayerDotAt_eq (a : (P).CrossCoeff) :
    tensorLayerDotAt D Sc m cutoff L ΛP ΛR hP hR ν u v i hv pL hl pR hr a =
      ReservoirLayerCells.dotAt D Sc m cutoff L ΛP ΛR pL hl pR hr i h := by
  unfold tensorLayerDotAt
  rw [tensorLayerDotRaw_eq]
  unfold ReservoirLayerCells.dotAt
  rfl

/-- Every source vector has the original affine dot quotient class after applying
  the literal supported matrix entry. Only its input class is prescribed. -/
theorem tensorLayerDot_class_square (a : (P).CrossCoeff)
    (G : probeOldWeightSpace D (parameterTwist D Sc) m ΛP (-ΛP) ⟶ elvWeightSpace D (parameterTwist D Sc) cutoff N ΛR
      (PowerWordWeightContexts.contextWeight D (PowerWordWeight.wordWeight D ΛR (νR ++ [i])) ηL))
    (f : G ⟶ ReservoirLayerCells.dotHomAt D Sc m cutoff L ΛP ΛR pL hl pR hr i h)
    (s : List I) (β : WeightBlocks D ΛR
      (PowerWordWeightContexts.contextWeight D (PowerWordWeight.wordWeight D ΛR (νR ++ [i])) ηL))
    (hs : (s.reverse : Multiset I) = β.1)
    (z : ((G.obj (WeightTensorVacuum.regularProbe D (parameterTwist D Sc) m ΛP)) β).obj
      (⟨⟨s.reverse⟩,hs⟩ : ContentCategory D (parameterTwist D Sc) cutoff N β.1))
    (y : coefficientObj D Sc s ⟶ coefficientObj D Sc (PowerWordLayerClasses.domWord νR ηL (.dot i)))
    (hy : PowerWordQuotientCoordinates.coordinate D Sc cutoff L s (PowerWordLayerClasses.domWord νR ηL (.dot i))
      (TensorLayerClasses.dotVector D Sc cutoff L m ΛP ΛR νR ηL i G
        (f ≫ eqToHom (ReservoirLayerCells.dotHomAt_eq D Sc m cutoff L ΛP ΛR pL hl pR hr i h)) s β hs z) =
      (PowerWordQuotientCoordinates.kernel D Sc cutoff L s (PowerWordLayerClasses.domWord νR ηL (.dot i))).mkQ y) :
    PowerWordQuotientCoordinates.coordinate D Sc cutoff L s (PowerWordLayerClasses.codWord νR ηL (.dot i))
      (TensorLayerClasses.dotVector D Sc cutoff L m ΛP ΛR νR ηL i G
        ((f ≫ tensorLayerDotAt D Sc m cutoff L ΛP ΛR hP hR ν u v i hv pL hl pR hr a) ≫
          eqToHom (ReservoirLayerCells.dotHomAt_eq D Sc m cutoff L ΛP ΛR pL hl pR hr i h)) s β hs z) =
      (PowerWordQuotientCoordinates.kernel D Sc cutoff L s (PowerWordLayerClasses.codWord νR ηL (.dot i))).mkQ
        (y ≫ sourceCoefficientHom D Sc 1 (ContextualOldGenerators.layerDiagram D Sc (List.reverse ηL) (.dot i) (List.reverse νR))) := by
  rw [tensorLayerDotAt_eq]
  exact ReservoirLayerCells.dot_class_square D Sc m cutoff L ΛP ΛR pL hl pR hr i h
    G f s β hs z y hy
end Dot
end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
