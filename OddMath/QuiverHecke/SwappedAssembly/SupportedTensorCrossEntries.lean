import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorDotEntries
import OddMath.QuiverHecke.SwappedAssembly.ReservoirContextCoordinates
import OddMath.QuiverHecke.SwappedAssembly.ReservoirLayerDistinctCrossings

/-! # Chosen crossing matrix entries in the selected tensor Hom

SwappedVacuumCoordinates §§2–6: retain the literal chosen upward crossing,
both actual reservoir paths, and the prescribed middle weight vertices when
passing to the supported tensor vacuum. No presentation or inverse premise
is imposed on the crossing coefficient.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM BicategoryStruct
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
local instance tensorCrossHomPi {k : Type u} [CommRing k] (A C : PiSCat.{u,u,u + 1} k) :
    PiSupercategory k (A ⟶ C) := PiTwoSupercategory.homPiLeft A C
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (L : I × ℕ → ℕ)
  (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "P" => elvProbeReservoir D Sc m cutoff N ΛP ΛR hP hR
local notation "Z" => ObjectProperty.FullSubcategory.obj (tensorVacuum D Sc m cutoff L ΛP ΛR)

section Same
variable (ν : X) (u v : List (Letter I)) (i : I)
  {cL c : I →₀ ℕ} (hv : StepValid (true,i) false (0,c))
  (hw : StepValid (true,i) false (nextSector (true,i) false (0,c)))
  (pL : SPath (SKM.lay D ν u (.cross i i) v).left (0,cL) (0,c))
  (hl : ∀ a ∈ (SKM.lay D ν u (.cross i i) v).left, a.l.1 = true)
  (pR : SPath (SKM.lay D ν u (.cross i i) v).right
    (0,c - Finsupp.single i 1 - Finsupp.single i 1) (0,0))
  (hr : ∀ a ∈ (SKM.lay D ν u (.cross i i) v).right, a.l.1 = true)
local notation "pg" => SPath.cons (Col.mk (up i) (SKM.wt D (SKM.wt D ν v) [up i]))
  false (0,c) hv (SPath.cons (Col.mk (up i) (SKM.wt D ν v)) false _ hw (SPath.nil _))
local notation "p" => SPath.append (SPath.append pL pg) pR
local notation "h₁" => ProbeReservoir.reservoirVacuumEdge (P) i (c - Finsupp.single i 1) hw
local notation "h₂" => ProbeReservoir.reservoirVacuumEdge (P) i c hv

/-- The chosen equal-colour crossing path in the selected tensor-Hom chart. -/
def tensorLayerSameCrossIso :
    ((P).pathFunctor p).obj Z ≅
      (tensorHomEquivalence D Sc m cutoff L ΛP ΛR (ReservoirWord.weight D ΛR cL)).functor.obj
        (ReservoirLayerCells.crossRawHom D Sc m cutoff L ΛP ΛR pL hl pR hr i i h₁ h₂) :=
  (P).reservoirLayerSameCrossIso ν u v i hv hw pL pR Z ≪≫
    tensorContextIso D Sc m cutoff L ΛP ΛR hP hR pL hl pR hr ((P).W.E i h₁ ≫ (P).W.E i h₂)

/-- The literal equal-colour crossing matrix entry is the prescribed tensor-Hom crossing. -/
theorem tensorLayerSameCross_square (a : (P).CrossCoeff) :
    (P).compLayer ((P).upwardGens a) (SKM.lay D ν u (.cross i i) v) p p Z ≫
        (tensorLayerSameCrossIso D Sc m cutoff L ΛP ΛR hP hR ν u v i hv hw pL hl pR hr).hom =
      (tensorLayerSameCrossIso D Sc m cutoff L ΛP ΛR hP hR ν u v i hv hw pL hl pR hr).hom ≫
        (tensorHomEquivalence D Sc m cutoff L ΛP ΛR (ReservoirWord.weight D ΛR cL)).functor.map
          (ReservoirLayerCells.crossRaw D Sc m cutoff L ΛP ΛR pL hl pR hr i i h₁ h₂ h₁ h₂) := by
  let F := (P).pathFunctor pL
  let Y := ((P).pathFunctor pR).obj Z
  let e := (homContentPostWordIso (P).T.obj (P).W i 0 ((P).muP (0,c)) h₁ h₂).app Y
  let g := Y ◁ (P).W.cross i i h₁ h₂ h₁ h₂
  have hc : (P).crossImage a i i (SKM.wt D ν v) pg pg Y = e.hom ≫ g ≫ e.inv := by
    rw [ProbeReservoir.crossImage]
    split_ifs with hii
    · rfl
    · exact False.elim (hii rfl)
  have hm : (P).crossImage a i i (SKM.wt D ν v) pg pg Y ≫ e.hom = e.hom ≫ g := by
    rw [hc]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hs : (P).compLayer ((P).upwardGens a) (SKM.lay D ν u (.cross i i) v) p p Z ≫
      ((P).reservoirLayerSameCrossIso ν u v i hv hw pL pR Z).hom =
    ((P).reservoirLayerSameCrossIso ν u v i hv hw pL pR Z).hom ≫ F.map g := by
    rw [(P).compLayer_eq ((P).upwardGens a) _ pL pg pg pR Z]
    let q := (P).pathFunctor_append_append_obj pL pg pR Z
    change (eqToHom q ≫ F.map ((P).crossImage a i i (SKM.wt D ν v) pg pg Y) ≫ eqToHom q.symm) ≫
      (eqToHom q ≫ F.map e.hom) = (eqToHom q ≫ F.map e.hom) ≫ F.map g
    have hh := congrArg F.map hm
    simp only [Functor.map_comp] at hh
    simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] using
      congrArg (fun f => eqToHom q ≫ f) hh
  let e₀ := (P).reservoirLayerSameCrossIso ν u v i hv hw pL pR Z
  let e₁ := tensorContextIso D Sc m cutoff L ΛP ΛR hP hR pL hl pR hr ((P).W.E i h₁ ≫ (P).W.E i h₂)
  change _ ≫ (e₀.hom ≫ e₁.hom) = (e₀.hom ≫ e₁.hom) ≫ _
  rw [← Category.assoc, hs, Category.assoc]
  rw [tensorContext_square D Sc m cutoff L ΛP ΛR hP hR pL hl pR hr ((P).W.cross i i h₁ h₂ h₁ h₂)]
  simp only [Category.assoc]
  rfl
end Same

private def crossRightPath {r : List (Col I X)} {cR cR' : I →₀ ℕ}
    (h : cR = cR') (pR : SPath r (0,cR') (0,0)) : SPath r (0,cR) (0,0) := by
  subst cR'
  exact pR

private def crossRightValue {cR cR' : I →₀ ℕ} (h : ((0,cR) : Sector I) = (0,cR'))
    (Y : (P).H (0,cR')) : (P).H (0,cR) := h ▸ Y

private def tensorCrossContextIso {l r : List (Col I X)} {cL cM cR cR' : I →₀ ℕ}
    (h : ((0,cR) : Sector I) = (0,cR'))
    (pL : SPath l (0,cL) (0,cM)) (hl : ∀ a ∈ l, a.l.1 = true)
    (pR : SPath r (0,cR') (0,0)) (hr : ∀ a ∈ r, a.l.1 = true)
    (A : (P).W.obj ((P).muM (0,cR)) ⟶ (P).W.obj ((P).muM (0,cM))) :
    ((P).pathFunctor pL).obj (crossRightValue D Sc m cutoff L ΛP ΛR hP hR (cR := cR) (cR' := cR') h
        (((P).pathFunctor pR).obj Z) ≫ A) ≅
      (tensorHomEquivalence D Sc m cutoff L ΛP ΛR (ReservoirWord.weight D ΛR cL)).functor.obj
        (tensorContextHom D Sc m cutoff L ΛP ΛR hP hR pL hl
          (crossRightPath (congrArg Prod.snd h) pR) hr A) := by
  have hc : cR = cR' := congrArg Prod.snd h
  subst cR'
  exact tensorContextIso D Sc m cutoff L ΛP ΛR hP hR pL hl pR hr A

private theorem tensorCrossContext_square {l r : List (Col I X)} {cL cM cR cR' : I →₀ ℕ}
    (h : ((0,cR) : Sector I) = (0,cR'))
    (pL : SPath l (0,cL) (0,cM)) (hl : ∀ a ∈ l, a.l.1 = true)
    (pR : SPath r (0,cR') (0,0)) (hr : ∀ a ∈ r, a.l.1 = true)
    {A B : (P).W.obj ((P).muM (0,cR)) ⟶ (P).W.obj ((P).muM (0,cM))} (a : A ⟶ B) :
    ((P).pathFunctor pL).map (crossRightValue D Sc m cutoff L ΛP ΛR hP hR (cR := cR) (cR' := cR') h
        (((P).pathFunctor pR).obj Z) ◁ a) ≫
        (tensorCrossContextIso D Sc m cutoff L ΛP ΛR hP hR h pL hl pR hr B).hom =
      (tensorCrossContextIso D Sc m cutoff L ΛP ΛR hP hR h pL hl pR hr A).hom ≫
        (tensorHomEquivalence D Sc m cutoff L ΛP ΛR (ReservoirWord.weight D ΛR cL)).functor.map
          ((TensorReservoirWords.pathHom D (parameterTwist D Sc) m cutoff L ΛP ΛR
            (crossRightPath (congrArg Prod.snd h) pR) hr ◁ a) ▷
              ReservoirWord.word (P).W.toRouquierData ΛR pL hl) := by
  have hc : cR = cR' := congrArg Prod.snd h
  subst cR'
  exact tensorContext_square D Sc m cutoff L ΛP ΛR hP hR pL hl pR hr a

section Distinct
variable (ν : X) (u v : List (Letter I)) (i j : I)
  {cL c : I →₀ ℕ}
  (hv₁ : StepValid (true,i) false (0,c))
  (hv₂ : StepValid (true,j) false (nextSector (true,i) false (0,c)))
  (hw₁ : StepValid (true,j) false (0,c))
  (hw₂ : StepValid (true,i) false (nextSector (true,j) false (0,c)))
  (hs : nextSector (true,j) false (nextSector (true,i) false (0,c)) =
    nextSector (true,i) false (nextSector (true,j) false (0,c)))
  (pL : SPath (SKM.lay D ν u (.cross i j) v).left (0,cL) (0,c))
  (hl : ∀ a ∈ (SKM.lay D ν u (.cross i j) v).left, a.l.1 = true)
  (pR : SPath (SKM.lay D ν u (.cross i j) v).right
    (0,c - Finsupp.single j 1 - Finsupp.single i 1) (0,0))
  (hr : ∀ a ∈ (SKM.lay D ν u (.cross i j) v).right, a.l.1 = true)
local notation "ps" => SPath.two (c₁ := Col.mk (up i) (SKM.wt D (SKM.wt D ν v) [up j]))
  (c₂ := Col.mk (up j) (SKM.wt D ν v)) false false hv₁ hv₂ hs
local notation "pt" => SPath.two (c₁ := Col.mk (up j) (SKM.wt D (SKM.wt D ν v) [up i]))
  (c₂ := Col.mk (up i) (SKM.wt D ν v)) false false hw₁ hw₂ rfl
local notation "p" => SPath.append (SPath.append pL ps) pR
local notation "q" => SPath.append (SPath.append pL pt) pR
local notation "r" => crossRightPath (congrArg Prod.snd hs) pR
local notation "h₁" => ProbeReservoir.reservoirVacuumEdge (P) j (c - Finsupp.single i 1) hv₂
local notation "h₂" => ProbeReservoir.reservoirVacuumEdge (P) i c hv₁
local notation "h₄" => ProbeReservoir.reservoirVacuumEdge (P) j c hw₁

private theorem tensorCrossEdge
    (hw₂ : StepValid (true,i) false (nextSector (true,j) false (0,c)))
    (hs : nextSector (true,j) false (nextSector (true,i) false (0,c)) =
      nextSector (true,i) false (nextSector (true,j) false (0,c))) :
    (P).muM (0,c - Finsupp.single i 1 - Finsupp.single j 1) + D.α i =
      (P).muM (0,c - Finsupp.single j 1) := by
  change (P).muM (nextSector (true,j) false (nextSector (true,i) false (0,c))) + D.α i = _
  rw [hs]
  exact (P).reservoirVacuumEdge i (c - Finsupp.single j 1) hw₂
local notation "h₃" => tensorCrossEdge D Sc m cutoff L ΛP ΛR hP hR i j hw₂ hs

/-- The literal distinct-colour source path in the selected tensor Hom.
The crossing's original right-path reindexing is retained. -/
def tensorLayerCrossSourceIso :
    ((P).pathFunctor p).obj Z ≅
      (tensorHomEquivalence D Sc m cutoff L ΛP ΛR (ReservoirWord.weight D ΛR cL)).functor.obj
        (ReservoirLayerCells.crossRawHom D Sc m cutoff L ΛP ΛR pL hl r hr i j h₁ h₂) :=
  (P).reservoirLayerCrossSourceIso ν u v i j hv₁ hv₂ hs pL pR Z ≪≫
    tensorCrossContextIso D Sc m cutoff L ΛP ΛR hP hR hs pL hl pR hr
      ((P).W.E j h₁ ≫ (P).W.E i h₂)

/-- The literal distinct-colour target path with the same transported right word. -/
def tensorLayerCrossTargetIso :
    ((P).pathFunctor q).obj Z ≅
      (tensorHomEquivalence D Sc m cutoff L ΛP ΛR (ReservoirWord.weight D ΛR cL)).functor.obj
        (ReservoirLayerCells.crossRawHom D Sc m cutoff L ΛP ΛR pL hl r hr j i h₃ h₄) :=
  (P).reservoirLayerCrossTargetIso ν u v i j hw₁ hw₂ hs pL pR Z ≪≫
    tensorCrossContextIso D Sc m cutoff L ΛP ΛR hP hR hs pL hl pR hr
      ((P).W.E i h₃ ≫ (P).W.E j h₄)

/-- The chosen distinct-colour matrix entry, with its original source cast,
is the prescribed factor crossing in the selected tensor Hom. -/
theorem tensorLayerCross_square (a : (P).CrossCoeff) (hij : i ≠ j) :
    (P).compLayer ((P).upwardGens a) (SKM.lay D ν u (.cross i j) v) p q Z ≫
        (tensorLayerCrossTargetIso D Sc m cutoff L ΛP ΛR hP hR ν u v i j hw₁ hw₂ hs pL hl pR hr).hom =
      (tensorLayerCrossSourceIso D Sc m cutoff L ΛP ΛR hP hR ν u v i j hv₁ hv₂ hs pL hl pR hr).hom ≫
        (tensorHomEquivalence D Sc m cutoff L ΛP ΛR (ReservoirWord.weight D ΛR cL)).functor.map
          (ReservoirLayerCells.crossRaw D Sc m cutoff L ΛP ΛR pL hl r hr i j h₁ h₂ h₃ h₄) := by
  let F := (P).pathFunctor pL
  let Y := ((P).pathFunctor pR).obj Z
  let eS := (P).reservoirCrossSourceIso (SKM.wt D ν v) i j c hv₁ hv₂ hs Y
  let eT := (P).reservoirCrossTargetIso (SKM.wt D ν v) i j c hw₁ hw₂ hs Y
  let g := crossRightValue D Sc m cutoff L ΛP ΛR hP hR
    (cR := c - Finsupp.single i 1 - Finsupp.single j 1)
    (cR' := c - Finsupp.single j 1 - Finsupp.single i 1) hs Y ◁ (P).W.cross i j h₁ h₂ h₃ h₄
  have hm := congrArg F.map ((P).crossImage_reservoirVacuum a (SKM.wt D ν v)
    i j hij c hv₁ hv₂ hw₁ hw₂ hs Y)
  simp only [Functor.map_comp] at hm
  change F.map ((P).crossImage a i j (SKM.wt D ν v) ps pt Y) ≫ F.map eT.hom =
    F.map eS.hom ≫ F.map g at hm
  have he : (P).compLayer ((P).upwardGens a) (SKM.lay D ν u (.cross i j) v) p q Z ≫
      ((P).reservoirLayerCrossTargetIso ν u v i j hw₁ hw₂ hs pL pR Z).hom =
    ((P).reservoirLayerCrossSourceIso ν u v i j hv₁ hv₂ hs pL pR Z).hom ≫ F.map g := by
    rw [(P).compLayer_eq ((P).upwardGens a) _ pL ps pt pR Z]
    let qs := (P).pathFunctor_append_append_obj pL ps pR Z
    let qt := (P).pathFunctor_append_append_obj pL pt pR Z
    change (eqToHom qs ≫ F.map ((P).crossImage a i j (SKM.wt D ν v) ps pt Y) ≫ eqToHom qt.symm) ≫
      (eqToHom qt ≫ F.map eT.hom) = (eqToHom qs ≫ F.map eS.hom) ≫ F.map g
    simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] using
      congrArg (fun f => eqToHom qs ≫ f) hm
  let dS := (P).reservoirLayerCrossSourceIso ν u v i j hv₁ hv₂ hs pL pR Z
  let dT := (P).reservoirLayerCrossTargetIso ν u v i j hw₁ hw₂ hs pL pR Z
  let fS := tensorCrossContextIso D Sc m cutoff L ΛP ΛR hP hR hs pL hl pR hr
    ((P).W.E j h₁ ≫ (P).W.E i h₂)
  let fT := tensorCrossContextIso D Sc m cutoff L ΛP ΛR hP hR hs pL hl pR hr
    ((P).W.E i h₃ ≫ (P).W.E j h₄)
  change _ ≫ (dT.hom ≫ fT.hom) = (dS.hom ≫ fS.hom) ≫ _
  rw [← Category.assoc, he, Category.assoc]
  rw [tensorCrossContext_square D Sc m cutoff L ΛP ΛR hP hR hs pL hl pR hr
    ((P).W.cross i j h₁ h₂ h₃ h₄)]
  simp only [Category.assoc]
  rfl
end Distinct
end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
