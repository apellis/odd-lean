import OddMath.QuiverHecke.SwappedAssembly.ReservoirWordFunctorStrict
import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorEntryLayerCharts

/-! # Global and local tensor layer charts are identity transports

SwappedVacuumCoordinates §§5–7. In the strict 2-supercategory `Π-𝔖ℭ𝔞𝔱`,
the global path chart `tensorRowTargetIso` and the local dot chart
`tensorLayerDotIso` are composites of equality transports, whiskered
reservoir word comparisons and functor images of these. Hence each is
an `eqToHom`, and the change of chart between them in the original
whole-Hom category is an `eqToHom` as well. The literal dot map is retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM BicategoryStruct
namespace OddMath.QuiverHecke.SwappedAssembly

theorem exists_eqToHom_self {C : Type*} [Category C] {A B : C} (h : A = B) :
    ∃ h' : A = B, eqToHom h = eqToHom h' := ⟨h, rfl⟩

theorem exists_eqToHom_map {C C' : Type*} [Category C] [Category C'] (F : C ⥤ C')
    {A B : C} (f : A ⟶ B) (hf : ∃ h, f = eqToHom h) : ∃ h, F.map f = eqToHom h := by
  obtain ⟨h, rfl⟩ := hf
  exact ⟨congrArg F.obj h, eqToHom_map F h⟩

theorem exists_eqToHom_inv {C : Type*} [Category C] {A B : C} (e : A ≅ B)
    (he : ∃ h, e.hom = eqToHom h) : ∃ h, e.inv = eqToHom h := by
  obtain ⟨h, he⟩ := he
  refine ⟨h.symm, ?_⟩
  rw [← cancel_mono e.hom, Iso.inv_hom_id, he, eqToHom_trans, eqToHom_refl]

/-- In the strict 2-supercategory `Π-𝔖ℭ𝔞𝔱` the associator is an equality transport. -/
theorem exists_eqToHom_associator.{w} {k : Type w} [CommRing k]
    {a b c d : PiSCat.{w,w,w + 1} k}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) : ∃ e, (associator f g h).hom = eqToHom e :=
  ⟨_, by rw [BicategoryStruct.Strict.associator_eqToIso]; rfl⟩

section Shift
universe r v' u'
variable {k : Type r} [CommRing k] {C : Type u'} [Category.{v'} C]
  [Preadditive C] [Linear k C] [Supercategory k C] [PiSupercategory k C]
  {C' : Type u'} [Category.{v'} C'] [Preadditive C'] [Linear k C']
  [Supercategory k C'] [PiSupercategory k C']

/-- At the zero content shift the beta/xi conjugation comparison is an
equality transport. -/
theorem exists_eqToHom_homShiftConjugationIso (F : C ⥤ C') [F.Additive] [F.Linear k]
    [IsSuperfunctor k F] (p : ZMod 2) (hp : p = 0) (Z : C) :
    ∃ h, (homShiftConjugationIso (k := k) F p Z).hom = eqToHom h := by
  subst hp
  refine ⟨by simp only [homParityShift_zero, Functor.id_obj], ?_⟩
  rw [homShiftConjugationIso_hom]
  change F.map (𝟙 Z) ≫ 𝟙 (F.obj Z) = _
  rw [F.map_id, Category.comp_id]
  rfl

end Shift

theorem homContentShift_zero {I X : Type*} [AddCommGroup X] (D : Datum I X) (i : I) :
    homContentShift D i 0 = 0 := by
  simp only [homContentShift, map_zero, mul_zero]

namespace SupportedSectors.TensorEntryPullback

/-- For an equivalence given by an equality of indices, a change between
two charts that are both equality transports is an equality transport. -/
theorem chartChange_eqToHom {J : Type*} (C : J → Type*) [∀ j, Category (C j)]
    {x y : J} (h : x = y) {X : C y} {A A' : C x}
    (e : X ≅ (Pi.eqToEquivalence C h).functor.obj A)
    (d : X ≅ (Pi.eqToEquivalence C h).functor.obj A')
    (he : ∃ h, e.hom = eqToHom h) (hd : ∃ h, d.hom = eqToHom h) :
    ∃ h', (chartChange (Pi.eqToEquivalence C h) e d).hom = eqToHom h' := by
  subst h
  obtain ⟨h₁, he'⟩ := exists_eqToHom_inv e he
  obtain ⟨h₂, hd'⟩ := hd
  refine ⟨h₁.trans h₂, ?_⟩
  apply (Pi.eqToEquivalence C (rfl : x = x)).functor.map_injective
  simp only [chartChange, Functor.preimageIso_hom, Functor.map_preimage, Iso.trans_hom,
    Iso.symm_hom, he', hd', eqToHom_trans, eqToHom_map]

end SupportedSectors.TensorEntryPullback

namespace SupportedSectors
open CyclotomicAction ELVOld
universe u
local instance tensorLayerChartTransportHomPi {k : Type u} [CommRing k]
    (A C : PiSCat.{u,u,u + 1} k) : PiSupercategory k (A ⟶ C) :=
  PiTwoSupercategory.homPiLeft A C
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (ΛP ΛR : X) (L : I × ℕ → ℕ)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR) (s : List I)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "cS" => tensorSourceContent D ΛP ΛR s
local notation "P" => elvProbeReservoir D Sc m cutoff N ΛP ΛR hP hR

/-- The prescribed global path chart is an equality transport. -/
theorem tensorRowTargetIso_hom_eqToHom {a : Obj (SKM.sig D)}
    (p : SPath a.word (0,cS) (0,0)) (hup : ∀ c ∈ a.word, c.l.1 = true) :
    ∃ h, (tensorRowTargetIso D Sc m cutoff ΛP ΛR L hP hR s p hup).hom = eqToHom h := by
  unfold tensorRowTargetIso tensorVacuumPathIso
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv, Iso.app_hom]
  repeat' first
    | exact exists_eqToHom_self _
    | apply exists_eqToHom_comp
    | apply ProbeReservoir.reservoirWordFunctorIso_hom_app_eqToHom

section Context
variable {l r : List (Col I X)} {cL cM cR : I →₀ ℕ}
  (pL : SPath l (0,cL) (0,cM)) (hl : ∀ a ∈ l, a.l.1 = true)
  (pR : SPath r (0,cR) (0,0)) (hr : ∀ a ∈ r, a.l.1 = true)

/-- The two-context chart of a middle factor is an equality transport. -/
theorem tensorContextIso_hom_eqToHom
    (A : (P).W.obj ((P).muM (0,cR)) ⟶ (P).W.obj ((P).muM (0,cM))) :
    ∃ h, (tensorContextIso D Sc m cutoff L ΛP ΛR hP hR pL hl pR hr A).hom = eqToHom h := by
  unfold tensorContextIso ProbeReservoir.reservoirContextIso
  simp only [Iso.trans_hom, eqToIso.hom, Functor.mapIso_hom,
    TwoSupercategory.whiskerRightIso_hom, Iso.app_hom]
  repeat' first
    | exact exists_eqToHom_self _
    | apply exists_eqToHom_comp
    | apply exists_eqToHom_map
    | apply exists_eqToHom_whiskerRight
    | apply ProbeReservoir.reservoirWordFunctorIso_hom_app_eqToHom

end Context

section Dot
variable (ν : X) (u v : List (Letter I)) (i : I)
  {cL c : I →₀ ℕ} (hv : StepValid (true,i) false (0,c))
  (pL : SPath (SKM.lay D ν u (.dot i) v).left (0,cL) (0,c))
  (hl : ∀ a ∈ (SKM.lay D ν u (.dot i) v).left, a.l.1 = true)
  (pR : SPath (SKM.lay D ν u (.dot i) v).right (0,c - Finsupp.single i 1) (0,0))
  (hr : ∀ a ∈ (SKM.lay D ν u (.dot i) v).right, a.l.1 = true)

/-- The prescribed local dot chart is an equality transport. -/
theorem tensorLayerDotIso_hom_eqToHom :
    ∃ h, (tensorLayerDotIso D Sc m cutoff L ΛP ΛR hP hR ν u v i hv pL hl pR hr).hom =
      eqToHom h := by
  unfold tensorLayerDotIso ProbeReservoir.reservoirLayerDotIso tensorContextIso
    ProbeReservoir.reservoirContextIso reservoirVacuumPostIso
  simp only [Iso.trans_hom, eqToIso.hom, Functor.mapIso_hom,
    TwoSupercategory.whiskerRightIso_hom, Iso.app_hom]
  repeat' first
    | exact exists_eqToHom_self _
    | apply exists_eqToHom_comp
    | apply exists_eqToHom_map
    | apply exists_eqToHom_whiskerRight
    | apply ProbeReservoir.reservoirWordFunctorIso_hom_app_eqToHom

/-- Any equality-transport chart and the local dot chart differ by an
equality transport in the original whole-Hom category. -/
theorem tensorLayerDot_chartChange_eqToHom
    {G : probeOldWeightSpace D (parameterTwist D Sc) m ΛP (-ΛP) ⟶
      elvWeightSpace D (parameterTwist D Sc) cutoff N ΛR (ReservoirWord.weight D ΛR cL)}
    (g : ((P).pathFunctor (SPath.append (SPath.append pL
        (SPath.cons (Col.mk (up i) (SKM.wt D ν v)) false (0,c) hv (SPath.nil _))) pR)).obj
          (ObjectProperty.FullSubcategory.obj (tensorVacuum D Sc m cutoff L ΛP ΛR)) ≅
      (tensorHomEquivalence D Sc m cutoff L ΛP ΛR (ReservoirWord.weight D ΛR cL)).functor.obj G)
    (hg : ∃ h, g.hom = eqToHom h) :
    ∃ h, (TensorEntryPullback.chartChange
      (tensorHomEquivalence D Sc m cutoff L ΛP ΛR (ReservoirWord.weight D ΛR cL)) g
      (tensorLayerDotIso D Sc m cutoff L ΛP ΛR hP hR ν u v i hv pL hl pR hr)).hom =
        eqToHom h := by
  unfold tensorHomEquivalence
  exact TensorEntryPullback.chartChange_eqToHom _ _ g _ hg
    (tensorLayerDotIso_hom_eqToHom D Sc m cutoff ΛP ΛR L hP hR ν u v i hv pL hl pR hr)

end Dot

section Same
variable (ν : X) (u v : List (Letter I)) (i : I)
  {cL c : I →₀ ℕ} (hv : StepValid (true,i) false (0,c))
  (hw : StepValid (true,i) false (nextSector (true,i) false (0,c)))
  (pL : SPath (SKM.lay D ν u (.cross i i) v).left (0,cL) (0,c))
  (hl : ∀ a ∈ (SKM.lay D ν u (.cross i i) v).left, a.l.1 = true)
  (pR : SPath (SKM.lay D ν u (.cross i i) v).right
    (0,c - Finsupp.single i 1 - Finsupp.single i 1) (0,0))
  (hr : ∀ a ∈ (SKM.lay D ν u (.cross i i) v).right, a.l.1 = true)

/-- The prescribed equal-colour crossing chart is an equality transport:
its content shift vanishes on the vacuum sector. -/
theorem tensorLayerSameCrossIso_hom_eqToHom :
    ∃ h, (tensorLayerSameCrossIso D Sc m cutoff L ΛP ΛR hP hR ν u v i hv hw pL hl pR hr).hom =
      eqToHom h := by
  unfold tensorLayerSameCrossIso ProbeReservoir.reservoirLayerSameCrossIso
  simp only [Iso.trans_hom, eqToIso.hom, Functor.mapIso_hom, Iso.app_hom,
    homContentPostWordIso_hom_app]
  repeat' first
    | exact exists_eqToHom_self _
    | exact homContentShift_zero D i
    | apply exists_eqToHom_comp
    | apply exists_eqToHom_map
    | apply exists_eqToHom_associator
    | apply exists_eqToHom_homShiftConjugationIso
    | apply tensorContextIso_hom_eqToHom

end Same

open private tensorCrossContextIso in
/-- The distinct-colour context chart, with its right-path reindexing, is an
equality transport. -/
theorem tensorCrossContextIso_hom_eqToHom {l r : List (Col I X)} {cL cM cR cR' : I →₀ ℕ}
    (h : ((0,cR) : Sector I) = (0,cR'))
    (pL : SPath l (0,cL) (0,cM)) (hl : ∀ a ∈ l, a.l.1 = true)
    (pR : SPath r (0,cR') (0,0)) (hr : ∀ a ∈ r, a.l.1 = true)
    (A : (P).W.obj ((P).muM (0,cR)) ⟶ (P).W.obj ((P).muM (0,cM))) :
    ∃ e, (tensorCrossContextIso D Sc m cutoff L ΛP ΛR hP hR h pL hl pR hr A).hom =
      eqToHom e := by
  cases h
  exact tensorContextIso_hom_eqToHom D Sc m cutoff ΛP ΛR L hP hR pL hl pR hr A

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

/-- The distinct-colour source chart is an equality transport. -/
theorem tensorLayerCrossSourceIso_hom_eqToHom :
    ∃ h, (tensorLayerCrossSourceIso D Sc m cutoff L ΛP ΛR hP hR ν u v i j
      hv₁ hv₂ hs pL hl pR hr).hom = eqToHom h := by
  unfold tensorLayerCrossSourceIso ProbeReservoir.reservoirLayerCrossSourceIso
    ProbeReservoir.reservoirCrossSourceIso reservoirVacuumPairIso
  simp only [Iso.trans_hom, eqToIso.hom, Functor.mapIso_hom]
  repeat' first
    | exact exists_eqToHom_self _
    | apply exists_eqToHom_comp
    | apply exists_eqToHom_map
    | apply exists_eqToHom_associator
    | apply tensorCrossContextIso_hom_eqToHom

/-- The distinct-colour target chart is an equality transport. -/
theorem tensorLayerCrossTargetIso_hom_eqToHom :
    ∃ h, (tensorLayerCrossTargetIso D Sc m cutoff L ΛP ΛR hP hR ν u v i j
      hw₁ hw₂ hs pL hl pR hr).hom = eqToHom h := by
  unfold tensorLayerCrossTargetIso ProbeReservoir.reservoirLayerCrossTargetIso
    ProbeReservoir.reservoirVacuumCrossTargetIso reservoirVacuumPairIso
  simp only [Iso.trans_hom, eqToIso.hom, eqToIso.inv, Iso.symm_hom, Functor.mapIso_hom,
    Functor.mapIso_inv]
  repeat' first
    | exact exists_eqToHom_self _
    | apply exists_eqToHom_comp
    | apply exists_eqToHom_map
    | apply exists_eqToHom_associator
    | apply tensorCrossContextIso_hom_eqToHom

end Distinct
end SupportedSectors
end OddMath.QuiverHecke.SwappedAssembly
