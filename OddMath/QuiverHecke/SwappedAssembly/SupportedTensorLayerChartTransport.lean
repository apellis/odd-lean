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

theorem exists_eqToHom_eqToIso {C : Type*} [Category C] {A B : C} (h : A = B) :
    ∃ h', (eqToIso h).hom = eqToHom h' := ⟨h, rfl⟩

/-- In the strict 2-supercategory `Π-𝔖ℭ𝔞𝔱` the associator is an equality transport. -/
theorem exists_eqToHom_associator.{w} {k : Type w} [CommRing k]
    {a b c d : PiSCat.{w,w,w + 1} k}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) : ∃ e, (associator f g h).hom = eqToHom e := by
  rw [BicategoryStruct.Strict.associator_eqToIso]
  exact exists_eqToHom_eqToIso _

theorem exists_eqToHom_trans {C : Type*} [Category C] {A B B' : C} (e : A ≅ B) (e' : B ≅ B')
    (he : ∃ h, e.hom = eqToHom h) (he' : ∃ h, e'.hom = eqToHom h) :
    ∃ h, (e ≪≫ e').hom = eqToHom h :=
  exists_eqToHom_comp e.hom e'.hom he he'

theorem exists_eqToHom_symm {C : Type*} [Category C] {A B : C} (e : A ≅ B)
    (he : ∃ h, e.hom = eqToHom h) : ∃ h, e.symm.hom = eqToHom h :=
  exists_eqToHom_inv e he

theorem exists_eqToHom_mapIso {C C' : Type*} [Category C] [Category C'] (F : C ⥤ C')
    {A B : C} (e : A ≅ B) (he : ∃ h, e.hom = eqToHom h) :
    ∃ h, (F.mapIso e).hom = eqToHom h :=
  exists_eqToHom_map F e.hom he

theorem exists_eqToHom_app {C C' : Type*} [Category C] [Category C'] {F G : C ⥤ C'}
    (α : F ≅ G) (Z : C) (h : ∃ h, α.hom.app Z = eqToHom h) :
    ∃ h, (α.app Z).hom = eqToHom h := h

theorem exists_eqToHom_whiskerRightIso.{w} {k : Type w} [CommRing k]
    {A B C : PiSCat.{w,w,w + 1} k} {F G : A ⟶ B}
    (e : F ≅ G) (E : B ⟶ C) (he : ∃ h, e.hom = eqToHom h) :
    ∃ h, (TwoSupercategory.whiskerRightIso (R := k) e E).hom = eqToHom h := by
  rw [TwoSupercategory.whiskerRightIso_hom (R := k)]
  exact exists_eqToHom_whiskerRight e.hom E he

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

/-- An equivalence whose functor pulls equality transports back to
equality transports: Pi reindexing along an equality of indices. -/
theorem preimage_eqToHom_of_pi {J : Type*} (C : J → Type*) [∀ j, Category (C j)]
    {x y : J} (h : x = y) {A B : C x}
    (h' : (Pi.eqToEquivalence C h).functor.obj A = (Pi.eqToEquivalence C h).functor.obj B) :
    ∃ h'' : A = B, (Pi.eqToEquivalence C h).functor.preimage (eqToHom h') = eqToHom h'' := by
  subst h
  refine ⟨h', ?_⟩
  apply (Pi.eqToEquivalence C (rfl : x = x)).functor.map_injective
  rw [Functor.map_preimage, eqToHom_map]

section General
variable {C₁ : Type*} [Category C₁] {C₂ : Type*} [Category C₂] (E : C₁ ≌ C₂)
  (hE : ∀ {A B : C₁} (h : E.functor.obj A = E.functor.obj B),
    ∃ h' : A = B, E.functor.preimage (eqToHom h) = eqToHom h')
include hE

/-- A chart change between equality-transport charts is an equality transport. -/
theorem chartChange_eqToHom_of {X : C₂} {A A' : C₁}
    (e : X ≅ E.functor.obj A) (d : X ≅ E.functor.obj A')
    (he : ∃ h, e.hom = eqToHom h) (hd : ∃ h, d.hom = eqToHom h) :
    ∃ h', (chartChange E e d).hom = eqToHom h' := by
  obtain ⟨h₁, he'⟩ := exists_eqToHom_inv e he
  obtain ⟨h₂, hd'⟩ := hd
  have hc : (chartChange E e d).hom = E.functor.preimage (eqToHom (h₁.trans h₂)) := by
    simp only [chartChange, Functor.preimageIso_hom, Iso.trans_hom, Iso.symm_hom, he', hd',
      eqToHom_trans]
  rw [hc]
  exact hE _

/-- Pulled-back arrows in two pairs of equality-transport charts are
conjugate by equality transports. -/
theorem arrow_eqToHom_conj_of {X Y : C₂} {A B A' B' : C₁}
    (e : X ≅ E.functor.obj A) (d : Y ≅ E.functor.obj B)
    (e' : X ≅ E.functor.obj A') (d' : Y ≅ E.functor.obj B')
    (he : ∃ h, e.hom = eqToHom h) (hd : ∃ h, d.hom = eqToHom h)
    (he' : ∃ h, e'.hom = eqToHom h) (hd' : ∃ h, d'.hom = eqToHom h) (m : X ⟶ Y) :
    ∃ (hA : A = A') (hB : B = B'),
      arrow E e d m = eqToHom hA ≫ arrow E e' d' m ≫ eqToHom hB.symm := by
  obtain ⟨hA, hcA⟩ := chartChange_eqToHom_of E hE e e' he he'
  obtain ⟨hB, hcB⟩ := chartChange_eqToHom_of E hE d d' hd hd'
  refine ⟨hA, hB, ?_⟩
  have sq := arrow_chartChange E e d e' d' m
  rw [hcA, hcB] at sq
  rw [← Category.assoc, ← sq, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

end General

end SupportedSectors.TensorEntryPullback

namespace SupportedSectors
open CyclotomicAction ELVOld
universe u
local instance tensorLayerChartTransportHomPi {k : Type u} [CommRing k]
    (A C : PiSCat.{u,u,u + 1} k) : PiSupercategory k (A ⟶ C) :=
  PiTwoSupercategory.homPiLeft A C

section PostWord
variable {k : Type u} [CommRing k] {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : X → PiSCat.{u,u,u + 1} k) (W : RouquierFamily (k := k) (B := PiSCat.{u,u,u + 1} k) D)
  (i : I) (muP : X) {muM nuM rhoM : X} (h : muM + D.α i = nuM) (h₂ : nuM + D.α i = rhoM)

/-- At zero content the BB word comparison is an equality transport:
the beta/xi conjugation is trivial and the associator is strict. -/
theorem homContentPostWordIso_zero_app_eqToHom (Z : homWeightSector T W.obj muP muM) :
    ∃ e, ((homContentPostWordIso T W i 0 muP h h₂).app Z).hom = eqToHom e := by
  rw [Iso.app_hom, homContentPostWordIso_hom_app]
  exact exists_eqToHom_comp _ _
    (exists_eqToHom_homShiftConjugationIso _ _ (homContentShift_zero D i) _)
    (exists_eqToHom_associator _ _ _)

end PostWord
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

/-- The vacuum input-weight equivalence pulls equality transports back to
equality transports. -/
theorem tensorHomEquivalence_preimage_eqToHom (z : X)
    {A B : probeOldWeightSpace D (parameterTwist D Sc) m ΛP (-ΛP) ⟶
      elvWeightSpace D (parameterTwist D Sc) cutoff N ΛR z}
    (h : (tensorHomEquivalence D Sc m cutoff L ΛP ΛR z).functor.obj A =
      (tensorHomEquivalence D Sc m cutoff L ΛP ΛR z).functor.obj B) :
    ∃ h' : A = B,
      (tensorHomEquivalence D Sc m cutoff L ΛP ΛR z).functor.preimage (eqToHom h) =
        eqToHom h' :=
  TensorEntryPullback.preimage_eqToHom_of_pi _ _ h

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

/-- **Dot layer coherence.** In every global chart that is an equality
transport, the pulled-back literal dot layer of the full chosen action is the
frozen local dot operator, up to equality transport of its endpoints. -/
theorem tensorOriginalWordLayer_dot_transport
    {G : probeOldWeightSpace D (parameterTwist D Sc) m ΛP (-ΛP) ⟶
      elvWeightSpace D (parameterTwist D Sc) cutoff N ΛR (ReservoirWord.weight D ΛR cL)}
    (g : ((P).pathFunctor (SPath.append (SPath.append pL
        (SPath.cons (Col.mk (up i) (SKM.wt D ν v)) false (0,c) hv (SPath.nil _))) pR)).obj
          (ObjectProperty.FullSubcategory.obj (tensorVacuum D Sc m cutoff L ΛP ΛR)) ≅
      (tensorHomEquivalence D Sc m cutoff L ΛP ΛR (ReservoirWord.weight D ΛR cL)).functor.obj G)
    (hg : ∃ h, g.hom = eqToHom h) (a : (P).CrossCoeff) (leftward : (P).LeftwardData) :
    ∃ (h₁ : G = ReservoirLayerCells.dotRawHom D Sc m cutoff L ΛP ΛR pL hl pR hr i
          (ProbeReservoir.reservoirVacuumEdge (P) i c hv))
      (h₂ : G = ReservoirLayerCells.dotRawHom D Sc m cutoff L ΛP ΛR pL hl pR hr i
          (ProbeReservoir.reservoirVacuumEdge (P) i c hv)),
      TensorEntryPullback.arrow
          (tensorHomEquivalence D Sc m cutoff L ΛP ΛR (ReservoirWord.weight D ΛR cL)) g g
          ((P).compLayer ((P).swappedGens a leftward) (SKM.lay D ν u (.dot i) v)
            (SPath.append (SPath.append pL
              (SPath.cons (Col.mk (up i) (SKM.wt D ν v)) false (0,c) hv (SPath.nil _))) pR)
            (SPath.append (SPath.append pL
              (SPath.cons (Col.mk (up i) (SKM.wt D ν v)) false (0,c) hv (SPath.nil _))) pR)
            (ObjectProperty.FullSubcategory.obj (tensorVacuum D Sc m cutoff L ΛP ΛR))) =
        eqToHom h₁ ≫ tensorLayerDotRaw D Sc m cutoff L ΛP ΛR hP hR ν u v i hv pL hl pR hr a ≫
          eqToHom h₂.symm := by
  rw [tensorLayerDotRaw_arrow (leftward := leftward)]
  have he := tensorLayerDotIso_hom_eqToHom D Sc m cutoff ΛP ΛR L hP hR ν u v i hv pL hl pR hr
  exact TensorEntryPullback.arrow_eqToHom_conj_of _
    (tensorHomEquivalence_preimage_eqToHom D Sc m cutoff ΛP ΛR L _) g g _ _ hg hg he he _

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
  simp only [Iso.trans_hom, eqToIso.hom, Functor.mapIso_hom]
  repeat' first
    | with_reducible exact exists_eqToHom_self _
    | (rw [(homContentPostWordIso_zero_app_eqToHom _ _ _ _ _ _ _).choose_spec]; exact ⟨_, rfl⟩)
    | with_reducible_and_instances apply exists_eqToHom_trans
    | with_reducible_and_instances apply exists_eqToHom_eqToIso
    | with_reducible_and_instances apply exists_eqToHom_symm
    | with_reducible_and_instances apply exists_eqToHom_mapIso
    | with_reducible_and_instances apply exists_eqToHom_whiskerRightIso
    | with_reducible_and_instances apply exists_eqToHom_app
    | with_reducible_and_instances apply exists_eqToHom_comp
    | with_reducible_and_instances apply exists_eqToHom_map
    | with_reducible_and_instances apply exists_eqToHom_whiskerRight
  repeat' first
    | exact homContentShift_zero D i
    | apply tensorContextIso_hom_eqToHom

/-- **Equal-colour crossing coherence.** In every global chart that is an
equality transport, the pulled-back literal equal-colour crossing layer of the
full chosen action is the frozen local crossing operator, up to equality
transport of its endpoints. -/
theorem tensorOriginalWordLayer_sameCross_transport
    {G : probeOldWeightSpace D (parameterTwist D Sc) m ΛP (-ΛP) ⟶
      elvWeightSpace D (parameterTwist D Sc) cutoff N ΛR (ReservoirWord.weight D ΛR cL)}
    (g : ((P).pathFunctor (SPath.append (SPath.append pL
        (SPath.cons (Col.mk (up i) (SKM.wt D (SKM.wt D ν v) [up i])) false (0,c) hv
          (SPath.cons (Col.mk (up i) (SKM.wt D ν v)) false _ hw (SPath.nil _)))) pR)).obj
          (ObjectProperty.FullSubcategory.obj (tensorVacuum D Sc m cutoff L ΛP ΛR)) ≅
      (tensorHomEquivalence D Sc m cutoff L ΛP ΛR (ReservoirWord.weight D ΛR cL)).functor.obj G)
    (hg : ∃ h, g.hom = eqToHom h) (a : (P).CrossCoeff) (leftward : (P).LeftwardData) :
    ∃ h₁ h₂,
      TensorEntryPullback.arrow
          (tensorHomEquivalence D Sc m cutoff L ΛP ΛR (ReservoirWord.weight D ΛR cL)) g g
          ((P).compLayer ((P).swappedGens a leftward) (SKM.lay D ν u (.cross i i) v)
            (SPath.append (SPath.append pL
              (SPath.cons (Col.mk (up i) (SKM.wt D (SKM.wt D ν v) [up i])) false (0,c) hv
                (SPath.cons (Col.mk (up i) (SKM.wt D ν v)) false _ hw (SPath.nil _)))) pR)
            (SPath.append (SPath.append pL
              (SPath.cons (Col.mk (up i) (SKM.wt D (SKM.wt D ν v) [up i])) false (0,c) hv
                (SPath.cons (Col.mk (up i) (SKM.wt D ν v)) false _ hw (SPath.nil _)))) pR)
            (ObjectProperty.FullSubcategory.obj (tensorVacuum D Sc m cutoff L ΛP ΛR))) =
        eqToHom h₁ ≫ tensorLayerSameCrossRaw D Sc m cutoff L ΛP ΛR hP hR ν u v i hv hw
          pL hl pR hr a ≫ eqToHom (Eq.symm h₂) := by
  rw [tensorLayerSameCrossRaw_arrow (leftward := leftward)]
  have he := tensorLayerSameCrossIso_hom_eqToHom D Sc m cutoff ΛP ΛR L hP hR ν u v i
    hv hw pL hl pR hr
  exact TensorEntryPullback.arrow_eqToHom_conj_of _
    (tensorHomEquivalence_preimage_eqToHom D Sc m cutoff ΛP ΛR L _) g g _ _ hg hg he he _

end Same

open private OddMath.QuiverHecke.SwappedAssembly.SupportedSectors.tensorCrossContextIso
  from OddMath.QuiverHecke.SwappedAssembly.SupportedTensorCrossEntries

/-- The distinct-colour context chart, with its right-path reindexing, is an
equality transport. -/
theorem tensorCrossContextIso_hom_eqToHom {l r : List (Col I X)} {cL cM cR cR' : I →₀ ℕ}
    (h : ((0,cR) : Sector I) = (0,cR'))
    (pL : SPath l (0,cL) (0,cM)) (hl : ∀ a ∈ l, a.l.1 = true)
    (pR : SPath r (0,cR') (0,0)) (hr : ∀ a ∈ r, a.l.1 = true)
    (A : (P).W.obj ((P).muM (0,cR)) ⟶ (P).W.obj ((P).muM (0,cM))) :
    ∃ e, (OddMath.QuiverHecke.SwappedAssembly.SupportedSectors.tensorCrossContextIso D Sc m cutoff L ΛP ΛR hP hR h pL hl pR hr A).hom =
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
  unfold tensorLayerCrossSourceIso
  unfold ProbeReservoir.reservoirLayerCrossSourceIso
  unfold ProbeReservoir.reservoirCrossSourceIso
  unfold reservoirVacuumPairIso
  repeat' first
    | with_reducible exact exists_eqToHom_self _
    | with_reducible_and_instances apply exists_eqToHom_trans
    | with_reducible_and_instances apply exists_eqToHom_eqToIso
    | with_reducible_and_instances apply exists_eqToHom_symm
    | with_reducible_and_instances apply exists_eqToHom_mapIso
    | with_reducible_and_instances apply exists_eqToHom_whiskerRightIso
    | with_reducible_and_instances apply exists_eqToHom_app
    | with_reducible_and_instances apply exists_eqToHom_comp
    | with_reducible_and_instances apply exists_eqToHom_map
    | with_reducible_and_instances apply exists_eqToHom_whiskerRight
  repeat' first
    | apply tensorCrossContextIso_hom_eqToHom
    | apply exists_eqToHom_associator

/-- The distinct-colour target chart is an equality transport. -/
theorem tensorLayerCrossTargetIso_hom_eqToHom :
    ∃ h, (tensorLayerCrossTargetIso D Sc m cutoff L ΛP ΛR hP hR ν u v i j
      hw₁ hw₂ hs pL hl pR hr).hom = eqToHom h := by
  unfold tensorLayerCrossTargetIso
  unfold ProbeReservoir.reservoirLayerCrossTargetIso
  unfold ProbeReservoir.reservoirCrossTargetIso
  unfold ProbeReservoir.reservoirVacuumCrossTargetIso
  unfold reservoirVacuumPairIso
  repeat' first
    | with_reducible exact exists_eqToHom_self _
    | with_reducible_and_instances apply exists_eqToHom_trans
    | with_reducible_and_instances apply exists_eqToHom_eqToIso
    | with_reducible_and_instances apply exists_eqToHom_symm
    | with_reducible_and_instances apply exists_eqToHom_mapIso
    | with_reducible_and_instances apply exists_eqToHom_whiskerRightIso
    | with_reducible_and_instances apply exists_eqToHom_app
    | with_reducible_and_instances apply exists_eqToHom_comp
    | with_reducible_and_instances apply exists_eqToHom_map
    | with_reducible_and_instances apply exists_eqToHom_whiskerRight
  repeat' first
    | apply tensorCrossContextIso_hom_eqToHom
    | apply exists_eqToHom_associator

/-- **Distinct-colour crossing coherence.** In every pair of global charts
that are equality transports, the pulled-back literal distinct-colour crossing
layer of the full chosen action is the frozen local crossing operator between
the two words, up to equality transport of its endpoints. -/
theorem tensorOriginalWordLayer_cross_transport
    {U V : probeOldWeightSpace D (parameterTwist D Sc) m ΛP (-ΛP) ⟶
      elvWeightSpace D (parameterTwist D Sc) cutoff N ΛR (ReservoirWord.weight D ΛR cL)}
    (gS : ((P).pathFunctor (SPath.append (SPath.append pL
        (SPath.two (c₁ := Col.mk (up i) (SKM.wt D (SKM.wt D ν v) [up j]))
          (c₂ := Col.mk (up j) (SKM.wt D ν v)) false false hv₁ hv₂ hs)) pR)).obj
          (ObjectProperty.FullSubcategory.obj (tensorVacuum D Sc m cutoff L ΛP ΛR)) ≅
      (tensorHomEquivalence D Sc m cutoff L ΛP ΛR (ReservoirWord.weight D ΛR cL)).functor.obj U)
    (gT : ((P).pathFunctor (SPath.append (SPath.append pL
        (SPath.two (c₁ := Col.mk (up j) (SKM.wt D (SKM.wt D ν v) [up i]))
          (c₂ := Col.mk (up i) (SKM.wt D ν v)) false false hw₁ hw₂ rfl)) pR)).obj
          (ObjectProperty.FullSubcategory.obj (tensorVacuum D Sc m cutoff L ΛP ΛR)) ≅
      (tensorHomEquivalence D Sc m cutoff L ΛP ΛR (ReservoirWord.weight D ΛR cL)).functor.obj V)
    (hgS : ∃ h, gS.hom = eqToHom h) (hgT : ∃ h, gT.hom = eqToHom h)
    (a : (P).CrossCoeff) (leftward : (P).LeftwardData) :
    ∃ h₁ h₂,
      TensorEntryPullback.arrow
          (tensorHomEquivalence D Sc m cutoff L ΛP ΛR (ReservoirWord.weight D ΛR cL)) gS gT
          ((P).compLayer ((P).swappedGens a leftward) (SKM.lay D ν u (.cross i j) v)
            (SPath.append (SPath.append pL
              (SPath.two (c₁ := Col.mk (up i) (SKM.wt D (SKM.wt D ν v) [up j]))
                (c₂ := Col.mk (up j) (SKM.wt D ν v)) false false hv₁ hv₂ hs)) pR)
            (SPath.append (SPath.append pL
              (SPath.two (c₁ := Col.mk (up j) (SKM.wt D (SKM.wt D ν v) [up i]))
                (c₂ := Col.mk (up i) (SKM.wt D ν v)) false false hw₁ hw₂ rfl)) pR)
            (ObjectProperty.FullSubcategory.obj (tensorVacuum D Sc m cutoff L ΛP ΛR))) =
        eqToHom h₁ ≫ tensorLayerCrossRaw D Sc m cutoff L ΛP ΛR hP hR ν u v i j
          hv₁ hv₂ hw₁ hw₂ hs pL hl pR hr a ≫ eqToHom (Eq.symm h₂) := by
  rw [tensorLayerCrossRaw_arrow (leftward := leftward)]
  exact TensorEntryPullback.arrow_eqToHom_conj_of _
    (tensorHomEquivalence_preimage_eqToHom D Sc m cutoff ΛP ΛR L _) gS gT _ _ hgS hgT
    (tensorLayerCrossSourceIso_hom_eqToHom D Sc m cutoff ΛP ΛR L hP hR ν u v i j
      hv₁ hv₂ hs pL hl pR hr)
    (tensorLayerCrossTargetIso_hom_eqToHom D Sc m cutoff ΛP ΛR L hP hR ν u v i j
      hw₁ hw₂ hs pL hl pR hr) _

end Distinct
end SupportedSectors
end OddMath.QuiverHecke.SwappedAssembly
