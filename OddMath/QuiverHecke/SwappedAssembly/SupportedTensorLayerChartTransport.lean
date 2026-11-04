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
end SupportedSectors
end OddMath.QuiverHecke.SwappedAssembly
