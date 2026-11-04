import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorEntryPullback

/-! # Even charts on the original-weight tensor source row

SwappedVacuumCoordinates §§2–5: the prescribed global path chart and
its canonical original-input source chart are even whole-Hom maps.
Thus the source-unit observation can retain every odd coefficient and
generator sign when these charts are attached to the original-weight
row entry.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
private theorem even_iso_trans {k : Type*} [CommRing k]
    {C : Type*} [Category* C] [Preadditive C] [Linear k C] [Supercategory k C]
    {A B C₀ : C} (e : A ≅ B) (f : B ≅ C₀)
    (he : e.hom ∈ parity (R := k) _ _ 0) (hf : f.hom ∈ parity (R := k) _ _ 0) :
    (e ≪≫ f).hom ∈ parity (R := k) _ _ 0 := by
  simpa only [Iso.trans_hom, zero_add] using comp_mem he hf

private theorem inverseInput_chart_even {k J : Type*} [CommRing k]
    (C : J → Type*) [∀ x, Category (C x)] [∀ x, Preadditive (C x)]
    [∀ x, Linear k (C x)] [∀ x, Supercategory k (C x)] {x y : J} (h : x = y)
    (F : C x) (G : C y) (e : G ≅ (Pi.eqToEquivalence C h).functor.obj F)
    (he : e.hom ∈ parity (R := k) _ _ 0) :
    ((Pi.eqToEquivalence C h).inverse.mapIso e ≪≫
      ((Pi.eqToEquivalence C h).unitIso.app F).symm).hom ∈ parity (R := k) _ _ 0 := by
  subst y
  dsimp only [Pi.eqToEquivalence, Equivalence.refl, Functor.id_obj] at e he ⊢
  change e.hom ∈ parity (R := k) G F 0 at he
  change e.hom ≫ 𝟙 F ∈ parity (R := k) G F 0
  exact comp_mem he (id_mem F)

universe u
local instance tensorEntryParityHomPi {k : Type u} [CommRing k] (A C : PiSCat.{u,u,u + 1} k) :
    PiSupercategory k (A ⟶ C) := PiTwoSupercategory.homPiLeft A C
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (ΛP ΛR : X) (L : I × ℕ → ℕ)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "Tw" => parameterTwist D Sc

variable (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR) (s : List I)
local notation "cS" => tensorSourceContent D ΛP ΛR s
local notation "P" => elvProbeReservoir D Sc m cutoff N ΛP ΛR hP hR
local notation "E" => tensorHomEquivalence D Sc m cutoff L ΛP ΛR (ReservoirWord.weight D ΛR cS)

/-- The fixed source sector has the original labelled source region at external weight ΛP − ΛR. -/
theorem tensorSourceWeight : (P).wt (0,cS) = (SKM.ob D (ΛP - ΛR) (upWord s)).start := by
  change (P).wt (0,cS) = SKM.wt D (ΛP - ΛR) (upWord s)
  apply (P).wt_eq_of_ok (tensorSourcePath D ΛP ΛR s) _ (SKM.ok_wd D (ΛP - ΛR) (upWord s))
  change (P).wt (0,0) = (SKM.sig D).endR _ (wd D (ΛP - ΛR) (upWord s))
  rw [SKM.endR_wd]
  exact tensorVacuumWeight D Sc m cutoff ΛP ΛR L hP hR

/-- The prescribed global target chart retains degree zero on the entire source Hom. -/
theorem tensorRowTargetIso_hom_mem {a : Obj (SKM.sig D)}
    (p : SPath a.word (0,cS) (0,0)) (hup : ∀ c ∈ a.word, c.l.1 = true) :
    (tensorRowTargetIso D Sc m cutoff ΛP ΛR L hP hR s (a := a) p hup).hom ∈ parity (R := k) _ _ 0 := by
  unfold tensorRowTargetIso
  apply even_iso_trans
  · exact eqToHom_mem (R := k) (factor_path_obj D Sc m cutoff N ΛP ΛR hP hR p
      (tensorVacuum D Sc m cutoff L ΛP ΛR)).symm
  · apply even_iso_trans
    · exact tensorVacuumPathIso_hom_mem D Sc m cutoff L ΛP ΛR hP hR p hup
    · exact eqToHom_mem (R := k) (tensorHomEquivalence_obj D Sc m cutoff L ΛP ΛR
        (TensorReservoirWords.pathHom D Tw m cutoff L ΛP ΛR p hup)).symm

/-- The original-input source chart is even, including on independent odd coefficient products. -/
theorem tensorOriginalRowSourceIso_hom_mem :
    (tensorOriginalRowSourceIso D Sc m cutoff ΛP ΛR L hP hR s).hom ∈ parity (R := k) _ _ 0 := by
  let p := tensorSourcePath D ΛP ΛR s
  let up := tensorSourceLabels_up D ΛP ΛR s
  have h₁ := eqToHom_mem (R := k) (congrArg
    (fun Z : H D Tw m cutoff N ΛP ΛR (0,cS) => Z.obj)
      (tensorSourceFamily_source D Sc m cutoff ΛP ΛR L s))
  have h₂ := eqToHom_mem (R := k) (factor_path_obj D Sc m cutoff N ΛP ΛR hP hR p
    (tensorVacuum D Sc m cutoff L ΛP ΛR))
  have h₃ := tensorRowTargetIso_hom_mem D Sc m cutoff ΛP ΛR L hP hR s
    (a := SKM.ob D (ΛP - ΛR) (upWord s)) p up
  exact inverseInput_chart_even (k := k) (fun x => probeOldWeightSpace D Tw m ΛP x ⟶
      elvWeightSpace D Tw cutoff N ΛR (ReservoirWord.weight D ΛR cS))
    (probeWeight_vacuum D ΛP).symm
    (TensorReservoirWords.pathHom D Tw m cutoff L ΛP ΛR p up)
    (tensorSourceFamily D Sc m cutoff ΛP ΛR L s (0,cS)).obj
    (eqToIso (congrArg (fun Z : H D Tw m cutoff N ΛP ΛR (0,cS) => Z.obj)
      (tensorSourceFamily_source D Sc m cutoff ΛP ΛR L s)) ≪≫
      eqToIso (factor_path_obj D Sc m cutoff N ΛP ΛR hP hR p
        (tensorVacuum D Sc m cutoff L ΛP ΛR)) ≪≫
      tensorRowTargetIso D Sc m cutoff ΛP ΛR L hP hR s
        (a := SKM.ob D (ΛP - ΛR) (upWord s)) p up) (even_iso_trans _ _ h₁ (even_iso_trans _ _ h₂ h₃))

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
