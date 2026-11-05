import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorRowLayers
import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorContexts

/-! # Original-weight pullback of the literal tensor source row

SwappedVacuumCoordinates §§3–5: use only the canonical input-weight
transport equivalence to pull an actual matrix-row entry to the original
whole tensor-Hom category. The source remains the inverse image of the
specified source-word functor. Composition is preserved by the derived
selected-Hom generator squares, without choosing quotient coordinates.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
namespace TensorEntryPullback
universe v₁ v₂ u₁ u₂ w
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (E : C ≌ D) {X Y Y' : D} {A B : C}

/-- Pull a whole actual source-row arrow through its specified target chart. -/
def map (e : Y ≅ E.functor.obj A) (f : X ⟶ Y) : E.inverse.obj X ⟶ A :=
  E.inverse.map (f ≫ e.hom) ≫ E.unitInv.app A

/-- The pullback retains every whole source-Hom arrow. -/
theorem map_injective (e : Y ≅ E.functor.obj A) : Function.Injective (map E (X := X) e) := by
  intro f g h
  apply (cancel_mono e.hom).mp
  apply E.inverse.map_injective
  exact (cancel_mono (E.unitInv.app A)).mp h

/-- Chronological postcomposition is preserved by the selected-Hom square. -/
theorem map_square (e : Y ≅ E.functor.obj A) (d : Y' ≅ E.functor.obj B)
    (f : X ⟶ Y) (m : Y ⟶ Y') (b : A ⟶ B)
    (hm : m ≫ d.hom = e.hom ≫ E.functor.map b) :
    map E d (f ≫ m) = map E e f ≫ b := by
  unfold map
  calc
    _ = E.inverse.map ((f ≫ e.hom) ≫ E.functor.map b) ≫ E.unitInv.app B := by
      simp only [Category.assoc]
      rw [hm]
    _ = E.inverse.map (f ≫ e.hom) ≫
        (E.inverse.map (E.functor.map b) ≫ E.unitInv.app B) := by
      rw [Functor.map_comp,Category.assoc]
    _ = E.inverse.map (f ≫ e.hom) ≫ (E.unitInv.app A ≫ b) := by
      simpa only [Category.assoc] using congrArg
        (fun g => E.inverse.map (f ≫ e.hom) ≫ g) (E.unitInv_naturality b)
    _ = _ := (Category.assoc _ _ _).symm

variable {k : Type w} [CommRing k] [Preadditive C] [Linear k C] [Preadditive D] [Linear k D]
  [E.inverse.Additive] [E.inverse.Linear k]

/-- The original-weight pullback is linear on every whole source Hom. -/
def linear (e : Y ≅ E.functor.obj A) : (X ⟶ Y) →ₗ[k] (E.inverse.obj X ⟶ A) where
  toFun := map E e
  map_add' f g := by
    simp only [map,Preadditive.add_comp,Functor.map_add]
  map_smul' r f := by
    simp only [map,Linear.smul_comp,Functor.map_smul,RingHom.id_apply]
end TensorEntryPullback

universe u
local instance tensorEntryPullbackHomPi {k : Type u} [CommRing k] (A C : PiSCat.{u,u,u + 1} k) :
    PiSupercategory k (A ⟶ C) := PiTwoSupercategory.homPiLeft A C
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (ΛP ΛR : X) (L : I × ℕ → ℕ)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "Tw" => parameterTwist D Sc

private theorem inverseInput_additive {x y z : X} (h : x = y) :
    (Pi.eqToEquivalence (fun x => probeOldWeightSpace D Tw m ΛP x ⟶
      elvWeightSpace D Tw cutoff N ΛR z) h).inverse.Additive := by
  subst y
  change (𝟭 _).Additive
  infer_instance

private theorem inverseInput_linear {x y z : X} (h : x = y) :
    (Pi.eqToEquivalence (fun x => probeOldWeightSpace D Tw m ΛP x ⟶
      elvWeightSpace D Tw cutoff N ΛR z) h).inverse.Linear k := by
  subst y
  change (𝟭 _).Linear k
  infer_instance

local instance originalInputInverse_additive (z : X) :
    (tensorHomEquivalence D Sc m cutoff L ΛP ΛR z).inverse.Additive :=
  inverseInput_additive D Sc m cutoff ΛP ΛR L (probeWeight_vacuum D ΛP).symm
local instance originalInputInverse_linear (z : X) :
    (tensorHomEquivalence D Sc m cutoff L ΛP ΛR z).inverse.Linear k :=
  inverseInput_linear D Sc m cutoff ΛP ΛR L (probeWeight_vacuum D ΛP).symm

variable (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR) (s : List I)
local notation "cS" => tensorSourceContent D ΛP ΛR s
local notation "E" => tensorHomEquivalence D Sc m cutoff L ΛP ΛR (ReservoirWord.weight D ΛR cS)
local notation "P" => elvProbeReservoir D Sc m cutoff N ΛP ΛR hP hR

/-- The specified source-word detector in its original input-weight presentation. -/
def tensorOriginalRowSource :=
  (E).inverse.obj (tensorSourceFamily D Sc m cutoff ΛP ΛR L s (0,cS)).obj

/-- Pull the actual supported matrix row through its proved selected tensor-Hom target chart. -/
def tensorOriginalRowEntry {a : Obj (SKM.sig D)}
    (hEnd : (ΛP - contentWeight D (0 : I →₀ ℕ)) + (-ΛR + contentWeight D (0 : I →₀ ℕ)) = a.endR)
    (p : SPath a.word (0,cS) (0,0))
    (A : probeOldWeightSpace D Tw m ΛP (-ΛP) ⟶
      elvWeightSpace D Tw cutoff N ΛR (ReservoirWord.weight D ΛR cS))
    (e : ((P).pathFunctor p).obj (tensorVacuum D Sc m cutoff L ΛP ΛR).obj ≅ (E).functor.obj A) :=
  (TensorEntryPullback.linear (E) e).comp
    (tensorVacuumRowProjection D Sc m cutoff ΛP ΛR L hP hR s hEnd p)

/-- The prescribed global path chart in the selected tensor Hom. -/
def tensorRowTargetIso {a : Obj (SKM.sig D)}
    (p : SPath a.word (0,cS) (0,0)) (hup : ∀ c ∈ a.word, c.l.1 = true) :
    ((P).pathFunctor p).obj (tensorVacuum D Sc m cutoff L ΛP ΛR).obj ≅
      (E).functor.obj (TensorReservoirWords.pathHom D Tw m cutoff L ΛP ΛR p hup) :=
  (eqToIso (factor_path_obj D Sc m cutoff N ΛP ΛR hP hR p
    (tensorVacuum D Sc m cutoff L ΛP ΛR))).symm ≪≫
    tensorVacuumPathIso D Sc m cutoff L ΛP ΛR hP hR p hup ≪≫
      (eqToIso (tensorHomEquivalence_obj D Sc m cutoff L ΛP ΛR
        (TensorReservoirWords.pathHom D Tw m cutoff L ΛP ΛR p hup))).symm

/-- Original-weight observation uses the specified global word chart, without a supplied comparison. -/
def tensorOriginalWordEntry {a : Obj (SKM.sig D)}
    (hEnd : (ΛP - contentWeight D (0 : I →₀ ℕ)) + (-ΛR + contentWeight D (0 : I →₀ ℕ)) = a.endR)
    (p : SPath a.word (0,cS) (0,0)) (hup : ∀ c ∈ a.word, c.l.1 = true) :=
  tensorOriginalRowEntry D Sc m cutoff ΛP ΛR L hP hR s (a := a) hEnd p
    (TensorReservoirWords.pathHom D Tw m cutoff L ΛP ΛR p hup)
    (tensorRowTargetIso D Sc m cutoff ΛP ΛR L hP hR s (a := a) p hup)

include hP hR in
/-- The inverse input-weight transport retains the same actual source-word Hom. -/
def tensorOriginalRowSourceIso :
    tensorOriginalRowSource D Sc m cutoff ΛP ΛR L s ≅
      TensorReservoirWords.pathHom D Tw m cutoff L ΛP ΛR
        (tensorSourcePath D ΛP ΛR s) (tensorSourceLabels_up D ΛP ΛR s) :=
  (E).inverse.mapIso
    (eqToIso (congrArg (fun Z : H D Tw m cutoff N ΛP ΛR (0,cS) => Z.obj)
        (tensorSourceFamily_source D Sc m cutoff ΛP ΛR L s)) ≪≫
      eqToIso (factor_path_obj D Sc m cutoff N ΛP ΛR hP hR (tensorSourcePath D ΛP ΛR s)
        (tensorVacuum D Sc m cutoff L ΛP ΛR)) ≪≫
      tensorRowTargetIso D Sc m cutoff ΛP ΛR L hP hR s
        (a := SKM.ob D (ΛP - ΛR) (upWord s)) (tensorSourcePath D ΛP ΛR s) (tensorSourceLabels_up D ΛP ΛR s)) ≪≫
    ((E).unitIso.app (TensorReservoirWords.pathHom D Tw m cutoff L ΛP ΛR
      (tensorSourcePath D ΛP ΛR s) (tensorSourceLabels_up D ΛP ΛR s))).symm

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
