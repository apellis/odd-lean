import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorVacuum
import OddMath.QuiverHecke.SwappedAssembly.ReservoirContextCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVReservoirLayerCells

/-! # The chosen tensor vacuum in both reservoir path contexts

SwappedVacuumCoordinates §§2–6: specialize the prescribed even reservoir
context charts to the literal supported tensor vacuum. The target is the
chosen tensor-Hom word with the unchanged middle factor morphism and both
actual reservoir paths. The square holds for every factor map, including
odd dots and crossings, without a presentation or central-inverse premise.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM BicategoryStruct
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
local instance tensorContextHomPi {k : Type u} [CommRing k] (A C : PiSCat.{u,u,u + 1} k) :
    PiSupercategory k (A ⟶ C) := PiTwoSupercategory.homPiLeft A C
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (L : I × ℕ → ℕ)
  (ΛP ΛR : X)
local notation "Sc'" => parameterTwist D Sc
local notation "N" => PowerWordContent.powerBound D cutoff L

private theorem inputEquivalence_obj {x y z : X} (h : x = y)
    (F : probeOldWeightSpace D Sc' m ΛP x ⟶ elvWeightSpace D Sc' cutoff N ΛR z) :
    (Pi.eqToEquivalence (fun x => probeOldWeightSpace D Sc' m ΛP x ⟶
      elvWeightSpace D Sc' cutoff N ΛR z) h).functor.obj F = h ▸ F := by subst y; rfl

private theorem inputWord_eq {x y z₀ z₁ z₂ z₃ : X} (h : x = y)
    (F : probeOldWeightSpace D Sc' m ΛP x ⟶ elvWeightSpace D Sc' cutoff N ΛR z₀)
    (R : elvWeightSpace D Sc' cutoff N ΛR z₀ ⟶ elvWeightSpace D Sc' cutoff N ΛR z₁)
    (A : elvWeightSpace D Sc' cutoff N ΛR z₁ ⟶ elvWeightSpace D Sc' cutoff N ΛR z₂)
    (K : elvWeightSpace D Sc' cutoff N ΛR z₂ ⟶ elvWeightSpace D Sc' cutoff N ΛR z₃) :
    ((((h ▸ F : probeOldWeightSpace D Sc' m ΛP y ⟶
      elvWeightSpace D Sc' cutoff N ΛR z₀) ≫ R) ≫ A) ≫ K) =
      (Pi.eqToEquivalence (fun x => probeOldWeightSpace D Sc' m ΛP x ⟶
        elvWeightSpace D Sc' cutoff N ΛR z₃) h).functor.obj (((F ≫ R) ≫ A) ≫ K) := by
  subst y
  rfl

private theorem inputWord_square {x y z₀ z₁ z₂ z₃ : X} (h : x = y)
    (F : probeOldWeightSpace D Sc' m ΛP x ⟶ elvWeightSpace D Sc' cutoff N ΛR z₀)
    (R : elvWeightSpace D Sc' cutoff N ΛR z₀ ⟶ elvWeightSpace D Sc' cutoff N ΛR z₁)
    (K : elvWeightSpace D Sc' cutoff N ΛR z₂ ⟶ elvWeightSpace D Sc' cutoff N ΛR z₃)
    {A B : elvWeightSpace D Sc' cutoff N ΛR z₁ ⟶ elvWeightSpace D Sc' cutoff N ΛR z₂}
    (a : A ⟶ B) :
    ((((h ▸ F : probeOldWeightSpace D Sc' m ΛP y ⟶
      elvWeightSpace D Sc' cutoff N ΛR z₀) ≫ R) ◁ a) ▷ K) ≫
        eqToHom (inputWord_eq D Sc m cutoff L ΛP ΛR h F R B K) =
      eqToHom (inputWord_eq D Sc m cutoff L ΛP ΛR h F R A K) ≫
        (Pi.eqToEquivalence (fun x => probeOldWeightSpace D Sc' m ΛP x ⟶
          elvWeightSpace D Sc' cutoff N ΛR z₃) h).functor.map (((F ≫ R) ◁ a) ▷ K) := by
  subst y
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  rfl

/-- The canonical equivalence implementing just the proved vacuum input-weight change. -/
def tensorHomEquivalence (z : X) :
    (probeOldWeightSpace D Sc' m ΛP (-ΛP) ⟶ elvWeightSpace D Sc' cutoff N ΛR z) ≌
      (probeOldWeightSpace D Sc' m ΛP (probeWeight D ΛP (0,0)) ⟶
        elvWeightSpace D Sc' cutoff N ΛR z) :=
  Pi.eqToEquivalence (fun x => probeOldWeightSpace D Sc' m ΛP x ⟶
    elvWeightSpace D Sc' cutoff N ΛR z) (probeWeight_vacuum D ΛP).symm

/-- The equivalence and the supported vacuum use exactly the same whole-Hom transport. -/
theorem tensorHomEquivalence_obj {z : X}
    (F : probeOldWeightSpace D Sc' m ΛP (-ΛP) ⟶ elvWeightSpace D Sc' cutoff N ΛR z) :
    (tensorHomEquivalence D Sc m cutoff L ΛP ΛR z).functor.obj F =
      tensorHomAt D Sc m cutoff L ΛP ΛR F :=
  inputEquivalence_obj D Sc m cutoff L ΛP ΛR (probeWeight_vacuum D ΛP).symm F

variable (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "P" => elvProbeReservoir D Sc m cutoff N ΛP ΛR hP hR

section Context
variable {l r : List (Col I X)} {cL cM cR : I →₀ ℕ}
  (pL : SPath l (0,cL) (0,cM)) (hl : ∀ a ∈ l, a.l.1 = true)
  (pR : SPath r (0,cR) (0,0)) (hr : ∀ a ∈ r, a.l.1 = true)

/-- The selected tensor Hom in both actual reservoir-word contexts. -/
def tensorContextHom
    (A : (P).W.obj ((P).muM (0,cR)) ⟶ (P).W.obj ((P).muM (0,cM))) :=
  (TensorReservoirWords.pathHom D Sc' m cutoff L ΛP ΛR pR hr ≫ A) ≫
    ReservoirWord.word (P).W.toRouquierData ΛR pL hl

/-- Specialize both prescribed path-context charts to the literal supported tensor vacuum. -/
def tensorContextIso
    (A : (P).W.obj ((P).muM (0,cR)) ⟶ (P).W.obj ((P).muM (0,cM))) :
    ((P).pathFunctor pL).obj (((P).pathFunctor pR).obj
      (tensorVacuum D Sc m cutoff L ΛP ΛR).obj ≫ A) ≅
        (tensorHomEquivalence D Sc m cutoff L ΛP ΛR (ReservoirWord.weight D ΛR cL)).functor.obj
          (tensorContextHom D Sc m cutoff L ΛP ΛR hP hR pL hl pR hr A) :=
  (P).reservoirContextIso pL hl pR hr (tensorVacuum D Sc m cutoff L ΛP ΛR).obj A ≪≫
    eqToIso (inputWord_eq D Sc m cutoff L ΛP ΛR (probeWeight_vacuum D ΛP).symm
      (WeightTensorVacuum.selectedHom D Sc' m cutoff ΛP ΛR L)
      (ReservoirWord.word (P).W.toRouquierData ΛR pR hr) A
      (ReservoirWord.word (P).W.toRouquierData ΛR pL hl))

/-- Every prescribed middle factor map has the literal selected tensor-Hom square.
There is no extra sign or supplied comparison for odd dots and crossings. -/
theorem tensorContext_square
    {A B : (P).W.obj ((P).muM (0,cR)) ⟶ (P).W.obj ((P).muM (0,cM))} (a : A ⟶ B) :
    ((P).pathFunctor pL).map ((((P).pathFunctor pR).obj
      (tensorVacuum D Sc m cutoff L ΛP ΛR).obj) ◁ a) ≫
        (tensorContextIso D Sc m cutoff L ΛP ΛR hP hR pL hl pR hr B).hom =
      (tensorContextIso D Sc m cutoff L ΛP ΛR hP hR pL hl pR hr A).hom ≫
        (tensorHomEquivalence D Sc m cutoff L ΛP ΛR (ReservoirWord.weight D ΛR cL)).functor.map
          ((TensorReservoirWords.pathHom D Sc' m cutoff L ΛP ΛR pR hr ◁ a) ▷
            ReservoirWord.word (P).W.toRouquierData ΛR pL hl) := by
  have he := inputWord_square D Sc m cutoff L ΛP ΛR (probeWeight_vacuum D ΛP).symm
    (WeightTensorVacuum.selectedHom D Sc' m cutoff ΛP ΛR L)
    (ReservoirWord.word (P).W.toRouquierData ΛR pR hr)
    (ReservoirWord.word (P).W.toRouquierData ΛR pL hl) a
  let Y := (tensorVacuum D Sc m cutoff L ΛP ΛR).obj
  let F := (P).pathFunctor pL
  let R := ReservoirWord.word (P).W.toRouquierData ΛR pR hr
  let K := ReservoirWord.word (P).W.toRouquierData ΛR pL hl
  let eA := (P).reservoirContextIso pL hl pR hr Y A
  let eB := (P).reservoirContextIso pL hl pR hr Y B
  let qA := inputWord_eq D Sc m cutoff L ΛP ΛR (probeWeight_vacuum D ΛP).symm
    (WeightTensorVacuum.selectedHom D Sc' m cutoff ΛP ΛR L) R A K
  let qB := inputWord_eq D Sc m cutoff L ΛP ΛR (probeWeight_vacuum D ΛP).symm
    (WeightTensorVacuum.selectedHom D Sc' m cutoff ΛP ΛR L) R B K
  let E := (tensorHomEquivalence D Sc m cutoff L ΛP ΛR (ReservoirWord.weight D ΛR cL)).functor
  let b := (TensorReservoirWords.pathHom D Sc' m cutoff L ΛP ΛR pR hr ◁ a) ▷ K
  change F.map ((((P).pathFunctor pR).obj Y) ◁ a) ≫ (eB.hom ≫ eqToHom qB) =
    (eA.hom ≫ eqToHom qA) ≫ E.map b
  calc
    _ = (F.map ((((P).pathFunctor pR).obj Y) ◁ a) ≫ eB.hom) ≫ eqToHom qB :=
      (Category.assoc _ _ _).symm
    _ = (eA.hom ≫ (((Y ≫ R) ◁ a) ▷ K)) ≫ eqToHom qB :=
      congrArg (fun f => f ≫ eqToHom qB) ((P).reservoirContext_square pL hl pR hr Y a)
    _ = eA.hom ≫ ((((Y ≫ R) ◁ a) ▷ K) ≫ eqToHom qB) := Category.assoc _ _ _
    _ = eA.hom ≫ (eqToHom qA ≫ E.map b) := congrArg (fun f => eA.hom ≫ f) he
    _ = _ := (Category.assoc _ _ _).symm

end Context
end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
