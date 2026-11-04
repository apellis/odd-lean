import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorEntryPullback
import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorMatrixCoefficients

/-! # Source coefficients through the prescribed tensor row chart

SwappedVacuumCoordinates §§5–7: the global reservoir-word chart intertwines
the full source coefficient action before and after the original input-weight
transport. This supplies the coefficient square for the specified row pullback.
-/
noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld VacuumTensorCoefficientMaps
universe u
local instance tensorRowCoefficientHomPi {k : Type u} [CommRing k]
    (A C : PiSCat.{u,u,u + 1} k) : PiSupercategory k (A ⟶ C) :=
  PiTwoSupercategory.homPiLeft A C
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (ΛP ΛR : X) (L : I × ℕ → ℕ)
local notation "Tw" => parameterTwist D Sc
local notation "N" => PowerWordContent.powerBound D cutoff L

private def inputAction {x y z : X} (h : x = y)
    (F : probeOldWeightSpace D Tw m ΛP x ⟶ elvWeightSpace D Tw cutoff N ΛR z)
    (φ : SYM D k →ₐ[k] End F) :
    SYM D k →ₐ[k] End (h ▸ F : probeOldWeightSpace D Tw m ΛP y ⟶
      elvWeightSpace D Tw cutoff N ΛR z) := by
  subst y
  exact φ

private theorem inputPost_eq {x y z z' : X} (h : x = y)
    (F : probeOldWeightSpace D Tw m ΛP x ⟶ elvWeightSpace D Tw cutoff N ΛR z)
    (K : elvWeightSpace D Tw cutoff N ΛR z ⟶ elvWeightSpace D Tw cutoff N ΛR z') :
    (h ▸ F : probeOldWeightSpace D Tw m ΛP y ⟶
      elvWeightSpace D Tw cutoff N ΛR z) ≫ K =
    (Pi.eqToEquivalence (fun x => probeOldWeightSpace D Tw m ΛP x ⟶
      elvWeightSpace D Tw cutoff N ΛR z') h).functor.obj (F ≫ K) := by
  subst y
  rfl

private theorem inputPost_square {x y z z' : X} (h : x = y)
    (F : probeOldWeightSpace D Tw m ΛP x ⟶ elvWeightSpace D Tw cutoff N ΛR z)
    (K : elvWeightSpace D Tw cutoff N ΛR z ⟶ elvWeightSpace D Tw cutoff N ΛR z')
    (φ : SYM D k →ₐ[k] End F) (a : SYM D k) :
    (inputAction D Sc m cutoff ΛP ΛR L h F φ a) ▷ K ≫
      eqToHom (inputPost_eq D Sc m cutoff ΛP ΛR L h F K) =
    eqToHom (inputPost_eq D Sc m cutoff ΛP ΛR L h F K) ≫
      (Pi.eqToEquivalence (fun x => probeOldWeightSpace D Tw m ΛP x ⟶
        elvWeightSpace D Tw cutoff N ΛR z') h).functor.map ((φ a) ▷ K) := by
  subst y
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  rfl

variable (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR) (s : List I)
local notation "cS" => tensorSourceContent D ΛP ΛR s
local notation "E" => tensorHomEquivalence D Sc m cutoff L ΛP ΛR (ReservoirWord.weight D ΛR cS)
local notation "P" => elvProbeReservoir D Sc m cutoff N ΛP ΛR hP hR

/-- The specified row target chart intertwines every source coefficient,
including mixed parity coefficients, with its original-weight path action. -/
theorem tensorRowTargetIso_coefficient {b : Obj (SKM.sig D)}
    (p : SPath b.word (0,cS) (0,0)) (hup : ∀ c ∈ b.word, c.l.1 = true)
    (a : SYM D k) :
    ((P).pathFunctor p).map ((tensorVacuumCoefficientAction D Sc m cutoff L ΛP ΛR a).hom) ≫
      (tensorRowTargetIso D Sc m cutoff ΛP ΛR L hP hR s p hup).hom =
    (tensorRowTargetIso D Sc m cutoff ΛP ΛR L hP hR s p hup).hom ≫
      (E).functor.map (pathCoefficientAction D Tw m cutoff L ΛP ΛR p hup a) := by
  let Z := tensorVacuum D Sc m cutoff L ΛP ΛR
  let K := ReservoirWord.word (P).W.toRouquierData ΛR p hup
  have hn := ((P).reservoirWordFunctorIso p hup).hom.naturality
    ((tensorVacuumCoefficientAction D Sc m cutoff L ΛP ΛR a).hom)
  have ht := inputPost_square D Sc m cutoff ΛP ΛR L (probeWeight_vacuum D ΛP).symm
    (WeightTensorVacuum.selectedHom D Tw m cutoff ΛP ΛR L) K
    (sourceCoefficientAction D Tw m cutoff L ΛP ΛR) a
  simp only [tensorRowTargetIso, tensorVacuumPathIso, Iso.trans_hom, Iso.symm_hom,
    eqToIso.hom, eqToIso.inv, Category.assoc, eqToHom_trans, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp] at ⊢
  change ((P).pathFunctor p).map ((tensorVacuumCoefficientAction D Sc m cutoff L ΛP ΛR a).hom) ≫
      ((P).reservoirWordFunctorIso p hup).hom.app Z.obj ≫
        eqToHom (inputPost_eq D Sc m cutoff ΛP ΛR L (probeWeight_vacuum D ΛP).symm
          (WeightTensorVacuum.selectedHom D Tw m cutoff ΛP ΛR L) K) =
    ((P).reservoirWordFunctorIso p hup).hom.app Z.obj ≫
      eqToHom (inputPost_eq D Sc m cutoff ΛP ΛR L (probeWeight_vacuum D ΛP).symm
        (WeightTensorVacuum.selectedHom D Tw m cutoff ΛP ΛR L) K) ≫ _
  rw [← Category.assoc, hn, Category.assoc]
  exact congrArg (fun f => ((P).reservoirWordFunctorIso p hup).hom.app Z.obj ≫ f) ht

/-- Pulling the whole row back to the original probe weight preserves
postcomposition by every full source coefficient. -/
theorem tensorRowPullback_coefficient {b : Obj (SKM.sig D)}
    (p : SPath b.word (0,cS) (0,0)) (hup : ∀ c ∈ b.word, c.l.1 = true)
    (a : SYM D k)
    (f : (tensorSourceFamily D Sc m cutoff ΛP ΛR L s (0,cS)).obj ⟶
      ((P).pathFunctor p).obj (tensorVacuum D Sc m cutoff L ΛP ΛR).obj) :
    TensorEntryPullback.map (E) (tensorRowTargetIso D Sc m cutoff ΛP ΛR L hP hR s p hup)
      (f ≫ ((P).pathFunctor p).map ((tensorVacuumCoefficientAction D Sc m cutoff L ΛP ΛR a).hom)) =
    pathHomCoefficientAction D Tw m cutoff L ΛP ΛR p hup
      (tensorOriginalRowSource D Sc m cutoff ΛP ΛR L s) a
      (TensorEntryPullback.map (E) (tensorRowTargetIso D Sc m cutoff ΛP ΛR L hP hR s p hup) f) :=
  TensorEntryPullback.map_square (E) _ _ f _ _
    (tensorRowTargetIso_coefficient D Sc m cutoff ΛP ΛR L hP hR s p hup a)

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
