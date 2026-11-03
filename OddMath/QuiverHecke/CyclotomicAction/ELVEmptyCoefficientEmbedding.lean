import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientAnnihilation
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumSupport
import OddMath.QuiverHecke.CyclotomicAction.ELVParabolicSpan

/-! # Full faithfulness of the empty-word coefficient embedding

The identity B_0=A in `DeformedReservoirBound.md`, §2, and the coefficient
input of the literal power vacuum. The affine empty-word PBW coordinate
and the absence of old cyclotomic relations give the exact Hom comparison.
No coefficient independence of the oriented action is assumed.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private def emptyNormalIndex : NFIdx ([] : List I) [] := by
  have hc : Categorification.TypeA.canWord 0 (1 : Equiv.Perm (Fin 0)) = [] := by
    apply List.length_eq_zero_iff.mp
    rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]
  refine ⟨([], 1), by simp, by simp, ?_⟩
  simp only [List.map_nil, List.length_nil, hc, cw, List.reverse_nil, List.nil_append, pl, SChain]

private def affineEmptyCoordinate :
    ((pres D Sc).obj (ob D []) ⟶ (pres D Sc).obj (ob D [])) →ₗ[k] k :=
  (basisNF D Sc [] []).coord (emptyNormalIndex (I := I))

private theorem affineEmptyCoordinate_id : affineEmptyCoordinate D Sc (𝟙 _) = 1 := by
  rw [← vacuum_nf D Sc (emptyNormalIndex (I := I)), affineEmptyCoordinate, ← basisNF_apply]
  change ((basisNF D Sc [] []).repr ((basisNF D Sc [] []) (emptyNormalIndex (I := I))))
    (emptyNormalIndex (I := I)) = 1
  simp only [Module.Basis.repr_self, Finsupp.single_eq_same]

/-- Coefficients at the empty identity, with all exterior coefficients retained. -/
def emptyCoefficientEncoder : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff →ₗ[k]
    Old D Sc cutoff [] [] :=
  (ideal D Sc cutoff [] []).mkQ.comp (ELVPScalar.scalar D Sc cutoff [])

private def rawEmptyCoefficientDecoder : hom D Sc cutoff [] [] →ₗ[k]
    SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff :=
  (TensorProduct.rid k (SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)).toLinearMap.comp
    (TensorProduct.map LinearMap.id (affineEmptyCoordinate D Sc))

/-- The affine-empty PBW coordinate decodes the literal old coefficient
corner. There is no first-position cyclotomic relation at the empty word. -/
def emptyCoefficientDecoder : Old D Sc cutoff [] [] →ₗ[k]
    SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff :=
  (ideal D Sc cutoff [] []).liftQ (rawEmptyCoefficientDecoder D Sc cutoff) (by
    intro f hf
    have hz : f = 0 := by simpa only [ideal_nil, Submodule.mem_bot] using hf
    rw [hz]
    exact Submodule.zero_mem _)

@[simp] theorem emptyCoefficientDecoder_encoder
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    emptyCoefficientDecoder D Sc cutoff (emptyCoefficientEncoder D Sc cutoff a) = a := by
  change (TensorProduct.rid k (SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff))
    (a ⊗ₜ[k] affineEmptyCoordinate D Sc (𝟙 _)) = a
  rw [affineEmptyCoordinate_id, TensorProduct.rid_tmul, one_smul]

@[simp] theorem emptyCoefficientEncoder_decoder (z : Old D Sc cutoff [] []) :
    emptyCoefficientEncoder D Sc cutoff (emptyCoefficientDecoder D Sc cutoff z) = z := by
  obtain ⟨f, rfl⟩ := (ideal D Sc cutoff [] []).mkQ_surjective z
  have hf := vacuum_hom_span D Sc cutoff f
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, rfl⟩ := hf
    change emptyCoefficientEncoder D Sc cutoff
      (emptyCoefficientDecoder D Sc cutoff
        (emptyCoefficientEncoder D Sc cutoff (SKM.SYM.elvCoefficientQuotient D cutoff a))) =
      emptyCoefficientEncoder D Sc cutoff (SKM.SYM.elvCoefficientQuotient D cutoff a)
    rw [emptyCoefficientDecoder_encoder]
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul r x _ hx => simp only [map_smul, hx]

/-- The complete old empty-word Hom is its full coefficient algebra. -/
def emptyCoefficientEquiv : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff ≃ₗ[k]
    Old D Sc cutoff [] [] :=
  LinearEquiv.ofLinearMap (emptyCoefficientEncoder D Sc cutoff) (emptyCoefficientDecoder D Sc cutoff)
    (by apply LinearMap.ext; intro z; exact emptyCoefficientEncoder_decoder D Sc cutoff z)
    (by apply LinearMap.ext; intro a; exact emptyCoefficientDecoder_encoder D Sc cutoff a)

/-- The original coefficient supercategory embeds at the empty old word. -/
def emptyCoefficientEmbedding :
    SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := k) D cutoff) ⥤ OldCategory D Sc cutoff where
  obj _ := ⟨[]⟩
  map f := emptyCoefficientEncoder D Sc cutoff (SuperalgebraCat.toElem f)
  map_id _ := rfl
  map_comp f g := (coefficientEndomorphism_comp D Sc cutoff []
    (SuperalgebraCat.toElem f) (SuperalgebraCat.toElem g)).symm

instance emptyCoefficientEmbedding_additive :
    (emptyCoefficientEmbedding (k := k) D Sc cutoff).Additive where
  map_add := (emptyCoefficientEncoder D Sc cutoff).map_add _ _

instance emptyCoefficientEmbedding_linear :
    (emptyCoefficientEmbedding (k := k) D Sc cutoff).Linear k where
  map_smul f r := (emptyCoefficientEncoder D Sc cutoff).map_smul r (SuperalgebraCat.toElem f)

instance emptyCoefficientEmbedding_super :
    IsSuperfunctor k (emptyCoefficientEmbedding (k := k) D Sc cutoff) where
  map_mem hf := coefficientEndomorphism_mem D Sc cutoff [] hf

instance emptyCoefficientEmbedding_full : (emptyCoefficientEmbedding (k := k) D Sc cutoff).Full where
  map_surjective f := (emptyCoefficientEquiv D Sc cutoff).surjective f

instance emptyCoefficientEmbedding_faithful : (emptyCoefficientEmbedding (k := k) D Sc cutoff).Faithful where
  map_injective h := (emptyCoefficientEquiv D Sc cutoff).injective h

end OddMath.QuiverHecke.ELVOld
