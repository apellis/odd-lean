import OddMath.QuiverHecke.CyclotomicAction.ELVCapKernelNaturality
import OddMath.QuiverHecke.CyclotomicAction.ELVUnitDotColumns

/-! # Ordinary-right covariance of the actual unscaled unit/dot columns

The column is exactly the chosen ordinary unit followed by an actual
induction-dot power, in canonical co-Yoneda coordinates. Its source
coefficient is composed without a parity twist.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem inductionUnitDotColumn_comp (i : I) (v t : List I) (n : ℕ)
    (b : Old D Sc cutoff v t) :
    inductionUnitDotColumn D Sc cutoff i v t n b =
      inductionUnitDotSign (k := k) (D.parity i) n •
        ((append D Sc cutoff i).map (X := (⟨v⟩ : OldCategory D Sc cutoff))
          (Y := (⟨t⟩ : OldCategory D Sc cutoff)) b ≫
        ((ideal D Sc cutoff (t ++ [i]) (t ++ [i])).mkQ
          (appendMovingPower D Sc cutoff i t n) :
            (append D Sc cutoff i).obj (⟨t⟩ : OldCategory D Sc cutoff) ⟶
              (append D Sc cutoff i).obj (⟨t⟩ : OldCategory D Sc cutoff))) := by
  rw [inductionUnitDotColumn_apply]
  congr 1
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective b
  rw [appendOutputEmbedding_single, canonicalAppendTarget_projection]
  rfl

/-- The exact ordinary categorical unit/dot column, with no column rescaling. -/
def unitKernelComponent (i : I) (n : ℕ) (v t : OldCategory D Sc cutoff) :
    (v ⟶ t) →ₗ[k] ((append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t) :=
  inductionUnitDotColumn D Sc cutoff i v.word t.word n

theorem unitKernelComponent_precompose (i : I) (n : ℕ)
    {v w : OldCategory D Sc cutoff} (a : v ⟶ w) (t : OldCategory D Sc cutoff) :
    (unitKernelComponent D Sc cutoff i n v t).comp (Linear.leftComp k t a) =
    (Linear.leftComp k ((append D Sc cutoff i).obj t) ((append D Sc cutoff i).map a)).comp
      (unitKernelComponent D Sc cutoff i n w t) := by
  apply LinearMap.ext
  intro b
  cases v with
  | mk v =>
    cases w with
    | mk w =>
      cases t with
      | mk t =>
        change inductionUnitDotColumn D Sc cutoff i v t n (a ≫ b) =
          (append D Sc cutoff i).map a ≫ inductionUnitDotColumn D Sc cutoff i w t n b
        rw [inductionUnitDotColumn_comp, inductionUnitDotColumn_comp,
          Functor.map_comp, Linear.comp_smul, Category.assoc]

/-- The actual unscaled unit/dot-power column is an ordinary-right kernel map. -/
def unitKernel (i : I) (n : ℕ) (t : OldCategory D Sc cutoff) :
    BalancedKernelTensor.inductionKernel (k := k) (𝟭 (OldCategory D Sc cutoff)) t ⟶
      BalancedKernelTensor.inductionKernel (k := k) (append D Sc cutoff i)
        ((append D Sc cutoff i).obj t) where
  app v := ModuleCat.ofHom (unitKernelComponent D Sc cutoff i n v.unop t)
  naturality _ _ a := by
    apply ModuleCat.hom_ext
    exact unitKernelComponent_precompose D Sc cutoff i n a.unop t

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
