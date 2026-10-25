import OddMath.SKM.LeftDot
import OddMath.SKM.SpanLower
import OddMath.SKM.Lemma71
import OddMath.SKM.BubbleCoefficientParity

/-! Actual contextual mixed-crossing isomorphisms for distinct colors. -/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}

/-- The right mixed crossing in arbitrary left/right contexts, at global μ. -/
def contextualSigma (μ : X) (L Q : List (Letter I)) (i j : I) :
    (pres D Sc).obj (ob D μ (L ++ [up j, dn i] ++ Q)) ⟶
      (pres D Sc).obj (ob D μ (L ++ [dn i, up j] ++ Q)) :=
  cl D Sc μ _ _ ((sigmaL i j).map (whL L Q))

def contextualLCross (μ : X) (L Q : List (Letter I)) (i j : I) :
    (pres D Sc).obj (ob D μ (L ++ [dn i, up j] ++ Q)) ⟶
      (pres D Sc).obj (ob D μ (L ++ [up j, dn i] ++ Q)) :=
  cl D Sc μ _ _ ((lcrossL i j).map (whL L Q))

theorem contextualSigma_lcross (μ : X) (L Q : List (Letter I)) (i j : I) (hij : i ≠ j) :
    contextualSigma (D := D) (Sc := Sc) μ L Q i j ≫ contextualLCross μ L Q i j = 𝟙 _ := by
  have E := congrArg (plcL D Sc μ L Q [up j, dn i] [up j, dn i])
    (sg_lc_ne (D := D) (Sc := Sc) i j (wt D μ Q) hij)
  rw [plcL_comp, plcL_cl, plcL_cl, plcL_id] at E
  exact E

theorem contextualLCross_sigma (μ : X) (L Q : List (Letter I)) (i j : I) (hij : i ≠ j) :
    contextualLCross (D := D) (Sc := Sc) μ L Q i j ≫ contextualSigma μ L Q i j = 𝟙 _ := by
  have E := congrArg (plcL D Sc μ L Q [dn i, up j] [dn i, up j])
    (lc_sg_ne (D := D) (Sc := Sc) i j (wt D μ Q) hij)
  rw [plcL_comp, plcL_cl, plcL_cl, plcL_id] at E
  exact E

/-- Target sorting by actual postcomposition, with an actual inverse. -/
def distinctTargetExchange (μ : X) (a L Q : List (Letter I)) (i j : I) (hij : i ≠ j) :
    ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ (L ++ [up j, dn i] ++ Q))) ≃ₗ[k]
      ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ (L ++ [dn i, up j] ++ Q))) where
  toFun f := f ≫ contextualSigma μ L Q i j
  invFun f := f ≫ contextualLCross μ L Q i j
  left_inv f := by dsimp only; rw [Category.assoc, contextualSigma_lcross μ L Q i j hij, Category.comp_id]
  right_inv f := by dsimp only; rw [Category.assoc, contextualLCross_sigma μ L Q i j hij, Category.comp_id]
  map_add' f g := Preadditive.add_comp ..
  map_smul' r f := Linear.smul_comp ..

/-- Source sorting by actual precomposition, with an actual inverse. -/
def distinctSourceExchange (μ : X) (L Q b : List (Letter I)) (i j : I) (hij : i ≠ j) :
    ((pres D Sc).obj (ob D μ (L ++ [dn i, up j] ++ Q)) ⟶ (pres D Sc).obj (ob D μ b)) ≃ₗ[k]
      ((pres D Sc).obj (ob D μ (L ++ [up j, dn i] ++ Q)) ⟶ (pres D Sc).obj (ob D μ b)) where
  toFun f := contextualSigma μ L Q i j ≫ f
  invFun f := contextualLCross μ L Q i j ≫ f
  left_inv f := by dsimp only; rw [← Category.assoc, contextualLCross_sigma μ L Q i j hij, Category.id_comp]
  right_inv f := by dsimp only; rw [← Category.assoc, contextualSigma_lcross μ L Q i j hij, Category.id_comp]
  map_add' f g := Preadditive.comp_add ..
  map_smul' r f := Linear.comp_smul ..

theorem contextualSigma_mem_parity (μ : X) (L Q : List (Letter I)) (i j : I) :
    contextualSigma (D := D) (Sc := Sc) μ L Q i j ∈
      homPar D Sc μ (L ++ [up j, dn i] ++ Q) (L ++ [dn i, up j] ++ Q)
        (D.parity i * D.parity j) := by
  simpa only [contextualSigma, parsum_map_whL, parsum_sigmaL] using
    (cl_mem_homPar' (D := D) (Sc := Sc) μ (L ++ [up j, dn i] ++ Q)
      (L ++ [dn i, up j] ++ Q) ((sigmaL i j).map (whL L Q)))

/-- Target exchange preserves the exact ordered source coefficient. -/
theorem distinctTargetExchange_coefficient (cs : CScalars Sc) (μ : X)
    (a L Q : List (Letter I)) (i j : I) (hij : i ≠ j)
    (f : (pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ (L ++ [up j, dn i] ++ Q)))
    (p : SYM D k) :
    distinctTargetExchange μ a L Q i j hij (bubAt D Sc μ a (betaSYM cs μ p) ≫ f) =
      bubAt D Sc μ a (betaSYM cs μ p) ≫ distinctTargetExchange μ a L Q i j hij f := by
  change (bubAt D Sc μ a (betaSYM cs μ p) ≫ f) ≫ contextualSigma μ L Q i j =
    bubAt D Sc μ a (betaSYM cs μ p) ≫ (f ≫ contextualSigma μ L Q i j)
  exact Category.assoc _ _ _

/-- Source exchange applies the actual full-SYM parity involution, with no
homogeneity restriction on its input coefficient and no scalar t_ij. -/
theorem distinctSourceExchange_coefficient (cs : CScalars Sc) (μ : X)
    (L Q b : List (Letter I)) (i j : I) (hij : i ≠ j)
    (f : (pres D Sc).obj (ob D μ (L ++ [dn i, up j] ++ Q)) ⟶ (pres D Sc).obj (ob D μ b))
    (p : SYM D k) :
    distinctSourceExchange μ L Q b i j hij
      (bubAt D Sc μ (L ++ [dn i, up j] ++ Q) (betaSYM cs μ p) ≫ f) =
      bubAt D Sc μ (L ++ [up j, dn i] ++ Q)
        (betaSYM cs μ (SYM.parityTwist D k (D.parity i * D.parity j) p)) ≫
        distinctSourceExchange μ L Q b i j hij f := by
  change contextualSigma μ L Q i j ≫ (_ ≫ f) = _ ≫ (contextualSigma μ L Q i j ≫ f)
  rw [← Category.assoc, ← source_target_twist cs μ (contextualSigma_mem_parity μ L Q i j),
    Category.assoc]

end OddMath.SKM
