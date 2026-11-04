import OddMath.SKM.PairingExtensionPresentation
import OddMath.SKM.BubblePolynomialExterior
import OddMath.SKM.SpanBubbleProd

/-! # Normalized bubbles under the pairing-extension presentation map

Brundan–Ellis (2.10)–(2.18) and (1.22), used in
`SwappedVacuumCoordinates.md` §7. The supplied normalization units are
pulled back by the original weight projection, so both ordinary and odd
bubbles retain their exact coefficients and height cases.
-/
noncomputable section
namespace OddMath.SKM.PairingExtension
open CategoryTheory StringDiagrams OddMath.QuiverHecke
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X)
  {k : Type w} [CommRing k] (Sc : Scalars D k)
local notation "Dₑ" => ReservoirWeights.pairingExtension D
local notation "Scₑ" => ReservoirWeights.pairingExtensionScalars D Sc

theorem homMap_cl (μ : X) (s t : List (Letter I)) (L : List (LayerData I)) :
    homMap D Sc μ s t (cl D Sc μ s t L) = cl Dₑ Scₑ (μ, 0) s t L := by
  by_cases h : SChain s L t
  · rw [cl_of h, cl_of h, homMap_diag, diagram_mkD]
  · rw [cl_of_not h, cl_of_not h, map_zero]

theorem homMap_bubAt (μ : X) (v : List (Letter I))
    (g : End ((pres D Sc).obj (ob D μ []))) :
    homMap D Sc μ v v (bubAt D Sc μ v g) =
      bubAt Dₑ Scₑ (μ, 0) v (homMap D Sc μ [] [] g) := by
  induction mem_span_cl μ g using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨L, _, rfl⟩ := hg
    rw [bubAt_cl, homMap_cl, homMap_cl, bubAt_cl]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul r x _ hx => simp only [map_smul, hx]

variable (cs : CScalars Sc)
local notation "csₑ" => ReservoirWeights.pairingExtensionCScalars D cs

theorem homMap_etaP (i : I) (μ : X) :
    homMap D Sc μ [] [up i, dn i] (etaP cs i μ) = etaP csₑ i (μ, 0) := by
  simp only [etaP, height, ReservoirWeights.pairingExtensionCScalars_c,
    ReservoirWeights.pairingExtension_ipar_original]
  split_ifs <;> simp only [map_smul, homMap_cl]

theorem homMap_epsP (i : I) (μ : X) :
    homMap D Sc μ [dn i, up i] [] (epsP cs i μ) = epsP csₑ i (μ, 0) := by
  simp only [epsP, height, ReservoirWeights.pairingExtensionCScalars_c,
    ReservoirWeights.pairingExtension_parity]
  split_ifs <;> simp only [map_smul, homMap_cl]

theorem homMap_bubL (i : I) (μ : X) (n : ℤ) :
    homMap D Sc μ [] [] (bubL cs i μ n) = bubL csₑ i (μ, 0) n := by
  simp only [bubL, height, ReservoirWeights.pairingExtensionCScalars_c,
    ReservoirWeights.pairingExtension_parity]
  split_ifs <;>
    simp only [homMap_comp, homMap_etaP, homMap_cl, map_smul, homMap_id, map_zero]

theorem homMap_bubR (i : I) (μ : X) (n : ℤ) :
    homMap D Sc μ [] [] (bubR cs i μ n) = bubR csₑ i (μ, 0) n := by
  simp only [bubR, height, ReservoirWeights.pairingExtensionCScalars_c,
    ReservoirWeights.pairingExtension_parity]
  split_ifs <;>
    simp only [homMap_comp, homMap_epsP, homMap_cl, map_smul, homMap_id, map_zero]

theorem homMap_oddBubble (i : I) (μ : X) :
    homMap D Sc μ [] [] (oddBubble cs i μ) = oddBubble csₑ i (μ, 0) := by
  simp only [oddBubble, height, ReservoirWeights.pairingExtensionCScalars_c]
  split_ifs <;> simp only [map_smul, homMap_bubL, homMap_bubR]

/-- The abstract coefficient algebra only depends on the unchanged colour parities. -/
def coefficientEquiv : SYM D k ≃ₐ[k] SYM Dₑ k :=
  (SYM.polynomialExteriorEquiv D k).trans (SYM.polynomialExteriorEquiv Dₑ k).symm

@[simp] theorem coefficientEquiv_ι (g : SYMGen D) :
    coefficientEquiv D (SYM.ι D k g) = SYM.ι Dₑ k g := by
  apply (SYM.polynomialExteriorEquiv Dₑ k).injective
  change (SYM.polynomialExteriorEquiv Dₑ k)
    ((SYM.polynomialExteriorEquiv Dₑ k).symm ((SYM.polynomialExteriorEquiv D k) (SYM.ι D k g))) = _
  rw [AlgEquiv.apply_symm_apply]
  rcases g with ⟨i,n⟩ | i
  · change SYM.polynomialExteriorProjection D k (SYM.e D k i n) =
      SYM.polynomialExteriorProjection Dₑ k (SYM.e Dₑ k i n)
    rw [SYM.polynomialExteriorProjection_e, SYM.polynomialExteriorProjection_e]
  · change SYM.polynomialExteriorProjection D k (SYM.delta D k i) =
      SYM.polynomialExteriorProjection Dₑ k (SYM.delta Dₑ k i)
    rw [SYM.polynomialExteriorProjection_delta, SYM.polynomialExteriorProjection_delta]
    rfl

theorem homMap_betaSYMGen (μ : X) (g : SYMGen D) :
    homMap D Sc μ [] [] (betaSYMGen cs μ g) = betaSYMGen csₑ (μ, 0) g := by
  rcases g with ⟨i,n⟩ | i
  · simp only [betaSYMGen, ReservoirWeights.pairingExtension_parity]
    split_ifs <;>
      simp only [betaGen, betaDGen, bubLs, height,
        ReservoirWeights.pairingExtensionCScalars_c, map_smul, homMap_bubL]
  · exact homMap_oddBubble D Sc cs i μ

/-- The presentation map on the algebra of closed diagrams. -/
def closedMap (μ : X) : End ((pres D Sc).obj (ob D μ [])) →ₐ[k]
    End ((pres Dₑ Scₑ).obj (ob Dₑ (μ, 0) [])) where
  toFun := homMap D Sc μ [] []
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := homMap_id D Sc μ []
  map_mul' f g := homMap_comp D Sc μ g f
  commutes' r := by
    change homMap D Sc μ [] [] (r • 𝟙 _) = r • 𝟙 _
    rw [map_smul, homMap_id]

theorem homMap_betaSYM (μ : X) (a : SYM D k) :
    homMap D Sc μ [] [] (betaSYM cs μ a) =
      betaSYM csₑ (μ, 0) (coefficientEquiv D a) := by
  have h : (closedMap D Sc μ).comp (betaSYM cs μ) =
      (betaSYM csₑ (μ, 0)).comp (coefficientEquiv (k := k) D).toAlgHom := by
    apply SYM.hom_ext
    intro g
    change homMap D Sc μ [] [] (betaSYM cs μ (SYM.ι D k g)) =
      betaSYM csₑ (μ, 0) (coefficientEquiv D (SYM.ι D k g))
    rw [coefficientEquiv_ι, betaSYM_ι, betaSYM_ι]
    exact homMap_betaSYMGen D Sc cs μ g
  exact congrArg (fun f => f a) h

/-- Source placement and the full normalized coefficient algebra commute with pullback. -/
theorem homMap_bubAt_betaSYM (μ : X) (v : List (Letter I)) (a : SYM D k) :
    homMap D Sc μ v v (bubAt D Sc μ v (betaSYM cs μ a)) =
      bubAt Dₑ Scₑ (μ, 0) v (betaSYM csₑ (μ, 0) (coefficientEquiv D a)) := by
  rw [homMap_bubAt, homMap_betaSYM]

end OddMath.SKM.PairingExtension
