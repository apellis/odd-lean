import OddMath.QuiverHecke.CyclotomicAction.ELVContentRectangularCross

/-! The normalized affine crossing with actual intermediate content targets.
The equal-colour branch retains its prescribed extra minus. -/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I) (i j : I) (δj δi γ : Multiset I)
  (hj : β + ([j] : Multiset I) = δj) (hi : β + ([i] : Multiset I) = δi)
  (hL : δj + ([i] : Multiset I) = γ) (hU : δi + ([j] : Multiset I) = γ)
  (hji : β + ([j,i] : Multiset I) = γ) (hij : β + ([i,j] : Multiset I) = γ)
local notation "J" => contentAppendTo D Sc cutoff N β [j] δj hj
local notation "K" => contentAppendTo D Sc cutoff N β [i] δi hi
local notation "L" => contentAppendTo D Sc cutoff N δj [i] γ hL
local notation "U" => contentAppendTo D Sc cutoff N δi [j] γ hU
local notation "F" => contentAppendTo D Sc cutoff N β ([j] ++ [i]) γ hji
local notation "G" => contentAppendTo D Sc cutoff N β ([i] ++ [j]) γ hij
local notation "eF" => contentAppend_compTo_eq D Sc cutoff N β [j] δj hj [i] γ hL hji
local notation "eG" => contentAppend_compTo_eq D Sc cutoff N β [i] δi hi [j] γ hU hij

/-- The raw crossing coefficient, without a distinct-colour premise. -/
theorem contentTargetsCross_raw_coefficient (s : ContentCategory D Sc cutoff N β) :
    contentDistinctTargetsCross D Sc cutoff N β i j δj δi γ hj hi hL hU s =
      eqToHom (congrArg (fun H => CategoryTheory.Functor.obj H s) eF) ≫
        contentAppendToComponent D Sc cutoff N (σ := [j] ++ [i]) (τ := [i] ++ [j]) hji hij
          (crossTwo D Sc j i) s ≫
        eqToHom (congrArg (fun H => CategoryTheory.Functor.obj H s) eG).symm := by
  apply (conj_eqToHom_iff_heq
    (contentDistinctTargetsCross D Sc cutoff N β i j δj δi γ hj hi hL hU s)
    (contentAppendToComponent D Sc cutoff N (σ := [j] ++ [i]) (τ := [i] ++ [j]) hji hij
      (crossTwo D Sc j i) s)
    (congrArg (fun H => CategoryTheory.Functor.obj H s) eF)
    (congrArg (fun H => CategoryTheory.Functor.obj H s) eG)).mpr
  exact truncatedDistinctCrossComponent_heq D Sc cutoff N i j s.obj

/-- The physical rectangular coefficient with the chosen equal-colour normalization. -/
def normalizedContentTargetsCross (s : ContentCategory D Sc cutoff N β) :
    (J ⋙ L).obj s ⟶ (K ⋙ U).obj s :=
  if i = j then -contentDistinctTargetsCross D Sc cutoff N β i j δj δi γ hj hi hL hU s
  else contentDistinctTargetsCross D Sc cutoff N β i j δj δi γ hj hi hL hU s

theorem normalizedContentTargetsCross_supernatural :
    IsSupernatural k (D.parity i * D.parity j)
      (normalizedContentTargetsCross D Sc cutoff N β i j δj δi γ hj hi hL hU) := by
  let hraw := contentDistinctTargetsCross_supernatural D Sc cutoff N β i j δj δi γ hj hi hL hU
  refine { mem := ?_, naturality := ?_ }
  · intro s
    dsimp only [normalizedContentTargetsCross]
    split_ifs
    · exact Submodule.neg_mem _ (hraw.mem s)
    · exact hraw.mem s
  · intro s t p f hf
    by_cases h : i = j
    · simp only [normalizedContentTargetsCross, ite_eq_left h]
      rw [Preadditive.comp_neg, hraw.naturality hf, Preadditive.neg_comp, smul_neg]
    · simpa only [normalizedContentTargetsCross, ite_eq_right h] using hraw.naturality hf

/-- The normalized rectangular coefficient is exactly the independently chosen
normalized affine crossing, including equal colours and all endpoint transports. -/
theorem normalizedContentTargetsCross_coefficient (s : ContentCategory D Sc cutoff N β) :
    normalizedContentTargetsCross D Sc cutoff N β i j δj δi γ hj hi hL hU s =
      eqToHom (congrArg (fun H => CategoryTheory.Functor.obj H s) eF) ≫
        contentAppendToComponent D Sc cutoff N (σ := [j] ++ [i]) (τ := [i] ++ [j]) hji hij
          (contentCrossAffine D Sc j i) s ≫
        eqToHom (congrArg (fun H => CategoryTheory.Functor.obj H s) eG).symm := by
  by_cases h : i = j
  · subst j
    simp only [normalizedContentTargetsCross, contentCrossAffine_equal,
      contentAppendToComponent_neg, Preadditive.comp_neg, Preadditive.neg_comp]
    exact congrArg Neg.neg (contentTargetsCross_raw_coefficient D Sc cutoff N β i i δj δi γ hj hi hL hU hji hij s)
  · simp only [normalizedContentTargetsCross, ite_eq_right h, contentCrossAffine_distinct D Sc j i (Ne.symm h)]
    exact contentTargetsCross_raw_coefficient D Sc cutoff N β i j δj δi γ hj hi hL hU hji hij s

private theorem normalized_contentCompTo_eq_compOfEq
    (η : Multiset I) (σ : List I) (δ : Multiset I) (hδ : η + (σ : Multiset I) = δ)
    (τ : List I) (ζ : Multiset I) (hζ : δ + (τ : Multiset I) = ζ)
    (h : η + ((σ ++ τ : List I) : Multiset I) = ζ) :
    contentInductionCompTo D Sc cutoff N η σ δ hδ τ ζ hζ h =
      inductionCompOfEq (contentAppendTo D Sc cutoff N η σ δ hδ)
        (contentAppendTo D Sc cutoff N δ τ ζ hζ)
        (contentAppendTo D Sc cutoff N η (σ ++ τ) ζ h)
        (contentAppend_compTo_eq D Sc cutoff N η σ δ hδ τ ζ hζ h) := by
  subst δ
  rfl

/-- The independently chosen normalized word crossing is the normalized
rectangular crossing for every colour pair and every actual successor certificate. -/
theorem normalizedContentTargetsCross_comparison
    (P : ContentModules D Sc cutoff N β) :
    ((contentInductionCompTo D Sc cutoff N β [i] δi hi [j] γ hU hij).hom.app P ≫
      (contentInductionTransform D Sc cutoff N (σ := [j] ++ [i]) (τ := [i] ++ [j]) hji hij
        (contentCrossAffine_reverse_mem D Sc i j)).app (D.parity i * D.parity j) P) ≫
      (contentInductionCompTo D Sc cutoff N β [j] δj hj [i] γ hL hji).inv.app P =
        BalancedInduction.rectangularCrossComponent J K L U
          (normalizedContentTargetsCross_supernatural D Sc cutoff N β i j δj δi γ hj hi hL hU) P := by
  have h := inductionCompOfEq_cross J K L U F G eF eG
    (normalizedContentTargetsCross_supernatural D Sc cutoff N β i j δj δi γ hj hi hL hU)
    (contentAppendTo_supernatural D Sc cutoff N (σ := [j] ++ [i]) (τ := [i] ++ [j]) hji hij
      (contentCrossAffine_reverse_mem D Sc i j))
    (normalizedContentTargetsCross_coefficient D Sc cutoff N β i j δj δi γ hj hi hL hU hji hij) P
  dsimp only [contentInductionTo] at h ⊢
  simpa only [normalized_contentCompTo_eq_compOfEq, contentInductionTransform,
    inductionTransform_app_self] using h

end OddMath.QuiverHecke.ELVOld
