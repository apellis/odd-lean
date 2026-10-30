import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumGeneratorCoordinates
import OddMath.QuiverHecke.CyclotomicAction.ELVContentPairTensor

/-! # Source comparison for vacuum observations

`VacuumSourceComparison.comparison` identifies the canonical block comparison
with two successive representable evaluations, on the entire balanced quotient.
`mixedCross_coordinates` applies the actual normalized crossing to this iterated
source. This is the source-side ingredient for vacuum observations and detecting
actions, not a reservoir-target-only postcomposition formula. Arbitrary append
blocks and represented prefixes are allowed; the pair corollaries retain full
coefficient parity and the equal-colour minus sign. Identification with the
recursive vacuum-word isomorphism is a further obligation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.VacuumSourceComparison
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I) (σ τ : List I) (γ : Multiset I)
  (h : (β + (σ : Multiset I)) + (τ : Multiset I) = γ)
  (h' : β + ((σ ++ τ : List I) : Multiset I) = γ)
local notation "J" => contentAppend D Sc cutoff N β σ
local notation "K" => contentAppendTo D Sc cutoff N (β + (σ : Multiset I)) τ γ h
local notation "A" => contentAppendTo D Sc cutoff N β (σ ++ τ) γ h'
local notation "H" v => contentRepresentable D Sc cutoff N β v
local notation "e" => contentAppend_comp_eq D Sc cutoff N β σ τ γ h h'

/-- The two successive representable evaluations, independently of the block comparison. -/
def iteratedForward (v : ContentCategory D Sc cutoff N β)
    (z : ContentCategory D Sc cutoff N γ) :
    BalancedInduction.Obj K (BalancedInduction.induced J (H v)).toFunctor z →ₗ[k]
      ((K).obj ((J).obj v) ⟶ z) :=
  (VacuumGeneratorCoordinates.equivTo D Sc cutoff N (β + (σ : Multiset I)) τ γ h
    ((J).obj v) z).toLinearMap ∘ₗ
    BalancedInduction.mapComponent K
      (InductionRepresentable.forwardTransform D Sc cutoff N β σ v) 0 z

theorem iteratedForward_tensor (v t : ContentCategory D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + (σ : Multiset I)))
    (z : ContentCategory D Sc cutoff N γ)
    (b : (K).obj w ⟶ z) (a : (J).obj t ⟶ w) (g : v ⟶ t) :
    iteratedForward D Sc cutoff N β σ τ γ h v z
      (BalancedInduction.tensor K (BalancedInduction.induced J (H v)).toFunctor w b
        (BalancedInduction.tensor J (H v).toFunctor t a g)) =
      (K).map ((J).map g ≫ a) ≫ b := by
  have hm := BalancedInduction.mapComponent_tensor K
    (InductionRepresentable.forwardTransform D Sc cutoff N β σ v) 0 z w b
    (BalancedInduction.tensor J (H v).toFunctor t a g)
  have ht := congrArg
    (VacuumGeneratorCoordinates.equivTo D Sc cutoff N (β + (σ : Multiset I)) τ γ h
      ((J).obj v) z) hm
  refine ht.trans ?_
  simp only [InductionRepresentable.forwardTransform_app, ↓reduceIte, twist_zero]
  change VacuumGeneratorCoordinates.equivTo D Sc cutoff N (β + (σ : Multiset I)) τ γ h
    ((J).obj v) z (BalancedInduction.tensor K
      (contentRepresentableFunctor D Sc cutoff N (β + (σ : Multiset I)) ((J).obj v)) w b
      (InductionRepresentable.forward D Sc cutoff N β σ v w
        (BalancedInduction.tensor J (contentRepresentableFunctor D Sc cutoff N β v) t a g))) = _
  exact (congrArg (fun x => VacuumGeneratorCoordinates.equivTo D Sc cutoff N
    (β + (σ : Multiset I)) τ γ h ((J).obj v) z
    (BalancedInduction.tensor K
      (contentRepresentableFunctor D Sc cutoff N (β + (σ : Multiset I)) ((J).obj v)) w b x))
    (InductionRepresentable.forward_tensor D Sc cutoff N β σ v w t a g)).trans
      (VacuumGeneratorCoordinates.equivTo_tensor D Sc cutoff N
        (β + (σ : Multiset I)) τ γ h ((J).obj v) w z b ((J).map g ≫ a))

/-- The canonical comparison agrees with successive representable evaluation,
including the source endpoint cast. -/
theorem comparison_tensor (v t : ContentCategory D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + (σ : Multiset I)))
    (z : ContentCategory D Sc cutoff N γ)
    (b : (K).obj w ⟶ z) (a : (J).obj t ⟶ w) (g : v ⟶ t) :
    VacuumGeneratorCoordinates.equivTo D Sc cutoff N β (σ ++ τ) γ h' v z
      (((contentInductionComp D Sc cutoff N β σ τ γ h h').hom.app (H v)).total z
        (BalancedInduction.tensor K (BalancedInduction.induced J (H v)).toFunctor w b
          (BalancedInduction.tensor J (H v).toFunctor t a g))) =
    eqToHom (congrArg (fun F => F.obj v) e).symm ≫
      iteratedForward D Sc cutoff N β σ τ γ h v z
        (BalancedInduction.tensor K (BalancedInduction.induced J (H v)).toFunctor w b
          (BalancedInduction.tensor J (H v).toFunctor t a g)) := by
  erw [contentInductionComp_hom_total_tensor, VacuumGeneratorCoordinates.equivTo_tensor,
    iteratedForward_tensor, Functor.map_comp]
  have hn := (eqToIso e).inv.naturality g
  simp only [eqToIso.inv, eqToHom_app, Functor.comp_map] at hn
  simpa only [Category.assoc] using congrArg (fun f => f ≫ (K).map a ≫ b) hn

/-- The iterated evaluation expressed at the block endpoint. -/
def sourceCoordinates (v : ContentCategory D Sc cutoff N β)
    (z : ContentCategory D Sc cutoff N γ) :
    BalancedInduction.Obj K (BalancedInduction.induced J (H v)).toFunctor z →ₗ[k]
      ((A).obj v ⟶ z) where
  toFun x := eqToHom (congrArg (fun F => F.obj v) e).symm ≫
    iteratedForward D Sc cutoff N β σ τ γ h v z x
  map_add' x y := by rw [map_add, Preadditive.comp_add]
  map_smul' r x := by rw [map_smul, Linear.comp_smul]; rfl

private theorem nested_ext {C B E : Type u}
    [Category.{u} C] [Category.{u} B] [Category.{u} E]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    [Preadditive E] [Linear k E] [Supercategory k E]
    (F : C ⥤ B) (G : B ⥤ E)
    [F.Additive] [F.Linear k] [IsSuperfunctor k F]
    [G.Additive] [G.Linear k] [IsSuperfunctor k G]
    (M : Superfunctor k C (SVec k)) (z : E)
    {V : Type u} [AddCommGroup V] [Module k V]
    {f g : BalancedInduction.Obj G (BalancedInduction.induced F M).toFunctor z →ₗ[k] V}
    (he : ∀ (t : C) (w : B) (b : G.obj w ⟶ z) (a : F.obj t ⟶ w) (m : M.obj t),
      f (BalancedInduction.tensor G (BalancedInduction.induced F M).toFunctor w b
        (BalancedInduction.tensor F M.toFunctor t a m)) =
      g (BalancedInduction.tensor G (BalancedInduction.induced F M).toFunctor w b
        (BalancedInduction.tensor F M.toFunctor t a m))) : f = g := by
  apply BalancedInduction.hom_ext
  intro w b x
  let T : BalancedInduction.Obj F M.toFunctor w →ₗ[k]
      BalancedInduction.Obj G (BalancedInduction.induced F M).toFunctor z :=
    BalancedInduction.inclusion G (BalancedInduction.induced F M).toFunctor z w ∘ₗ
      (TensorProduct.mk k (G.obj w ⟶ z) (BalancedInduction.Obj F M.toFunctor w)) b
  have ht : f ∘ₗ T = g ∘ₗ T := by
    apply BalancedInduction.hom_ext
    intro t a m
    exact he t w b a m
  exact congrArg (fun l => l x) ht

/-- Coherence on the entire balanced quotient, not merely identity tensors. -/
theorem comparison (v : ContentCategory D Sc cutoff N β)
    (z : ContentCategory D Sc cutoff N γ) :
    (VacuumGeneratorCoordinates.equivTo D Sc cutoff N β (σ ++ τ) γ h' v z).toLinearMap ∘ₗ
      ((contentInductionComp D Sc cutoff N β σ τ γ h h').hom.app (H v)).total z =
    sourceCoordinates D Sc cutoff N β σ τ γ h h' v z := by
  apply nested_ext J K (H v) z
  intro t w b a g
  exact comparison_tensor D Sc cutoff N β σ τ γ h h' v t w z b a g

end OddMath.QuiverHecke.ELVOld.VacuumSourceComparison

namespace OddMath.QuiverHecke.ELVOld.VacuumSourceComparison
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- Successive single-letter representable coordinates, retaining the content cast. -/
abbrev pairCoordinates (β : Multiset I) (i j : I) (γ : Multiset I)
    (h : β + ([i,j] : Multiset I) = γ) (v : ContentCategory D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N γ) :=
  sourceCoordinates D Sc cutoff N β [i] [j] γ (by rw [add_assoc]; exact h) h v w

theorem pairCoordinates_comparison (β : Multiset I) (i j : I) (γ : Multiset I)
    (h : β + ([i,j] : Multiset I) = γ) (v : ContentCategory D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N γ)
    (x : ContentEPairSpace D Sc cutoff N β i j γ h (contentRepresentable D Sc cutoff N β v) w) :
    pairCoordinates D Sc cutoff N β i j γ h v w x =
      VacuumGeneratorCoordinates.equivTo D Sc cutoff N β [i,j] γ h v w
        (contentEPairEquiv D Sc cutoff N β i j γ h (contentRepresentable D Sc cutoff N β v) w x) :=
  (congrArg (fun f => f x) (comparison D Sc cutoff N β [i] [j] γ _ h v w)).symm

/-- The actual normalized mixed crossing evaluated on the canonical image of
an arbitrary vector of successive single-letter source induction. Its source
coordinates are computed by two successive representable evaluations. -/
theorem mixedCross_coordinates (β : Multiset I) (i j : I) (hne : i ≠ j)
    (v : ContentCategory D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j] : Multiset I)))
    (x : ContentEPairSpace D Sc cutoff N β j i _ (content_pair_swap β i j)
      (contentRepresentable D Sc cutoff N β v) w) :
    VacuumGeneratorCoordinates.equivTo D Sc cutoff N β [i,j] _ rfl v w
      (((contentInductionCross D Sc cutoff N β i j).app (D.parity i * D.parity j)
        (contentRepresentable D Sc cutoff N β v)).app (D.parity i * D.parity j) w
        (contentEPairEquiv D Sc cutoff N β j i _ (content_pair_swap β i j)
          (contentRepresentable D Sc cutoff N β v) w x)) =
      contentAppendToComponent D Sc cutoff N rfl (content_pair_swap β i j) (crossTwo D Sc i j) v ≫
        twist k (D.parity i * D.parity j)
          (pairCoordinates D Sc cutoff N β j i _ (content_pair_swap β i j) v w x) := by
  rw [pairCoordinates_comparison]
  let E := VacuumGeneratorCoordinates.equivTo D Sc cutoff N β [j,i] _ (content_pair_swap β i j) v w
  have hh := VacuumGeneratorCoordinates.mixedCross_coordinates D Sc cutoff N β i j hne v w
    (E (contentEPairEquiv D Sc cutoff N β j i _ (content_pair_swap β i j)
      (contentRepresentable D Sc cutoff N β v) w x))
  dsimp only [E] at hh
  erw [LinearEquiv.symm_apply_apply] at hh
  exact hh

/-- Equal-colour source transport retains the prescribed minus sign. -/
theorem equalCross_coordinates (β : Multiset I) (i : I)
    (v : ContentCategory D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,i] : Multiset I)))
    (x : ContentEPairSpace D Sc cutoff N β i i _ (content_pair_swap β i i)
      (contentRepresentable D Sc cutoff N β v) w) :
    VacuumGeneratorCoordinates.equivTo D Sc cutoff N β [i,i] _ rfl v w
      (((contentInductionCross D Sc cutoff N β i i).app (D.parity i * D.parity i)
        (contentRepresentable D Sc cutoff N β v)).app (D.parity i * D.parity i) w
        (contentEPairEquiv D Sc cutoff N β i i _ (content_pair_swap β i i)
          (contentRepresentable D Sc cutoff N β v) w x)) =
      -(contentAppendToComponent D Sc cutoff N rfl (content_pair_swap β i i) (crossTwo D Sc i i) v ≫
        twist k (D.parity i * D.parity i)
          (pairCoordinates D Sc cutoff N β i i _ (content_pair_swap β i i) v w x)) := by
  rw [pairCoordinates_comparison]
  let E := VacuumGeneratorCoordinates.equivTo D Sc cutoff N β [i,i] _ (content_pair_swap β i i) v w
  have hh := VacuumGeneratorCoordinates.equalCross_coordinates D Sc cutoff N β i v w
    (E (contentEPairEquiv D Sc cutoff N β i i _ (content_pair_swap β i i)
      (contentRepresentable D Sc cutoff N β v) w x))
  dsimp only [E] at hh
  erw [LinearEquiv.symm_apply_apply] at hh
  exact hh

end OddMath.QuiverHecke.ELVOld.VacuumSourceComparison
