import OddMath.QuiverHecke.CyclotomicAction.ELVProbeBlockQuadraticDots
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightDistinctSlides

/-! # The whole-weight original-parameter quadratic of the OLD probe

Brundan–Ellis (1.7), DeformedActionAssembly §6 (9): the two prescribed
positive crossings compose to the original-Sc polynomial in the two
independent whiskered dots. Supported blocks retain their exact chosen
coordinates; absent double predecessors use their constructed zero object.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld ELVOld.BalancedInduction CyclotomicAction
universe u

private theorem orderedPolynomial_total
    {k : Type u} {C A : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category A] [Preadditive A] [Linear k A] [Supercategory k A]
    {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
    (F : Superfunctor k C A) (i j : I) (a b : End F) (N : C) :
    (orderedPairOperatorPolynomial D Sc i j a b).total N =
      orderedPairOperatorPolynomial (R := End (F.obj N)) D Sc i j (a.total N) (b.total N) :=
  orderedPairOperatorPolynomial_map_hom D Sc (supernaturalEndEvaluation F N) i j a b

private theorem orderedPolynomial_component
    {k : Type u} [CommRing k] {J : Type*} {A : J → Type*}
    [∀ j, Category (A j)] [∀ j, Preadditive (A j)] [∀ j, Linear k (A j)]
    {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
    (V : ∀ j, A j) (i j : I) (a b : End V) (t : J) :
    (orderedPairOperatorPolynomial D Sc i j a b) t =
      orderedPairOperatorPolynomial (R := End (V t)) D Sc i j (a t) (b t) :=
  orderedPairOperatorPolynomial_map_hom D Sc (piEndEvaluation V t) i j a b

private theorem conjugate_quadratic {k : Type u} {C : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C]
    {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
    {A A' B B' : C} (e : A = A') (f : B = B') (c : A' ⟶ B') (d : B' ⟶ A')
    (i j : I) (a b : End A')
    (h : c ≫ d = orderedPairOperatorPolynomial D Sc i j a b) :
    (eqToHom e ≫ c ≫ eqToHom f.symm) ≫ (eqToHom f ≫ d ≫ eqToHom e.symm) =
      orderedPairOperatorPolynomial (R := End A) D Sc i j
        (eqToHom e ≫ a ≫ eqToHom e.symm) (eqToHom e ≫ b ≫ eqToHom e.symm) := by
  cases e
  cases f
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using h

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
private def probeEndForget {ν : Multiset I} (N : ProbeCanonicalModules D Sc m ν) :
    End N →ₐ[k] End N.obj :=
  AlgHom.ofLinearMap
    { toFun := fun f => f.hom
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    rfl (fun _ _ => rfl)

private theorem orderedPolynomial_forget (S : SKM.Scalars D k) {ν : Multiset I}
    (N : ProbeCanonicalModules D S m ν) (i j : I) (a b : End N) :
    (orderedPairOperatorPolynomial D Sc i j a b).hom =
      orderedPairOperatorPolynomial (R := End N.obj) D Sc i j a.hom b.hom :=
  orderedPairOperatorPolynomial_map_hom D Sc (probeEndForget D S m N) i j a b

section Crossing
variable (i j : I) (Λ : X) {x₀ xj xi xu : X}
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
local notation "Sc'" => parameterTwist D Sc
local notation "sw" => blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄

/-- Whole selected block-natural maps satisfy the original-parameter quadratic. -/
theorem probeOldBlockDistinctCross_quadratic (hij : i ≠ j)
    (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    probeOldBlockDistinctCross D Sc' m i j Λ h₁ h₂ h₃ h₄ β ε hε ≫
      probeOldBlockDistinctCross D Sc' m j i Λ h₃ h₄ h₁ h₂ β ε (sw hε) =
      orderedPairOperatorPolynomial (R := End (probeOldBlockPairIndTo D Sc' m i j Λ h₁ h₂ β ε hε))
        D Sc j i (probeOldBlockPairInnerDotTo D Sc' m i j Λ h₁ h₂ β ε hε)
          (probeOldBlockPairOuterDotTo D Sc' m i j Λ h₁ h₂ β ε hε) := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro N
  rw [Superfunctor.comp_total, orderedPolynomial_total]
  apply InducedCategory.hom_ext
  change ((probeOldBlockDistinctCross D Sc' m i j Λ h₁ h₂ h₃ h₄ β ε hε).total N).hom ≫
      ((probeOldBlockDistinctCross D Sc' m j i Λ h₃ h₄ h₁ h₂ β ε (sw hε)).total N).hom = _
  rw [orderedPolynomial_forget]
  exact probeOldBlockDistinctCross_quadratic_dots D Sc m i j Λ h₁ h₂ h₃ h₄ hij β ε hε N

/-- Every whole-weight block, including absent predecessors, has the original-Sc quadratic. -/
theorem probeOldActionDistinctCross_quadratic (hij : i ≠ j) :
    probeOldActionDistinctCross D Sc' m i j Λ h₁ h₂ h₃ h₄ ≫
      probeOldActionDistinctCross D Sc' m j i Λ h₃ h₄ h₁ h₂ =
      orderedPairOperatorPolynomial (R := End (probeOldE D Sc' m j Λ h₁ ≫ probeOldE D Sc' m i Λ h₂))
        D Sc j i (probeOldActionDot D Sc' m j Λ h₁ ▷ probeOldE D Sc' m i Λ h₂)
          (probeOldE D Sc' m j Λ h₁ ◁ probeOldActionDot D Sc' m i Λ h₂) := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro M
  rw [Superfunctor.comp_total, orderedPolynomial_total]
  funext ε
  change (probeOldActionDistinctCross D Sc' m i j Λ h₁ h₂ h₃ h₄).total M ε ≫
      (probeOldActionDistinctCross D Sc' m j i Λ h₃ h₄ h₁ h₂).total M ε = _
  rw [orderedPolynomial_component]
  by_cases hε : ∃ β, blockSucc₂ D i j Λ h₁ h₂ β = ε
  · obtain ⟨β, hβ⟩ := hε
    rw [probeOldActionDistinctCross_total_of D Sc' m i j Λ h₁ h₂ h₃ h₄ β ε hβ,
      probeOldActionDistinctCross_total_of D Sc' m j i Λ h₃ h₄ h₁ h₂ β ε (sw hβ),
      probeOldPairInnerDotTo_total D Sc' m i j Λ h₁ h₂ β ε hβ,
      probeOldPairOuterDotTo_total D Sc' m i j Λ h₁ h₂ β ε hβ]
    have hb := congrArg (fun f => f.total (M β))
      (probeOldBlockDistinctCross_quadratic D Sc m i j Λ h₁ h₂ h₃ h₄ hij β ε hβ)
    rw [Superfunctor.comp_total, orderedPolynomial_total] at hb
    exact conjugate_quadratic D Sc _ _ _ _ j i _ _ hb
  · exact (probeOldEFunctor_comp₂_isZero D Sc' m i j Λ h₁ h₂ ε hε M).eq_of_src _ _
end Crossing
end OddMath.QuiverHecke
