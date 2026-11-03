import OddMath.QuiverHecke.CyclotomicAction.ELVInductionRectangularTriple
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleMulticolourBraid

/-! # Braids on a cube of balanced induction functors

Brundan–Ellis (1.9): the six prescribed rectangular crossing comparisons
transport a source braid through twelve independent induction edges.
The source equation is an explicit input only to this generic transport
lemma; concrete OLD quotient specializations supply it.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
private theorem cube_three_squares {C : Type*} [Category* C]
    {X₀ X₁ X₂ X₃ Y₀ Y₁ Y₂ Y₃ : C}
    (e₀ : X₀ ⟶ Y₀) (e₁ : X₁ ⟶ Y₁) (e₂ : X₂ ⟶ Y₂) (e₃ : X₃ ⟶ Y₃)
    (a₀ : X₀ ⟶ X₁) (a₁ : X₁ ⟶ X₂) (a₂ : X₂ ⟶ X₃)
    (b₀ : Y₀ ⟶ Y₁) (b₁ : Y₁ ⟶ Y₂) (b₂ : Y₂ ⟶ Y₃)
    (h₀ : a₀ ≫ e₁ = e₀ ≫ b₀) (h₁ : a₁ ≫ e₂ = e₁ ≫ b₁)
    (h₂ : a₂ ≫ e₃ = e₂ ≫ b₂) :
    (a₀ ≫ a₁ ≫ a₂) ≫ e₃ = e₀ ≫ (b₀ ≫ b₁ ≫ b₂) := by
  simp only [Category.assoc]
  rw [h₂, ← Category.assoc a₁, h₁, Category.assoc e₁, ← Category.assoc a₀, h₀, Category.assoc]

variable {k C Aᵢ Aⱼ Aₗ Pᵢⱼ Pᵢₗ Pⱼₗ T : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} Aᵢ] [Preadditive Aᵢ] [Linear k Aᵢ] [Supercategory k Aᵢ]
  [Category.{u} Aⱼ] [Preadditive Aⱼ] [Linear k Aⱼ] [Supercategory k Aⱼ]
  [Category.{u} Aₗ] [Preadditive Aₗ] [Linear k Aₗ] [Supercategory k Aₗ]
  [Category.{u} Pᵢⱼ] [Preadditive Pᵢⱼ] [Linear k Pᵢⱼ] [Supercategory k Pᵢⱼ]
  [Category.{u} Pᵢₗ] [Preadditive Pᵢₗ] [Linear k Pᵢₗ] [Supercategory k Pᵢₗ]
  [Category.{u} Pⱼₗ] [Preadditive Pⱼₗ] [Linear k Pⱼₗ] [Supercategory k Pⱼₗ]
  [Category.{u} T] [Preadditive T] [Linear k T] [Supercategory k T]
  (Ai : C ⥤ Aᵢ) [Ai.Additive] [Ai.Linear k] [IsSuperfunctor k Ai]
  (Aj : C ⥤ Aⱼ) [Aj.Additive] [Aj.Linear k] [IsSuperfunctor k Aj]
  (Al : C ⥤ Aₗ) [Al.Additive] [Al.Linear k] [IsSuperfunctor k Al]
  (Bij_i : Aᵢ ⥤ Pᵢⱼ) [Bij_i.Additive] [Bij_i.Linear k] [IsSuperfunctor k Bij_i]
  (Bij_j : Aⱼ ⥤ Pᵢⱼ) [Bij_j.Additive] [Bij_j.Linear k] [IsSuperfunctor k Bij_j]
  (Bil_i : Aᵢ ⥤ Pᵢₗ) [Bil_i.Additive] [Bil_i.Linear k] [IsSuperfunctor k Bil_i]
  (Bil_l : Aₗ ⥤ Pᵢₗ) [Bil_l.Additive] [Bil_l.Linear k] [IsSuperfunctor k Bil_l]
  (Bjl_j : Aⱼ ⥤ Pⱼₗ) [Bjl_j.Additive] [Bjl_j.Linear k] [IsSuperfunctor k Bjl_j]
  (Bjl_l : Aₗ ⥤ Pⱼₗ) [Bjl_l.Additive] [Bjl_l.Linear k] [IsSuperfunctor k Bjl_l]
  (Cl : Pᵢⱼ ⥤ T) [Cl.Additive] [Cl.Linear k] [IsSuperfunctor k Cl]
  (Cj : Pᵢₗ ⥤ T) [Cj.Additive] [Cj.Linear k] [IsSuperfunctor k Cj]
  (Ci : Pⱼₗ ⥤ T) [Ci.Additive] [Ci.Linear k] [IsSuperfunctor k Ci]
  {p q r : ZMod 2}
  {α₀ : ∀ s, (Ai ⋙ Bij_i).obj s ⟶ (Aj ⋙ Bij_j).obj s}
  {α₁ : ∀ s, (Bij_j ⋙ Cl).obj s ⟶ (Bjl_j ⋙ Ci).obj s}
  {α₂ : ∀ s, (Aj ⋙ Bjl_j).obj s ⟶ (Al ⋙ Bjl_l).obj s}
  {β₀ : ∀ s, (Bij_i ⋙ Cl).obj s ⟶ (Bil_i ⋙ Cj).obj s}
  {β₁ : ∀ s, (Ai ⋙ Bil_i).obj s ⟶ (Al ⋙ Bil_l).obj s}
  {β₂ : ∀ s, (Bil_l ⋙ Cj).obj s ⟶ (Bjl_l ⋙ Ci).obj s}
  (hα₀ : IsSupernatural k p α₀) (hα₁ : IsSupernatural k q α₁)
  (hα₂ : IsSupernatural k r α₂) (hβ₀ : IsSupernatural k r β₀)
  (hβ₁ : IsSupernatural k q β₁) (hβ₂ : IsSupernatural k p β₂)

/-- The first path around the induction cube, with three independent pair crossings. -/
def inductionCubeLeftBraid (N : Superfunctor k C (SVec k)) :
    induced Ci (induced Bjl_l (induced Al N)) ⟶ induced Cl (induced Bij_i (induced Ai N)) :=
  (induction Ci).map (rectangularCrossComponent Aj Al Bjl_j Bjl_l hα₂ N) ≫
    rectangularCrossComponent Bij_j Bjl_j Cl Ci hα₁ ((induction Aj).obj N) ≫
      (induction Cl).map (rectangularCrossComponent Ai Aj Bij_i Bij_j hα₀ N)

/-- The second path uses the other three pairs of the same twelve edges. -/
def inductionCubeRightBraid (N : Superfunctor k C (SVec k)) :
    induced Ci (induced Bjl_l (induced Al N)) ⟶ induced Cl (induced Bij_i (induced Ai N)) :=
  rectangularCrossComponent Bil_l Bjl_l Cj Ci hβ₂ ((induction Al).obj N) ≫
    (induction Cj).map (rectangularCrossComponent Ai Al Bil_i Bil_l hβ₁ N) ≫
      rectangularCrossComponent Bij_i Bil_i Cl Cj hβ₀ ((induction Ai).obj N)

/-- The six flattening squares transport the literal source braid. -/
theorem inductionCube_braid
    (hb : ∀ s, Cl.map (α₀ s) ≫ α₁ (Aj.obj s) ≫ Ci.map (α₂ s) =
      β₀ (Ai.obj s) ≫ Cj.map (β₁ s) ≫ β₂ (Al.obj s))
    (N : Superfunctor k C (SVec k)) :
    inductionCubeLeftBraid Ai Aj Al Bij_i Bij_j Bjl_j Bjl_l Cl Ci hα₀ hα₁ hα₂ N =
      inductionCubeRightBraid Ai Al Bij_i Bil_i Bil_l Bjl_l Cl Cj Ci hβ₀ hβ₁ hβ₂ N := by
  let e₀ := inductionTripleFlattening Al Bjl_l Ci N
  let e₁ := inductionTripleFlattening Aj Bjl_j Ci N
  let e₂ := inductionTripleFlattening Aj Bij_j Cl N
  let e₃ := inductionTripleFlattening Ai Bij_i Cl N
  let e₄ := inductionTripleFlattening Al Bil_l Cj N
  let e₅ := inductionTripleFlattening Ai Bil_i Cj N
  have hL := cube_three_squares e₀.hom e₁.hom e₂.hom e₃.hom
    ((induction Ci).map (rectangularCrossComponent Aj Al Bjl_j Bjl_l hα₂ N))
    (rectangularCrossComponent Bij_j Bjl_j Cl Ci hα₁ ((induction Aj).obj N))
    ((induction Cl).map (rectangularCrossComponent Ai Aj Bij_i Bij_j hα₀ N))
    (transformComponent (hα₂.whiskerRight Ci) N)
    (transformComponent (hα₁.whiskerLeft Aj) N)
    (transformComponent (hα₀.whiskerRight Cl) N)
    (inductionTripleFlattening_prefix_rectangular Al Bjl_l Aj Bjl_j Ci hα₂ N)
    (inductionTripleFlattening_suffix_rectangular Aj Bjl_j Ci Bij_j Cl hα₁ N)
    (inductionTripleFlattening_prefix_rectangular Aj Bij_j Ai Bij_i Cl hα₀ N)
  have hR := cube_three_squares e₀.hom e₄.hom e₅.hom e₃.hom
    (rectangularCrossComponent Bil_l Bjl_l Cj Ci hβ₂ ((induction Al).obj N))
    ((induction Cj).map (rectangularCrossComponent Ai Al Bil_i Bil_l hβ₁ N))
    (rectangularCrossComponent Bij_i Bil_i Cl Cj hβ₀ ((induction Ai).obj N))
    (transformComponent (hβ₂.whiskerLeft Al) N)
    (transformComponent (hβ₁.whiskerRight Cj) N)
    (transformComponent (hβ₀.whiskerLeft Ai) N)
    (inductionTripleFlattening_suffix_rectangular Al Bjl_l Ci Bil_l Cj hβ₂ N)
    (inductionTripleFlattening_prefix_rectangular Al Bil_l Ai Bil_i Cj hβ₁ N)
    (inductionTripleFlattening_suffix_rectangular Ai Bil_i Cj Bij_i Cl hβ₀ N)
  have hd := transformComponent_multicolour_braid
    ((Ai ⋙ Bij_i) ⋙ Cl) ((Aj ⋙ Bij_j) ⋙ Cl) ((Aj ⋙ Bjl_j) ⋙ Ci)
    ((Al ⋙ Bjl_l) ⋙ Ci) ((Ai ⋙ Bil_i) ⋙ Cj) ((Al ⋙ Bil_l) ⋙ Cj)
    (hα₀.whiskerRight Cl) (hα₁.whiskerLeft Aj) (hα₂.whiskerRight Ci)
    (hβ₀.whiskerLeft Ai) (hβ₁.whiskerRight Cj) (hβ₂.whiskerLeft Al) hb N
  apply (cancel_mono e₃.hom).mp
  exact hL.trans ((congrArg (fun f => e₀.hom ≫ f) hd).trans hR.symm)

end OddMath.QuiverHecke.ELVOld.BalancedInduction
