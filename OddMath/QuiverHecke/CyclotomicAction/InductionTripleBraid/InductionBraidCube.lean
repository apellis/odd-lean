import OddMath.QuiverHecke.CyclotomicAction.InductionGridRouquier.InductionGridRelations
import OddMath.QuiverHecke.CyclotomicAction.InductionTripleBraid.VacuumTensor

/-!
# Induction triple braid

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Braids on a cube of balanced induction functors

Brundan–Ellis (1.9): the six prescribed rectangular crossing comparisons
transport a source braid through twelve independent induction edges.
The source equation is an explicit input only to this generic transport
lemma; concrete OLD quotient specializations supply it.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
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

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # The three independent dots under triple-induction flattening

Brundan–Ellis (1.9): the one chosen triple flattening intertwines the
first, middle and last independently whiskered induction dots with their
literal source positional transformations. Changing categories and the
ordinary induction-composition isomorphisms are retained throughout.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u

private theorem mapped_dot_square
    {C A : Type*} [Category* C] [Category* A] (F : C ⥤ A)
    {X Y : C} {Z : A} (a : End X) (e : X ⟶ Y) (b : End Y)
    (f : F.obj Y ⟶ Z) (c : End Z)
    (ha : a ≫ e = e ≫ b) (hb : F.map b ≫ f = f ≫ c) :
    F.map a ≫ (F.map e ≫ f) = (F.map e ≫ f) ≫ c := by
  rw [← Category.assoc, ← Functor.map_comp, ha, Functor.map_comp,
    Category.assoc, hb, Category.assoc]

private theorem composite_dot_square {C : Type*} [Category* C]
    {X Y Z : C} (a : End X) (e : X ⟶ Y) (b : End Y) (f : Y ⟶ Z) (c : End Z)
    (ha : a ≫ e = e ≫ b) (hb : b ≫ f = f ≫ c) :
    a ≫ (e ≫ f) = (e ≫ f) ≫ c := by
  rw [← Category.assoc, ha, Category.assoc, hb, Category.assoc]

variable {k C A B E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  (L : B ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]

/-- The actual first dot, mapped by both later inductions, uses the selected triple flattening. -/
theorem inductionTripleFlattening_first_dot {p : ZMod 2}
    {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k)) :
    (induction L).map ((induction K).map (dotEnd J hα M)) ≫
        (inductionTripleFlattening J K L M).hom =
      (inductionTripleFlattening J K L M).hom ≫
        dotEnd ((J ⋙ K) ⋙ L) ((hα.whiskerRight K).whiskerRight L) M :=
  mapped_dot_square (induction L) ((induction K).map (dotEnd J hα M))
    ((inductionComp J K).hom.app M) (dotEnd (J ⋙ K) (hα.whiskerRight K) M)
    ((inductionComp (J ⋙ K) L).hom.app M)
    (dotEnd ((J ⋙ K) ⋙ L) ((hα.whiskerRight K).whiskerRight L) M)
    (inductionComp_inner_dot J K hα M) (inductionComp_inner_dot (J ⋙ K) L (hα.whiskerRight K) M)

/-- The independently chosen middle dot uses that same triple flattening. -/
theorem inductionTripleFlattening_middle_dot {p : ZMod 2}
    {β : ∀ s, K.obj s ⟶ K.obj s} (hβ : IsSupernatural k p β)
    (M : Superfunctor k C (SVec k)) :
    (induction L).map (dotEnd K hβ ((induction J).obj M)) ≫
        (inductionTripleFlattening J K L M).hom =
      (inductionTripleFlattening J K L M).hom ≫
        dotEnd ((J ⋙ K) ⋙ L) ((hβ.whiskerLeft J).whiskerRight L) M :=
  mapped_dot_square (induction L) (dotEnd K hβ ((induction J).obj M))
    ((inductionComp J K).hom.app M) (dotEnd (J ⋙ K) (hβ.whiskerLeft J) M)
    ((inductionComp (J ⋙ K) L).hom.app M)
    (dotEnd ((J ⋙ K) ⋙ L) ((hβ.whiskerLeft J).whiskerRight L) M)
    (inductionComp_outer_dot J K hβ M) (inductionComp_inner_dot (J ⋙ K) L (hβ.whiskerLeft J) M)

/-- The independent last dot uses the prefix-first flattening via its proved suffix equality. -/
theorem inductionTripleFlattening_last_dot {p : ZMod 2}
    {γ : ∀ s, L.obj s ⟶ L.obj s} (hγ : IsSupernatural k p γ)
    (M : Superfunctor k C (SVec k)) :
    dotEnd L hγ ((induction K).obj ((induction J).obj M)) ≫
        (inductionTripleFlattening J K L M).hom =
      (inductionTripleFlattening J K L M).hom ≫
        dotEnd ((J ⋙ K) ⋙ L) (hγ.whiskerLeft (J ⋙ K)) M := by
  rw [inductionTripleFlattening_suffix]
  exact composite_dot_square
    (dotEnd L hγ ((induction K).obj ((induction J).obj M)))
    ((inductionComp K L).hom.app ((induction J).obj M))
    (dotEnd (K ⋙ L) (hγ.whiskerLeft K) ((induction J).obj M))
    ((inductionComp J (K ⋙ L)).hom.app M)
    (dotEnd ((J ⋙ K) ⋙ L) (hγ.whiskerLeft (J ⋙ K)) M)
    (inductionComp_outer_dot K L hγ ((induction J).obj M))
    (inductionComp_outer_dot J (K ⋙ L) (hγ.whiskerLeft K) M)

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # The whole original-parameter correction through the triple chart

Brundan–Ellis (1.9): the polynomial in the three independent nested
induction dots is the same original-Sc correction through the prescribed
triple flattening. The source correction and its naturality are constructed
from the dots and parameter support, without comparison premises.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u

private theorem triple_transform_total {k C E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    {F G : C ⥤ E} [F.Additive] [F.Linear k] [IsSuperfunctor k F]
    [G.Additive] [G.Linear k] [IsSuperfunctor k G]
    {p : ZMod 2} {γ : ∀ s, F.obj s ⟶ G.obj s} (hγ : IsSupernatural k p γ)
    (N : Superfunctor k C (SVec k)) (w : E) :
    (transformComponent hγ N).total w = transformLinear hγ N w := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp only [SuperNatTrans.total, transformComponent_app,
      ite_true, ite_false, zero_ne_one, one_ne_zero, add_zero, zero_add]

variable {k C E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (F : C ⥤ E) [F.Additive] [F.Linear k] [IsSuperfunctor k F]
  {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (i j : I) {a b c : ∀ s, End (F.obj s)}
  (ha : IsSupernatural k (D.parity i) a) (hb : IsSupernatural k (D.parity j) b)
  (hc : IsSupernatural k (D.parity i) c)

/-- The entire module correction is the original-Sc ordered polynomial. -/
theorem transformComponent_triplePolynomial (hij : i ≠ j)
    (N : Superfunctor k C (SVec k)) :
    tripleDotCorrectionPolynomial D Sc (R := End (induced F N)) i j
        (transformComponent ha N) (transformComponent hb N) (transformComponent hc N) =
      sign k (D.parity i * D.parity j) •
        transformComponent (tripleSourcePolynomial_supernatural F D (parameterTwist D Sc)
          i j ha hb hc hij) N := by
  apply OddMath.FiniteSupermodule.hom_ext_total
  intro w
  let ev : End (induced F N) →ₐ[k] Module.End k ((induced F N).obj w) :=
    (svecEndEvaluation ((induced F N).obj w)).comp (supernaturalEndEvaluation (induced F N) w)
  change ev (tripleDotCorrectionPolynomial D Sc i j
      (transformComponent ha N) (transformComponent hb N) (transformComponent hc N)) =
    ev (sign k (D.parity i * D.parity j) • transformComponent
      (tripleSourcePolynomial_supernatural F D (parameterTwist D Sc) i j ha hb hc hij) N)
  rw [tripleDotCorrectionPolynomial_map, map_smul]
  change tripleDotCorrectionPolynomial D Sc (R := Module.End k ((induced F N).obj w)) i j
      ((transformComponent ha N).total w) ((transformComponent hb N).total w)
      ((transformComponent hc N).total w) =
    sign k (D.parity i * D.parity j) •
      ((transformComponent (tripleSourcePolynomial_supernatural F D (parameterTwist D Sc)
        i j ha hb hc hij) N).total w)
  rw [triple_transform_total, triple_transform_total, triple_transform_total, triple_transform_total]
  exact transformLinear_triplePolynomial_eq F D Sc i j ha hb hc hij N w

section Chart
variable {A B : Type u}
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  (L : B ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]
  {α : ∀ s, End (J.obj s)} {β : ∀ s, End (K.obj s)} {γ : ∀ s, End (L.obj s)}
  (hα : IsSupernatural k (D.parity i) α) (hβ : IsSupernatural k (D.parity j) β)
  (hγ : IsSupernatural k (D.parity i) γ)

/-- The actual three nested dots give the same correction under the chosen triple chart. -/
theorem inductionTripleFlattening_polynomial (hij : i ≠ j)
    (N : Superfunctor k C (SVec k)) :
    tripleDotCorrectionPolynomial D Sc (R := End (induced L (induced K (induced J N)))) i j
        ((induction L).map ((induction K).map (dotEnd J hα N)))
        ((induction L).map (dotEnd K hβ ((induction J).obj N)))
        (dotEnd L hγ ((induction K).obj ((induction J).obj N))) =
      inductionEndConjugation (k := k) (inductionTripleFlattening J K L N)
        (sign k (D.parity i * D.parity j) • transformComponent
          (tripleSourcePolynomial_supernatural ((J ⋙ K) ⋙ L) D (parameterTwist D Sc) i j
            ((hα.whiskerRight K).whiskerRight L) ((hβ.whiskerLeft J).whiskerRight L)
            (hγ.whiskerLeft (J ⋙ K)) hij) N) := by
  let e := inductionTripleFlattening J K L N
  have ht := transformComponent_triplePolynomial ((J ⋙ K) ⋙ L) D Sc i j
    ((hα.whiskerRight K).whiskerRight L) ((hβ.whiskerLeft J).whiskerRight L)
    (hγ.whiskerLeft (J ⋙ K)) hij N
  have hp := congrArg (fun z : End (induced ((J ⋙ K) ⋙ L) N) =>
    inductionEndConjugation (k := k) e z) ht
  rw [tripleDotCorrectionPolynomial_map] at hp
  have h₁ : inductionEndConjugation (k := k) e
      (transformComponent ((hα.whiskerRight K).whiskerRight L) N) =
      (induction L).map ((induction K).map (dotEnd J hα N)) :=
    inductionEndConjugation_of_square e _ _ (inductionTripleFlattening_first_dot J K L hα N)
  have h₂ : inductionEndConjugation (k := k) e
      (transformComponent ((hβ.whiskerLeft J).whiskerRight L) N) =
      (induction L).map (dotEnd K hβ ((induction J).obj N)) :=
    inductionEndConjugation_of_square e _ _ (inductionTripleFlattening_middle_dot J K L hβ N)
  have h₃ : inductionEndConjugation (k := k) e
      (transformComponent (hγ.whiskerLeft (J ⋙ K)) N) =
      dotEnd L hγ ((induction K).obj ((induction J).obj N)) :=
    inductionEndConjugation_of_square e _ _ (inductionTripleFlattening_last_dot J K L hγ N)
  rw [h₁, h₂, h₃] at hp
  exact hp
end Chart
end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # The corrected braid on a seven-edge induction grid

Brundan–Ellis (1.9): retain the seven different append edges in the three
repeated-outer orderings. The six independent rectangular/equal crossings
and three independent dots are compared through the chosen triple charts.
The generic intermediate takes the literal source coefficient equation;
concrete stored-target actions must discharge it from the OLD quotient.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u

private theorem grid_three_squares {C : Type*} [Category* C]
    {X₀ X₁ X₂ X₃ Y₀ Y₁ Y₂ Y₃ : C}
    (e₀ : X₀ ⟶ Y₀) (e₁ : X₁ ⟶ Y₁) (e₂ : X₂ ⟶ Y₂) (e₃ : X₃ ⟶ Y₃)
    (a₀ : X₀ ⟶ X₁) (a₁ : X₁ ⟶ X₂) (a₂ : X₂ ⟶ X₃)
    (b₀ : Y₀ ⟶ Y₁) (b₁ : Y₁ ⟶ Y₂) (b₂ : Y₂ ⟶ Y₃)
    (h₀ : a₀ ≫ e₁ = e₀ ≫ b₀) (h₁ : a₁ ≫ e₂ = e₁ ≫ b₁)
    (h₂ : a₂ ≫ e₃ = e₂ ≫ b₂) :
    (a₀ ≫ a₁ ≫ a₂) ≫ e₃ = e₀ ≫ (b₀ ≫ b₁ ≫ b₂) := by
  simp only [Category.assoc]
  rw [h₂, ← Category.assoc a₁, h₁, Category.assoc e₁,
    ← Category.assoc a₀, h₀, Category.assoc]

private theorem grid_negative_square {C : Type*} [Category* C] [Preadditive C]
    {X Y : C} (a : End X) (e : X ⟶ Y) (b : End Y)
    (h : a ≫ e = e ≫ b) : (-a) ≫ e = e ≫ (-b) := by
  rw [Preadditive.neg_comp, Preadditive.comp_neg, h]

private theorem grid_difference_square {C : Type*} [Category* C] [Preadditive C]
    {X Y : C} (a b : End X) (c d : End Y) (e : X ⟶ Y)
    (ha : a ≫ e = e ≫ c) (hb : b ≫ e = e ≫ d) :
    (a - b) ≫ e = e ≫ (c - d) := by
  rw [Preadditive.sub_comp, Preadditive.comp_sub, ha, hb]

variable {k C A B P Q E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  [Category.{u} P] [Preadditive P] [Linear k P] [Supercategory k P]
  [Category.{u} Q] [Preadditive Q] [Linear k Q] [Supercategory k Q]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : C ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  (U : A ⥤ P) [U.Additive] [U.Linear k] [IsSuperfunctor k U]
  (V : A ⥤ Q) [V.Additive] [V.Linear k] [IsSuperfunctor k V]
  (W : B ⥤ Q) [W.Additive] [W.Linear k] [IsSuperfunctor k W]
  (L : P ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]
  (M : Q ⥤ E) [M.Additive] [M.Linear k] [IsSuperfunctor k M]
  {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (i j : I)
  {σ : ∀ s, (J ⋙ V).obj s ⟶ (K ⋙ W).obj s}
  {σ' : ∀ s, (K ⋙ W).obj s ⟶ (J ⋙ V).obj s}
  {τ : ∀ s, (J ⋙ U).obj s ⟶ (J ⋙ U).obj s}
  {ρ : ∀ s, (V ⋙ M).obj s ⟶ (U ⋙ L).obj s}
  {ρ' : ∀ s, (U ⋙ L).obj s ⟶ (V ⋙ M).obj s}
  {ξ : ∀ s, (W ⋙ M).obj s ⟶ (W ⋙ M).obj s}
  (hσ : IsSupernatural k (D.parity i * D.parity j) σ)
  (hσ' : IsSupernatural k (D.parity j * D.parity i) σ')
  (hτ : IsSupernatural k (D.parity i * D.parity i) τ)
  (hρ : IsSupernatural k (D.parity j * D.parity i) ρ)
  (hρ' : IsSupernatural k (D.parity i * D.parity j) ρ')
  (hξ : IsSupernatural k (D.parity i * D.parity i) ξ)
local notation "F₀" => (J ⋙ V) ⋙ M
local notation "F₁" => (J ⋙ U) ⋙ L
local notation "F₂" => (K ⋙ W) ⋙ M

/-- The independent paths on all seven grid edges, with the equal crossing negative. -/
def gridMixedBraid (N : Superfunctor k C (SVec k)) :
    End (induced M (induced V (induced J N))) :=
  (show End (induced M (induced V (induced J N))) from
    rectangularCrossComponent U V L M hρ' ((induction J).obj N) ≫
      (-(induction L).map (gridDoubleCrossComponent J U hτ N)) ≫
        rectangularCrossComponent V U M L hρ ((induction J).obj N)) -
  (show End (induced M (induced V (induced J N))) from
    (induction M).map (rectangularCrossComponent K J W V hσ' N) ≫
      (-gridDoubleCrossComponent W M hξ ((induction K).obj N)) ≫
        (induction M).map (rectangularCrossComponent J K V W hσ N))

/-- The direct three-functor source paths for this same grid. -/
def gridDirectMixedBraid (N : Superfunctor k C (SVec k)) : End (induced F₀ N) :=
  (show End (induced F₀ N) from
    transformComponent (hρ'.whiskerLeft J) N ≫
      (-transformComponent (hτ.whiskerRight L) N) ≫ transformComponent (hρ.whiskerLeft J) N) -
  (show End (induced F₀ N) from
    transformComponent (hσ'.whiskerRight M) N ≫
      (-transformComponent (hξ.whiskerLeft K) N) ≫ transformComponent (hσ.whiskerRight M) N)

/-- The six rectangular squares use the three prescribed triple charts. -/
theorem gridMixedBraid_conjugate (N : Superfunctor k C (SVec k)) :
    gridMixedBraid J K U V W L M D i j hσ hσ' hτ hρ hρ' hξ N =
      inductionEndConjugation (k := k) (inductionTripleFlattening J V M N)
        (gridDirectMixedBraid J K U V W L M D i j hσ hσ' hτ hρ hρ' hξ N) := by
  let e := inductionTripleFlattening J V M N
  let eR := inductionTripleFlattening J U L N
  let eL := inductionTripleFlattening K W M N
  have hR := grid_three_squares e.hom eR.hom eR.hom e.hom
    (rectangularCrossComponent U V L M hρ' ((induction J).obj N))
    (-(induction L).map (gridDoubleCrossComponent J U hτ N))
    (rectangularCrossComponent V U M L hρ ((induction J).obj N))
    (transformComponent (hρ'.whiskerLeft J) N) (-transformComponent (hτ.whiskerRight L) N)
    (transformComponent (hρ.whiskerLeft J) N)
    (inductionTripleFlattening_suffix_rectangular J V M U L hρ' N)
    (grid_negative_square _ _ _ (inductionTripleFlattening_prefix_rectangular J U J U L hτ N))
    (inductionTripleFlattening_suffix_rectangular J U L V M hρ N)
  have hL := grid_three_squares e.hom eL.hom eL.hom e.hom
    ((induction M).map (rectangularCrossComponent K J W V hσ' N))
    (-gridDoubleCrossComponent W M hξ ((induction K).obj N))
    ((induction M).map (rectangularCrossComponent J K V W hσ N))
    (transformComponent (hσ'.whiskerRight M) N) (-transformComponent (hξ.whiskerLeft K) N)
    (transformComponent (hσ.whiskerRight M) N)
    (inductionTripleFlattening_prefix_rectangular J V K W M hσ' N)
    (grid_negative_square _ _ _ (inductionTripleFlattening_suffix_rectangular K W M W M hξ N))
    (inductionTripleFlattening_prefix_rectangular K W J V M hσ N)
  have hrow : gridMixedBraid J K U V W L M D i j hσ hσ' hτ hρ hρ' hξ N ≫ e.hom =
      e.hom ≫ gridDirectMixedBraid J K U V W L M D i j hσ hσ' hτ hρ hρ' hξ N :=
    grid_difference_square _ _ _ _ _ hR hL
  exact (inductionEndConjugation_of_square e _ _ hrow).symm

variable {α : ∀ s, End (J.obj s)} {β : ∀ s, End (V.obj s)} {γ : ∀ s, End (M.obj s)}
  (hα : IsSupernatural k (D.parity i) α) (hβ : IsSupernatural k (D.parity j) β)
  (hγ : IsSupernatural k (D.parity i) γ)

/-- The whole grid correction, with the literal source equation exposed at this generic intermediate. -/
theorem gridMixedBraid_polynomial (hij : i ≠ j)
    (hsource : ∀ s,
      (show End ((F₀).obj s) from M.map (σ s) ≫ ξ (K.obj s) ≫ M.map (σ' s)) -
      (show End ((F₀).obj s) from ρ (J.obj s) ≫ L.map (τ s) ≫ ρ' (J.obj s)) =
        tripleDotCorrectionPolynomial D (parameterTwist D Sc) (R := End ((F₀).obj s)) i j
          (γ ((J ⋙ V).obj s)) (M.map (β (J.obj s))) (M.map (V.map (α s))))
    (N : Superfunctor k C (SVec k)) :
    gridMixedBraid J K U V W L M D i j hσ hσ' hτ hρ hρ' hξ N =
      tripleDotCorrectionPolynomial D Sc (R := End (induced M (induced V (induced J N)))) i j
        ((induction M).map ((induction V).map (dotEnd J hα N)))
        ((induction M).map (dotEnd V hβ ((induction J).obj N)))
        (dotEnd M hγ ((induction V).obj ((induction J).obj N))) := by
  have hd := transformComponent_corrected_braid F₀ F₁ F₂ D Sc i j
    ((hα.whiskerRight V).whiskerRight M) ((hβ.whiskerLeft J).whiskerRight M)
    (hγ.whiskerLeft (J ⋙ V))
    (hσ.whiskerRight M) (hξ.whiskerLeft K) (hσ'.whiskerRight M)
    (hρ.whiskerLeft J) (hτ.whiskerRight L) (hρ'.whiskerLeft J) hsource hij N
  have hp := transformComponent_triplePolynomial F₀ D Sc i j
    ((hα.whiskerRight V).whiskerRight M) ((hβ.whiskerLeft J).whiskerRight M)
    (hγ.whiskerLeft (J ⋙ V)) hij N
  have ht := inductionTripleFlattening_polynomial D Sc i j J V M hα hβ hγ hij N
  rw [gridMixedBraid_conjugate]
  change inductionEndConjugation (k := k) (inductionTripleFlattening J V M N) _ = _
  rw [show gridDirectMixedBraid J K U V W L M D i j hσ hσ' hτ hρ hρ' hξ N = _ from hd, hp]
  exact ht.symm

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end
