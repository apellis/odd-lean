import OddMath.QuiverHecke.CyclotomicAction.ELVInductionPairPolynomial
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridDots
import OddMath.QuiverHecke.CyclotomicAction.ELVEndEvaluation

/-! # Original-parameter quadratic polynomials through the chosen induction chart

DeformedActionAssembly §6 (9): the polynomial of the two independent
induction dots equals the signed source polynomial transported through
the prescribed composition isomorphism, as whole module endomorphisms.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
private theorem transform_total {k C E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    {F G : C ⥤ E} [F.Additive] [F.Linear k] [IsSuperfunctor k F]
    [G.Additive] [G.Linear k] [IsSuperfunctor k G]
    {p : ZMod 2} {a : ∀ s, F.obj s ⟶ G.obj s}
    (ha : IsSupernatural k p a) (N : Superfunctor k C (SVec k)) (w : E) :
    (transformComponent ha N).total w = transformLinear ha N w := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp only [SuperNatTrans.total, transformComponent_app, ite_true, ite_false,
      zero_ne_one, one_ne_zero, add_zero, zero_add]

variable {k C E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (F : C ⥤ E) [F.Additive] [F.Linear k] [IsSuperfunctor k F]

/-- Pointwise equal source arrows have equal whole balanced induction maps. -/
theorem transformComponent_congr_pointwise {p : ZMod 2}
    {a b : ∀ s, F.obj s ⟶ F.obj s} (ha : IsSupernatural k p a) (hb : IsSupernatural k p b)
    (h : ∀ s, a s = b s) (N : Superfunctor k C (SVec k)) :
    transformComponent ha N = transformComponent hb N := by
  apply OddMath.FiniteSupermodule.hom_ext_total
  intro w
  rw [transform_total, transform_total]
  apply hom_ext
  intro s g n
  rw [transformLinear_tensor, transformLinear_tensor, h s]

variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (i j : I) {a b : ∀ s, End (F.obj s)}
  (ha : IsSupernatural k (D.parity i) a) (hb : IsSupernatural k (D.parity j) b)

/-- The original-parameter polynomial is an equality of whole module morphisms. -/
theorem transformComponent_pairPolynomial (hij : i ≠ j)
    (hQ : IsSupernatural k 0 (fun s => elvSignedPairQuadEval D Sc (R := End (F.obj s)) i j (a s) (b s)))
    (N : Superfunctor k C (SVec k)) :
    transformComponent hQ N = orderedPairOperatorPolynomial (R := End (induced F N)) D Sc i j
      (transformComponent ha N) (transformComponent hb N) := by
  apply OddMath.FiniteSupermodule.hom_ext_total
  intro w
  let ev : End (induced F N) →ₐ[k] Module.End k ((induced F N).obj w) :=
    (svecEndEvaluation ((induced F N).obj w)).comp (supernaturalEndEvaluation (induced F N) w)
  change (transformComponent hQ N).total w =
    ev (orderedPairOperatorPolynomial (R := End (induced F N)) D Sc i j (transformComponent ha N) (transformComponent hb N))
  rw [orderedPairOperatorPolynomial_map_hom]
  change (transformComponent hQ N).total w = orderedPairOperatorPolynomial (R := Module.End k ((induced F N).obj w)) D Sc i j
    ((transformComponent ha N).total w) ((transformComponent hb N).total w)
  rw [transform_total, transform_total, transform_total]
  exact transformLinear_pairPolynomial F D Sc i j ha hb hij hQ N w

section Conjugation
variable {V : Type*} [Category V] [Preadditive V] [Linear k V]
/-- The exact chosen chart transports the endomorphism algebra without reversing products. -/
def inductionEndConjugation {x y : V} (e : x ≅ y) : End y →ₐ[k] End x :=
  AlgHom.ofLinearMap
    { toFun := fun f => e.hom ≫ f ≫ e.inv
      map_add' := by
        intro f g
        change y ⟶ y at f g
        change e.hom ≫ (f + g) ≫ e.inv = (e.hom ≫ f ≫ e.inv) + (e.hom ≫ g ≫ e.inv)
        simp only [Preadditive.comp_add, Preadditive.add_comp]
      map_smul' := by
        intro r f
        change y ⟶ y at f
        change e.hom ≫ (r • f) ≫ e.inv = r • (e.hom ≫ f ≫ e.inv)
        simp only [Linear.comp_smul, Linear.smul_comp] }
    (by
      change e.hom ≫ (𝟙 y) ≫ e.inv = 𝟙 x
      simp only [Category.id_comp, Iso.hom_inv_id])
    (fun f g => by
      change e.hom ≫ (g ≫ f) ≫ e.inv = (e.hom ≫ g ≫ e.inv) ≫ (e.hom ≫ f ≫ e.inv)
      simp only [Category.assoc, Iso.inv_hom_id_assoc])

@[simp] theorem inductionEndConjugation_apply {x y : V} (e : x ≅ y) (f : End y) :
    inductionEndConjugation (k := k) e f = e.hom ≫ f ≫ e.inv := rfl

/-- A commuting dot square fixes the corresponding conjugated endomorphism. -/
theorem inductionEndConjugation_of_square {x y : V} (e : x ≅ y) (a : End x) (b : End y)
    (h : a ≫ e.hom = e.hom ≫ b) : inductionEndConjugation (k := k) e b = a := by
  change e.hom ≫ b ≫ e.inv = a
  have he := congrArg (fun f => f ≫ e.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using he.symm
end Conjugation

section Pair
variable {A : Type u}
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ E) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  {α : ∀ s, End (J.obj s)} {β : ∀ s, End (K.obj s)}
  (hα : IsSupernatural k (D.parity i) α) (hβ : IsSupernatural k (D.parity j) β)

/-- The chosen inner and outer induction dots give the original polynomial under flattening. -/
theorem inductionComp_pairPolynomial (hij : i ≠ j)
    (hQ : IsSupernatural k 0 (fun s => elvSignedPairQuadEval D Sc
      (R := End ((J ⋙ K).obj s)) i j (K.map (α s)) (β (J.obj s))))
    (N : Superfunctor k C (SVec k)) :
    (inductionComp J K).hom.app N ≫ transformComponent hQ N ≫ (inductionComp J K).inv.app N =
      orderedPairOperatorPolynomial (R := End (induced K (induced J N))) D Sc i j
        ((induction K).map (dotEnd J hα N)) (dotEnd K hβ ((induction J).obj N)) := by
  let e : induced K (induced J N) ≅ induced (J ⋙ K) N := (inductionComp J K).app N
  have h := transformComponent_pairPolynomial (J ⋙ K) D Sc i j
    (hα.whiskerRight K) (hβ.whiskerLeft J) hij hQ N
  have hc := congrArg (fun z : End (induced (J ⋙ K) N) => inductionEndConjugation (k := k) e z) h
  rw [orderedPairOperatorPolynomial_map_hom] at hc
  have h₁ : inductionEndConjugation (k := k) e (transformComponent (hα.whiskerRight K) N) =
      (induction K).map (dotEnd J hα N) :=
    inductionEndConjugation_of_square e _ _ (inductionComp_inner_dot J K hα N)
  have h₂ : inductionEndConjugation (k := k) e (transformComponent (hβ.whiskerLeft J) N) =
      dotEnd K hβ ((induction J).obj N) :=
    inductionEndConjugation_of_square e _ _ (inductionComp_outer_dot J K hβ N)
  rw [h₁, h₂, inductionEndConjugation_apply] at hc
  exact hc
end Pair
end OddMath.QuiverHecke.ELVOld.BalancedInduction
