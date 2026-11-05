/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVRouquierData

/-! # Evaluating polynomial endomorphisms of the weight action

DeformedActionAssembly §6 (9): total evaluation preserves the ordered
endomorphism algebra. This transports the component quadratic polynomial
to the native two-morphism relation without commuting odd operators.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {k : Type u} [CommRing k]
    {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]

/-- Total evaluation is linear on arbitrary supernatural maps. -/
def supernaturalTotalLinearMap (F G : Superfunctor k C B) (M : C) :
    (F ⟶ G) →ₗ[k] (F.obj M ⟶ G.obj M) where
  toFun f := f.total M
  map_add' f g := by
    change (f.app 0 M + g.app 0 M) + (f.app 1 M + g.app 1 M) =
      (f.app 0 M + f.app 1 M) + (g.app 0 M + g.app 1 M)
    abel
  map_smul' r f := by
    change r • f.app 0 M + r • f.app 1 M = r • (f.app 0 M + f.app 1 M)
    exact (smul_add _ _ _).symm

/-- Total evaluation respects the ordered endomorphism algebra. -/
def supernaturalEndEvaluation (F : Superfunctor k C B) (M : C) :
    End F →ₐ[k] End (F.obj M) :=
  AlgHom.ofLinearMap (supernaturalTotalLinearMap F F M)
    (by change (𝟙 F : F ⟶ F).total M = 𝟙 (F.obj M); simp [SuperNatTrans.total])
    (fun f g => Superfunctor.comp_total g f M)
/-- Project a family endomorphism to one of its categories. -/
def piEndEvaluation {J : Type*} {A : J → Type*} [∀ j, Category (A j)]
    [∀ j, Preadditive (A j)] [∀ j, Linear k (A j)] (V : ∀ j, A j) (j : J) :
    End V →ₐ[k] End (V j) :=
  AlgHom.ofLinearMap
    { toFun := fun f => f j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    rfl (fun _ _ => rfl)

/-- Endomorphisms of a super vector space act as ordinary linear operators,
with the same multiplication order. -/
def svecEndEvaluation (V : SVec k) : End V →ₐ[k] Module.End k V :=
  AlgHom.ofLinearMap
    { toFun := fun f => f
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    rfl (fun _ _ => rfl)
/-- Evaluate an endomorphism of a family of module-valued functors all the
way to its linear operator. -/
def moduleFamilyEndEvaluation {J : Type u} {A : J → Type u}
    [∀ j, Category.{u} (A j)] [∀ j, Preadditive (A j)]
    [∀ j, Linear k (A j)] [∀ j, Supercategory k (A j)]
    (F : Superfunctor k C (∀ j, Superfunctor k (A j) (SVec k)))
    (M : C) (j : J) (w : A j) :
    End F →ₐ[k] Module.End k ((F.obj M j).obj w) :=
  (((svecEndEvaluation ((F.obj M j).obj w)).comp
      (supernaturalEndEvaluation (F.obj M j) w)).comp
      (piEndEvaluation (F.obj M) j)).comp
      (supernaturalEndEvaluation F M)

theorem moduleFamilyEndEvaluation_ext {J : Type u} {A : J → Type u}
    [∀ j, Category.{u} (A j)] [∀ j, Preadditive (A j)]
    [∀ j, Linear k (A j)] [∀ j, Supercategory k (A j)]
    (F : Superfunctor k C (∀ j, Superfunctor k (A j) (SVec k)))
    (f g : End F) (h : ∀ M j w,
      moduleFamilyEndEvaluation F M j w f = moduleFamilyEndEvaluation F M j w g) : f = g := by
  apply supernatural_hom_ext_total
  intro M
  funext j
  apply FiniteSupermodule.hom_ext_total
  intro w
  exact h M j w

/-- Ordered operator polynomials commute with algebra homomorphisms;
this does not require the component evaluation to be invertible. -/
theorem orderedPairOperatorPolynomial_map_hom
    {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
    {R S : Type*} [Ring R] [Algebra k R] [Ring S] [Algebra k S]
    (e : R →ₐ[k] S) (i j : I) (A B : R) :
    e (orderedPairOperatorPolynomial D Sc i j A B) =
      orderedPairOperatorPolynomial D Sc i j (e A) (e B) := by
  unfold orderedPairOperatorPolynomial
  split_ifs <;> simp only [map_smul, map_one, map_add, map_sum, map_mul, map_pow]
/-- Componentwise ordered quadratics give the equation of natural maps. -/
theorem moduleFamily_polynomial_of_components
    {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
    {J : Type u} {A : J → Type u}
    [∀ j, Category.{u} (A j)] [∀ j, Preadditive (A j)]
    [∀ j, Linear k (A j)] [∀ j, Supercategory k (A j)]
    {F G : Superfunctor k C (∀ j, Superfunctor k (A j) (SVec k))}
    (c : F ⟶ G) (d : G ⟶ F) (a b : End F) (i j : I)
    (h : ∀ M t w, ((d.total M t).total w).comp ((c.total M t).total w) =
      orderedPairOperatorPolynomial (R := Module.End k ((F.obj M t).obj w)) D Sc i j ((a.total M t).total w) ((b.total M t).total w)) :
    c ≫ d = orderedPairOperatorPolynomial (R := End F) D Sc i j a b := by
  apply moduleFamilyEndEvaluation_ext
  intro M t w
  rw [orderedPairOperatorPolynomial_map_hom]
  change ((c ≫ d).total M t).total w =
    orderedPairOperatorPolynomial (R := Module.End k ((F.obj M t).obj w)) D Sc i j ((a.total M t).total w) ((b.total M t).total w)
  rw [Superfunctor.comp_total]
  change ((c.total M t) ≫ (d.total M t)).total w = _
  rw [Superfunctor.comp_total]
  exact h M t w
end OddMath.QuiverHecke.ELVOld
