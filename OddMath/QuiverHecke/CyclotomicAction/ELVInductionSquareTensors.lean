import OddMath.QuiverHecke.CyclotomicAction.ELVInductionUnitTensors
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendQuotientTensors
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedAppendParity

/-! # Tensor generators under a commuting induction square

The comparison in DeformedActionAssembly §§5–6 and STATUS critical-chain
item 2 factors through
composition of induction, the literal append/quotient square, and induction
of the quotient counit. This calculation keeps the intermediate modules
abstract until all four maps have been evaluated.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u

/-- Total composition as a linear-map equality, with the endpoint
instances fixed while the supermodules are abstract. -/
theorem composition_total_linear
    {k : Type u} [CommRing k] {C : Type u} [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {F G H : Superfunctor k C (SVec k)} (f : F ⟶ G) (g : G ⟶ H) (w : C) :
    (f ≫ g).total w = g.total w ∘ₗ f.total w :=
  Superfunctor.comp_total f g w

/-- Equality of module maps gives equality of their total linear maps
without introducing a new concrete endpoint presentation. -/
theorem total_linear_congr
    {k : Type u} [CommRing k] {C : Type u} [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {F G : Superfunctor k C (SVec k)} {f g : F ⟶ G} (h : f = g) (w : C) :
    f.total w = g.total w := congrArg (fun a : F ⟶ G => a.total w) h

section FunctorEquality
variable {k : Type u} [CommRing k]
  {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  (J K : C ⥤ D) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  [K.Additive] [K.Linear k] [IsSuperfunctor k K] (h : J = K)
  (R : Superfunctor k C (SVec k))

private theorem functorEq_hom_app :
    (inductionFunctorIsoOfEq J K h).hom.app R = (inducedIsoOfFunctorEq J K h R).hom := by
  subst K
  rfl

private theorem functorEq_total_tensor (v : C) (w : D)
    (g : J.obj v ⟶ w) (b : R.obj v) :
    ((inductionFunctorIsoOfEq J K h).hom.app R).total w
      (tensor J R.toFunctor v g b) =
      tensor K R.toFunctor v
        (eqToHom (congrArg (fun F : C ⥤ D => F.obj v) h).symm ≫ g) b := by
  subst K
  simp only [inductionFunctorIsoOfEq, Iso.refl_hom, NatTrans.id_app,
    SuperNatTrans.total, Superfunctor.id_app_zero, Superfunctor.id_app_one,
    add_zero, eqToHom_refl, Category.id_comp]
  rfl
end FunctorEquality

variable {k : Type u} [CommRing k]
  {C A B D : Type u} [Category.{u} C] [Category.{u} A]
  [Category.{u} B] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  [Preadditive B] [Linear k B] [Supercategory k B]
  [Preadditive D] [Linear k D] [Supercategory k D]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (U : A ⥤ D) [U.Additive] [U.Linear k] [IsSuperfunctor k U]
  (Q : C ⥤ B) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
  (T : B ⥤ D) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
  (h : J ⋙ U = Q ⋙ T)
  (R : Superfunctor k C (SVec k)) (M : Superfunctor k B (SVec k))
  (c : (induction Q).obj R ⟶ M)

/-- The four comparison maps after induction along the quotient. -/
def squareComparison : (induction J ⋙ induction U).obj R ⟶ (induction T).obj M :=
  (inductionComp J U).hom.app R ≫
    (inductionFunctorIsoOfEq (J ⋙ U) (Q ⋙ T) h).hom.app R ≫
      (inductionComp Q T).inv.app R ≫ (induction T).map c

/-- The functor-level square comparison has precisely the component
equality map used in the selected append comparisons. -/
theorem squareComparison_eq :
    squareComparison J U Q T h R M c =
      (inductionComp J U).hom.app R ≫
        (inducedIsoOfFunctorEq (J ⋙ U) (Q ⋙ T) h R).hom ≫
          (inductionComp Q T).inv.app R ≫ (induction T).map c := by
  exact congrArg (fun z : (induction (J ⋙ U)).obj R ⟶ (induction (Q ⋙ T)).obj R =>
    (inductionComp J U).hom.app R ≫ z ≫ (inductionComp Q T).inv.app R ≫
      (induction T).map c) (functorEq_hom_app (J ⋙ U) (Q ⋙ T) h R)

/-- On a generator the four-map comparison changes only the arrow through
the commuting square and applies the chosen input map to its unit tensor.
The evenness premise concerns that input map, not arbitrary module vectors
or category arrows. -/
theorem squareComparison_total_tensor
    (hc : c ∈ parity (R := k) _ _ 0)
    (s : C) (w : A) (g : J.obj s ⟶ w) (b : R.obj s) :
    (squareComparison J U Q T h R M c).total (U.obj w)
      (tensor U ((induction J).obj R).toFunctor w (𝟙 (U.obj w))
        (tensor J R.toFunctor s g b)) =
      tensor T M.toFunctor (Q.obj s)
        (eqToHom (congrArg (fun F : C ⥤ D => F.obj s) h).symm ≫ U.map g)
        (c.app 0 (Q.obj s) (unit Q R.toFunctor s b)) := by
  let a := (inductionComp J U).hom.app R
  let e := (inductionFunctorIsoOfEq (J ⋙ U) (Q ⋙ T) h).hom.app R
  let d := (inductionComp Q T).inv.app R
  let f := (induction T).map c
  have ha : a.total (U.obj w)
      (tensor U ((induction J).obj R).toFunctor w (𝟙 (U.obj w))
        (tensor J R.toFunctor s g b)) =
      tensor (J ⋙ U) R.toFunctor s (U.map g) b := by
    have hx := inductionComp_hom_total_tensor J U R s w (U.obj w) (𝟙 _) g b
    set_option backward.dsimp.instances true in
      dsimp only [induction] at hx ⊢
    simpa only [a, Category.comp_id] using hx
  have he : e.total (U.obj w)
      (tensor (J ⋙ U) R.toFunctor s (U.map g) b) =
      tensor (Q ⋙ T) R.toFunctor s
        (eqToHom (congrArg (fun F : C ⥤ D => F.obj s) h).symm ≫ U.map g) b :=
    functorEq_total_tensor (J ⋙ U) (Q ⋙ T) h R s (U.obj w) (U.map g) b
  have hd := inductionComp_inv_total_tensor Q T R s (U.obj w)
    (eqToHom (congrArg (fun F : C ⥤ D => F.obj s) h).symm ≫ U.map g) b
  have hf := moduleMap_total_tensor_even T c hc (U.obj w) (Q.obj s)
    (eqToHom (congrArg (fun F : C ⥤ D => F.obj s) h).symm ≫ U.map g)
    (unit Q R.toFunctor s b)
  set_option backward.dsimp.instances true in
    dsimp only [induction] at hd hf
  unfold squareComparison
  rw [Superfunctor.comp_total, SVec.comp_apply, ha,
    Superfunctor.comp_total, SVec.comp_apply, he,
    Superfunctor.comp_total, SVec.comp_apply]
  exact (congrArg (f.total (U.obj w)) hd).trans hf

/-- The same canonical comparison on the literal underlying coends.
Exposing these carriers before specializing the square keeps the
induction superspace projections out of subsequent generator formulas. -/
def squareLinear (w : D) :
    Obj U (induced J R).toFunctor w →ₗ[k] Obj T M.toFunctor w :=
  (squareComparison J U Q T h R M c).total w

/-- Generator formula on literal coends, normalized while the four
functors and their module endpoints are still abstract. -/
theorem squareLinear_tensor
    (hc : c ∈ parity (R := k) _ _ 0)
    (s : C) (w : A) (g : J.obj s ⟶ w) (b : R.obj s) :
    squareLinear J U Q T h R M c (U.obj w)
      (tensor U (induced J R).toFunctor w (𝟙 (U.obj w))
        (tensor J R.toFunctor s g b)) =
      tensor T M.toFunctor (Q.obj s)
        (eqToHom (congrArg (fun F : C ⥤ D => F.obj s) h).symm ≫ U.map g)
        (c.app 0 (Q.obj s) (unit Q R.toFunctor s b)) := by
  have hs := squareComparison_total_tensor J U Q T h R M c hc s w g b
  set_option backward.dsimp.instances true in
    dsimp only [squareLinear, induction] at hs ⊢
  exact hs

end OddMath.QuiverHecke.ELVOld.BalancedInduction
