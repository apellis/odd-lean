import OddMath.QuiverHecke.CyclotomicAction.ModuleInduction
import OddMath.QuiverHecke.CyclotomicAction.ContentModules
import OddMath.QuiverHecke.CyclotomicAction.ContentModule
import OddMath.QuiverHecke.CyclotomicAction.CyclotomicQuotientTop
import OddMath.QuiverHecke.CyclotomicAction.KernelDegree
import Mathlib.CategoryTheory.EqToHom

/-!
# Induction grid mate

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

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
end

end

section

/-! # Canonical parity transport of induction and its actual counit

The source comparison is the image of the actual vector parity isomorphism
under restriction and balanced induction. Its tensor formula twists the
kernel arrow, including all coefficient parity. Counit naturality proves
the whole module-map comparison independently of any representative basis.
This supplies the categorical transport used in DeformedMatrixComparison
(3), (5); the concrete shifted old-Hom source must still be identified with
the corresponding restricted representable module.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  (A : C ⥤ D) [A.Additive] [A.Linear k] [IsSuperfunctor k A]

/-- Canonical whole-module source transport, built from actual parity and
the existing restriction/induction functors. -/
def adjunctionParitySourceIso (N : Superfunctor k D (SVec k)) :
    (induction A).obj ((restriction A).obj N) ≅
      (induction A).obj ((restriction A).obj (supermoduleParityObj N)) :=
  ((restriction A ⋙ induction A).mapIso (supermoduleParityIso N)).symm

/-- The actual counit at the parity-shifted module, transported on source
and output by the canonical isomorphisms, equals the original actual counit.
This is a whole supernatural module-map equality, including odd inputs. -/
theorem adjunctionParitySourceIso_counit
    (N : Superfunctor k D (SVec k)) :
    (adjunctionParitySourceIso A N).hom ≫
      (adjunctionCounit A).app (supermoduleParityObj N) ≫
        (supermoduleParityIso N).hom =
      (adjunctionCounit A).app N := by
  have hn := (adjunctionCounit A).naturality (supermoduleParityIso N).hom
  simp only [Functor.id_map] at hn
  change (restriction A ⋙ induction A).map (supermoduleParityIso N).inv ≫
      ((adjunctionCounit A).app (supermoduleParityObj N) ≫
        (supermoduleParityIso N).hom) = (adjunctionCounit A).app N
  rw [← hn, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

end OddMath.QuiverHecke.ELVOld.BalancedInduction
end

end

section

/-! # The prescribed coefficient module and actual parity restriction

The odd shifted Hom coefficient functor is compared with the actual parity
shift of the restriction of the old representable. The comparison is the
identity on underlying quotient coefficients. Its projections and action
agree independently, retaining total exterior parity.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem oldCategory_twist (v w : OldCategory D Sc cutoff)
    (p : ZMod 2) (f : v ⟶ w) :
    twist k p f = oldTwist D Sc cutoff p v.word w.word f := by
  obtain ⟨a, rfl⟩ := (ideal D Sc cutoff v.word w.word).mkQ_surjective f
  rw [twist_apply, oldCategory_proj, oldCategory_proj]
  change (ideal D Sc cutoff v.word w.word).mkQ (proj k 0 a) +
    sign k p • (ideal D Sc cutoff v.word w.word).mkQ (proj k 1 a) =
      (ideal D Sc cutoff v.word w.word).mkQ (twist k p a)
  rw [twist_apply, map_add, map_smul]

namespace CyclotomicCrossingTensor

def parityRestrictedRepresentable (i : I) (v : List I) :
    Superfunctor k (OldCategory D Sc cutoff) (SVec k) :=
  (BalancedInduction.restriction (append D Sc cutoff i)).obj
    (supermoduleParityObj (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))

theorem coefficientOne_obj_proj (i : I) (v : List I) (s : OldCategory D Sc cutoff)
    (q : ZMod 2) :
    ((coefficient D Sc cutoff 1 i v).obj s).proj q =
      ((parityRestrictedRepresentable D Sc cutoff i v).obj s).proj q := by
  change (shiftedHom D Sc cutoff 1 v (s.word ++ [i])).proj q =
    (SVec.piObj (Supercategory.homSVec k (OldCategory D Sc cutoff)
      (⟨v⟩ : OldCategory D Sc cutoff) ((append D Sc cutoff i).obj s))).proj q
  rw [SVec.piObj_proj, Supercategory.homSVec_proj]
  have hcat : (Supercategory.proj k (q + 1) :
      ((⟨v⟩ : OldCategory D Sc cutoff) ⟶ (append D Sc cutoff i).obj s) →ₗ[k]
        ((⟨v⟩ : OldCategory D Sc cutoff) ⟶ (append D Sc cutoff i).obj s)) =
      oldProj D Sc cutoff v (s.word ++ [i]) (q + 1) :=
    LinearMap.ext (oldCategory_proj D Sc cutoff ⟨v⟩ ((append D Sc cutoff i).obj s) (q + 1))
  refine Eq.trans ?_ hcat.symm
  rcases parity_eq_zero_or_one q with rfl | rfl
  · apply LinearMap.ext
    intro b
    change Old D Sc cutoff v (s.word ++ [i]) at b
    change b - oldProj D Sc cutoff v (s.word ++ [i]) (1 + 1) b =
      oldProj D Sc cutoff v (s.word ++ [i]) (0 + 1) b
    rw [SVec.zmod2_one_add_one, zero_add]
    obtain ⟨a, rfl⟩ := (ideal D Sc cutoff v (s.word ++ [i])).mkQ_surjective b
    rw [oldProj_mk, oldProj_mk]
    have h := congrArg (ideal D Sc cutoff v (s.word ++ [i])).mkQ (proj_add_proj (R := k) a)
    rw [map_add] at h
    exact (eq_sub_of_add_eq ((add_comm _ _).trans h)).symm
  · rfl

theorem coefficientOne_map (i : I) (v : List I) {s t : OldCategory D Sc cutoff}
    (f : s ⟶ t) (b : Old D Sc cutoff v (s.word ++ [i])) :
    (coefficient D Sc cutoff 1 i v).map f b =
      (parityRestrictedRepresentable D Sc cutoff i v).map f b := by
  change (oldRepresentableFunctor D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)).map
      ((append D Sc cutoff i).map (oldTwist D Sc cutoff 1 s.word t.word f)) b =
    (twist k 1 ((oldRepresentableFunctor D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)).map
      ((append D Sc cutoff i).map f))) b
  rw [← oldCategory_twist D Sc cutoff s t 1 f,
    Supercategory.map_twist, Supercategory.map_twist]

/-- The comparison is defined on the actual functors and is identity on every
underlying old quotient coefficient. -/
def coefficientParityIso (i : I) (v : List I) :
    coefficient D Sc cutoff 1 i v ≅
      (parityRestrictedRepresentable D Sc cutoff i v).toFunctor :=
  NatIso.ofComponents (fun s =>
    { hom := LinearMap.id
      inv := LinearMap.id
      hom_inv_id := by ext b; rfl
      inv_hom_id := by ext b; rfl }) (by
        intro s t f
        apply LinearMap.ext
        intro b
        change (coefficient D Sc cutoff 1 i v).map f b =
          (parityRestrictedRepresentable D Sc cutoff i v).map f b
        exact coefficientOne_map D Sc cutoff i v f b)

/-- Objectwise identity is even for the independently defined gradings. -/
theorem coefficientParityIso_hom_mem (i : I) (v : List I) (s : OldCategory D Sc cutoff) :
    (coefficientParityIso D Sc cutoff i v).hom.app s ∈
      parity (R := k) ((coefficient D Sc cutoff 1 i v).obj s)
        ((parityRestrictedRepresentable D Sc cutoff i v).obj s) 0 := by
  intro q
  change LinearMap.id ∘ₗ ((coefficient D Sc cutoff 1 i v).obj s).proj q =
    ((parityRestrictedRepresentable D Sc cutoff i v).obj s).proj (q + 0) ∘ₗ LinearMap.id
  rw [add_zero, LinearMap.id_comp, LinearMap.comp_id]
  exact coefficientOne_obj_proj D Sc cutoff i v s q

end CyclotomicCrossingTensor
end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Actual shifted coefficient supermodule and canonical source transport

The prescribed coefficient(1) functor is packaged as its actual supermodule,
using its independently proved action/projection comparison. The resulting
even module isomorphism is mapped through actual induction. Composition with
the canonical parity source isomorphism gives whole coend transport and
an equality with the actual adjunction counit.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem coefficientOne_obj_part (i : I) (v : List I) (s : OldCategory D Sc cutoff)
    (q : ZMod 2) :
    ((coefficient D Sc cutoff 1 i v).obj s).part q =
      ((parityRestrictedRepresentable D Sc cutoff i v).obj s).part q := by
  ext b
  rw [SVec.mem_part_iff, SVec.mem_part_iff, coefficientOne_obj_proj]
  rfl

instance coefficientOne_additive (i : I) (v : List I) :
    (coefficient D Sc cutoff 1 i v).Additive where
  map_add {s t} f g := by
    apply LinearMap.ext
    intro b
    change (coefficient D Sc cutoff 1 i v).map (f + g) b =
      (coefficient D Sc cutoff 1 i v).map f b + (coefficient D Sc cutoff 1 i v).map g b
    rw [coefficientOne_map, coefficientOne_map, coefficientOne_map]
    exact congrArg (fun h => h b)
      ((parityRestrictedRepresentable D Sc cutoff i v).toFunctor.map_add (f := f) (g := g))

instance coefficientOne_linear (i : I) (v : List I) :
    (coefficient D Sc cutoff 1 i v).Linear k where
  map_smul {s t} f r := by
    apply LinearMap.ext
    intro b
    change (coefficient D Sc cutoff 1 i v).map (r • f) b =
      r • (coefficient D Sc cutoff 1 i v).map f b
    rw [coefficientOne_map, coefficientOne_map]
    exact congrArg (fun h => h b)
      ((parityRestrictedRepresentable D Sc cutoff i v).toFunctor.map_smul r f)

instance coefficientOne_super (i : I) (v : List I) :
    IsSuperfunctor k (coefficient D Sc cutoff 1 i v) where
  map_mem := by
    intro s t p f hf
    apply SVec.mem_parityHom_of_apply_mem
    intro q b hb
    change b ∈ ((coefficient D Sc cutoff 1 i v).obj s).part q at hb
    rw [coefficientOne_obj_part] at hb
    change (coefficient D Sc cutoff 1 i v).map f b ∈
      ((coefficient D Sc cutoff 1 i v).obj t).part (q + p)
    rw [coefficientOne_obj_part, coefficientOne_map]
    exact SVec.apply_mem_part
      (map_mem (parityRestrictedRepresentable D Sc cutoff i v).toFunctor hf) hb

def coefficientOneModule (i : I) (v : List I) :
    Superfunctor k (OldCategory D Sc cutoff) (SVec k) :=
  ⟨coefficient D Sc cutoff 1 i v⟩

def coefficientModuleForward (i : I) (v : List I) :
    coefficientOneModule D Sc cutoff i v ⟶ parityRestrictedRepresentable D Sc cutoff i v :=
  Superfunctor.homMk (IsSupernatural.toSuperNatTrans (p := 0)
    (x := fun s => (coefficientParityIso D Sc cutoff i v).hom.app s) {
      mem := coefficientParityIso_hom_mem D Sc cutoff i v
      naturality := by
        intro s t q f hf
        simp only [zero_mul, Supercategory.sign_zero, one_smul]
        exact (coefficientParityIso D Sc cutoff i v).hom.naturality f })

def coefficientModuleBackward (i : I) (v : List I) :
    parityRestrictedRepresentable D Sc cutoff i v ⟶ coefficientOneModule D Sc cutoff i v :=
  Superfunctor.homMk (IsSupernatural.toSuperNatTrans (p := 0)
    (x := fun s => (coefficientParityIso D Sc cutoff i v).inv.app s) {
      mem := by
        intro s q
        change LinearMap.id ∘ₗ
            ((parityRestrictedRepresentable D Sc cutoff i v).obj s).proj q =
          ((coefficient D Sc cutoff 1 i v).obj s).proj (q + 0) ∘ₗ LinearMap.id
        rw [add_zero, LinearMap.id_comp, LinearMap.comp_id]
        exact (coefficientOne_obj_proj D Sc cutoff i v s q).symm
      naturality := by
        intro s t q f hf
        simp only [zero_mul, Supercategory.sign_zero, one_smul]
        exact (coefficientParityIso D Sc cutoff i v).inv.naturality f })

@[simp] theorem coefficientModuleForward_app (i : I) (v : List I)
    (p : ZMod 2) (s : OldCategory D Sc cutoff) :
    (coefficientModuleForward D Sc cutoff i v).app p s =
      if p = 0 then LinearMap.id else 0 := rfl

@[simp] theorem coefficientModuleBackward_app (i : I) (v : List I)
    (p : ZMod 2) (s : OldCategory D Sc cutoff) :
    (coefficientModuleBackward D Sc cutoff i v).app p s =
      if p = 0 then LinearMap.id else 0 := rfl

def coefficientParityModuleIso (i : I) (v : List I) :
    coefficientOneModule D Sc cutoff i v ≅ parityRestrictedRepresentable D Sc cutoff i v where
  hom := coefficientModuleForward D Sc cutoff i v
  inv := coefficientModuleBackward D Sc cutoff i v
  hom_inv_id := by
    apply Superfunctor.hom_ext
    intro p s
    rcases parity_eq_zero_or_one p with rfl | rfl <;>
      simp only [Superfunctor.comp_app, coefficientModuleForward_app,
        coefficientModuleBackward_app, Superfunctor.id_app_zero, Superfunctor.id_app_one,
        ↓reduceIte, zero_add, one_ne_zero, SVec.zmod2_one_add_one]
    all_goals
      ext b
      simp <;> rfl
  inv_hom_id := by
    apply Superfunctor.hom_ext
    intro p s
    rcases parity_eq_zero_or_one p with rfl | rfl <;>
      simp only [Superfunctor.comp_app, coefficientModuleForward_app,
        coefficientModuleBackward_app, Superfunctor.id_app_zero, Superfunctor.id_app_one,
        ↓reduceIte, zero_add, one_ne_zero, SVec.zmod2_one_add_one]
    all_goals
      ext b
      simp <;> rfl

/-- The prescribed moving-parity coefficient is packaged before taking its coend. -/
instance movingCoefficient_additive (j : {j : I // D.parity j = 1}) (v : List I) :
    (coefficient D Sc cutoff (D.parity j.1) j.1 v).Additive := by
  simpa only [j.property] using coefficientOne_additive D Sc cutoff j.1 v

instance movingCoefficient_linear (j : {j : I // D.parity j = 1}) (v : List I) :
    (coefficient D Sc cutoff (D.parity j.1) j.1 v).Linear k := by
  simpa only [j.property] using coefficientOne_linear D Sc cutoff j.1 v

instance movingCoefficient_super (j : {j : I // D.parity j = 1}) (v : List I) :
    IsSuperfunctor k (coefficient D Sc cutoff (D.parity j.1) j.1 v) := by
  simpa only [j.property] using coefficientOne_super D Sc cutoff j.1 v

def movingCoefficientModule (j : {j : I // D.parity j = 1}) (v : List I) :
    Superfunctor k (OldCategory D Sc cutoff) (SVec k) :=
  ⟨coefficient D Sc cutoff (D.parity j.1) j.1 v⟩

def movingCoefficientForward (j : {j : I // D.parity j = 1}) (v : List I) :
    movingCoefficientModule D Sc cutoff j v ⟶ coefficientOneModule D Sc cutoff j.1 v :=
  Superfunctor.homMk (IsSupernatural.toSuperNatTrans (p := 0)
    (x := fun _ => LinearMap.id) {
      mem := by
        intro s q
        change LinearMap.id ∘ₗ
            ((coefficient D Sc cutoff (D.parity j.1) j.1 v).obj s).proj q =
          ((coefficient D Sc cutoff 1 j.1 v).obj s).proj (q + 0) ∘ₗ LinearMap.id
        rw [add_zero, LinearMap.id_comp, LinearMap.comp_id, j.property]
      naturality := by
        intro s t q f hf
        simp only [zero_mul, Supercategory.sign_zero, one_smul]
        change LinearMap.id ∘ₗ (coefficient D Sc cutoff (D.parity j.1) j.1 v).map f =
          (coefficient D Sc cutoff 1 j.1 v).map f ∘ₗ LinearMap.id
        rw [LinearMap.id_comp, LinearMap.comp_id, j.property] })

def movingCoefficientBackward (j : {j : I // D.parity j = 1}) (v : List I) :
    coefficientOneModule D Sc cutoff j.1 v ⟶ movingCoefficientModule D Sc cutoff j v :=
  Superfunctor.homMk (IsSupernatural.toSuperNatTrans (p := 0)
    (x := fun _ => LinearMap.id) {
      mem := by
        intro s q
        change LinearMap.id ∘ₗ ((coefficient D Sc cutoff 1 j.1 v).obj s).proj q =
          ((coefficient D Sc cutoff (D.parity j.1) j.1 v).obj s).proj (q + 0) ∘ₗ LinearMap.id
        rw [add_zero, LinearMap.id_comp, LinearMap.comp_id, j.property]
      naturality := by
        intro s t q f hf
        simp only [zero_mul, Supercategory.sign_zero, one_smul]
        change LinearMap.id ∘ₗ (coefficient D Sc cutoff 1 j.1 v).map f =
          (coefficient D Sc cutoff (D.parity j.1) j.1 v).map f ∘ₗ LinearMap.id
        rw [LinearMap.id_comp, LinearMap.comp_id, j.property] })

@[simp] theorem movingCoefficientForward_app (j : {j : I // D.parity j = 1})
    (v : List I) (q : ZMod 2) (s : OldCategory D Sc cutoff) :
    (movingCoefficientForward D Sc cutoff j v).app q s =
      if q = 0 then LinearMap.id else 0 := rfl

@[simp] theorem movingCoefficientBackward_app (j : {j : I // D.parity j = 1})
    (v : List I) (q : ZMod 2) (s : OldCategory D Sc cutoff) :
    (movingCoefficientBackward D Sc cutoff j v).app q s =
      if q = 0 then LinearMap.id else 0 := rfl

/-- The coefficient comparison is pointwise identity; it is formed before induction. -/
def movingCoefficientIso (j : {j : I // D.parity j = 1}) (v : List I) :
    movingCoefficientModule D Sc cutoff j v ≅ coefficientOneModule D Sc cutoff j.1 v where
  hom := movingCoefficientForward D Sc cutoff j v
  inv := movingCoefficientBackward D Sc cutoff j v
  hom_inv_id := by
    apply Superfunctor.hom_ext
    intro q s
    rcases parity_eq_zero_or_one q with rfl | rfl <;>
      simp only [Superfunctor.comp_app, movingCoefficientForward_app,
        movingCoefficientBackward_app, Superfunctor.id_app_zero, Superfunctor.id_app_one,
        ↓reduceIte, zero_add, one_ne_zero, SVec.zmod2_one_add_one]
    all_goals
      ext b
      simp <;> rfl
  inv_hom_id := by
    apply Superfunctor.hom_ext
    intro q s
    rcases parity_eq_zero_or_one q with rfl | rfl <;>
      simp only [Superfunctor.comp_app, movingCoefficientForward_app,
        movingCoefficientBackward_app, Superfunctor.id_app_zero, Superfunctor.id_app_one,
        ↓reduceIte, zero_add, one_ne_zero, SVec.zmod2_one_add_one]
    all_goals
      ext b
      simp <;> rfl

/-- The actual induction of the moving coefficient has literally the prescribed
source carrier. The comparison is induced from the pointwise coefficient iso;
no equality recursor transports a coend. -/
def coefficientOneSourceEquiv (j : {j : I // D.parity j = 1}) (v t : List I) :
    BalancedInduction.Obj (append D Sc cutoff j.1)
      (coefficient D Sc cutoff 1 j.1 v) (⟨t⟩ : OldCategory D Sc cutoff) ≃ₗ[k]
      Source D Sc cutoff j.1 v t :=
  moduleIsoLinearEquiv
    (((BalancedInduction.induction (append D Sc cutoff j.1)).mapIso
      (movingCoefficientIso D Sc cutoff j v)).symm)
    (⟨t⟩ : OldCategory D Sc cutoff)

/-- Canonical actual module transport into induction of the prescribed
coefficient(1), whose underlying coend is the independently defined source. -/
def shiftedSourceParityIso (i : I) (v : List I) :
    (BalancedInduction.induction (append D Sc cutoff i)).obj
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))) ≅
    (BalancedInduction.induction (append D Sc cutoff i)).obj (coefficientOneModule D Sc cutoff i v) :=
  BalancedInduction.adjunctionParitySourceIso (append D Sc cutoff i)
    (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) ≪≫
      ((BalancedInduction.induction (append D Sc cutoff i)).mapIso
        (coefficientParityModuleIso D Sc cutoff i v)).symm

/-- Actual counit at the parity-shifted representable, expressed on the
prescribed coefficient module and with the canonical output parity map. -/
def shiftedSourceCounit (i : I) (v : List I) :
    (BalancedInduction.induction (append D Sc cutoff i)).obj
      (coefficientOneModule D Sc cutoff i v) ⟶
      oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff) :=
  ((BalancedInduction.induction (append D Sc cutoff i)).mapIso
      (coefficientParityModuleIso D Sc cutoff i v)).hom ≫
    (BalancedInduction.adjunctionCounit (append D Sc cutoff i)).app
      (supermoduleParityObj (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))) ≫
    (supermoduleParityIso (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).hom

theorem shiftedSourceParityIso_counit (i : I) (v : List I) :
    (shiftedSourceParityIso D Sc cutoff i v).hom ≫ shiftedSourceCounit D Sc cutoff i v =
      (BalancedInduction.adjunctionCounit (append D Sc cutoff i)).app
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) := by
  change ((BalancedInduction.adjunctionParitySourceIso (append D Sc cutoff i)
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).hom ≫
    ((BalancedInduction.induction (append D Sc cutoff i)).mapIso
      (coefficientParityModuleIso D Sc cutoff i v)).inv) ≫
    (((BalancedInduction.induction (append D Sc cutoff i)).mapIso
      (coefficientParityModuleIso D Sc cutoff i v)).hom ≫
      ((BalancedInduction.adjunctionCounit (append D Sc cutoff i)).app
        (supermoduleParityObj (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))) ≫
        (supermoduleParityIso (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))).hom)) = _
  rw [Category.assoc, Iso.inv_hom_id_assoc]
  exact BalancedInduction.adjunctionParitySourceIso_counit (append D Sc cutoff i)
    (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
end

end

section

/-! # Whiskering and balanced induction composition

The composition comparison intertwines independently defined inner and outer
supernatural transformations on arbitrary modules. This supplies the whiskering
comparison needed by the content E-action in `DeformedActionAssembly.md`.
The outer kernel twist in inner whiskering and the supernaturality twist in
outer whiskering are retained. No content reassociation is assumed.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
universe u
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
variable {k : Type u} [CommRing k]
variable {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  [Preadditive E] [Linear k E] [Supercategory k E]
variable (J : C ⥤ D) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
variable (K : D ⥤ E) [K.Additive] [K.Linear k] [IsSuperfunctor k K]

/-- The even component is already the entire flattening map. -/
abbrev compForward (M : Superfunctor k C (SVec k)) (z : E) :
    Obj K (induced J M).toFunctor z →ₗ[k] Obj (J ⋙ K) M.toFunctor z :=
  ((inductionComp J K).hom.app M).app 0 z

theorem compForward_tensor (M : Superfunctor k C (SVec k))
    (v : C) (w : D) (z : E) (g : K.obj w ⟶ z)
    (h : J.obj v ⟶ w) (m : M.obj v) :
    compForward J K M z
      (tensor K (induced J M).toFunctor w g (tensor J M.toFunctor v h m)) =
      tensor (J ⋙ K) M.toFunctor v (K.map h ≫ g) m :=
  inductionComp_hom_tensor J K M v w z g h m

variable {J}
variable {J' : C ⥤ D} [J'.Additive] [J'.Linear k] [IsSuperfunctor k J']

/-- Inner source transformation: induction by K must twist the OUTER kernel g too. -/
theorem compForward_transform_inner_tensor {p : ZMod 2}
    {α : ∀ v, J.obj v ⟶ J'.obj v} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k))
    (v : C) (w : D) (z : E) (g : K.obj w ⟶ z)
    (h : J'.obj v ⟶ w) (m : M.obj v) :
    compForward J K M z
      (mapComponent K (transformComponent hα M) p z
        (tensor K (induced J' M).toFunctor w g (tensor J' M.toFunctor v h m))) =
    transformLinear (hα.whiskerRight K) M z
      (compForward J' K M z
        (tensor K (induced J' M).toFunctor w g (tensor J' M.toFunctor v h m))) := by
  rw [mapComponent_tensor K (transformComponent hα M) p z w g
    (tensor J' M.toFunctor v h m)]
  simp only [transformComponent_apply, ↓reduceIte]
  simp only [transformLinear_tensor, compForward_tensor, Functor.map_comp,
    map_twist, twist_comp, Category.assoc]
  rfl

variable (J)
variable {K}
variable {K' : D ⥤ E}
  [K'.Additive] [K'.Linear k] [IsSuperfunctor k K']

/-- Outer source transformation: the missing inner twist comes from supernaturality. -/
theorem compForward_transform_outer_tensor {p : ZMod 2}
    {β : ∀ w, K.obj w ⟶ K'.obj w} (hβ : IsSupernatural k p β)
    (M : Superfunctor k C (SVec k))
    (v : C) (w : D) (z : E) (g : K'.obj w ⟶ z)
    (h : J.obj v ⟶ w) (m : M.obj v) :
    compForward J K M z
      (transformLinear hβ (induced J M) z
        (tensor K' (induced J M).toFunctor w g (tensor J M.toFunctor v h m))) =
    transformLinear (hβ.whiskerLeft J) M z
      (compForward J K' M z
        (tensor K' (induced J M).toFunctor w g (tensor J M.toFunctor v h m))) := by
  rw [transformLinear_tensor hβ (induced J M) z w g (tensor J M.toFunctor v h m),
    compForward_tensor, compForward_tensor, transformLinear_tensor]
  change tensor (J ⋙ K) M.toFunctor v
      (K.map h ≫ (β w ≫ twist k p g)) m =
    tensor (J ⋙ K) M.toFunctor v
      (β (J.obj v) ≫ twist k p (K'.map h ≫ g)) m
  rw [twist_comp, ← map_twist K', ← Category.assoc,
    hβ.naturality_twist h, Category.assoc]

/- Extension to the all-vector linear-map statements uses hom_ext twice, not Fubini.
   The inner variable after the first hom_ext is itself a quotient vector; curry it
   using inclusion ∘ₗ TensorProduct.mk. This helper spells out that step.
-/
variable (K)
omit [Supercategory k E] [K.Additive] [K.Linear k] [IsSuperfunctor k K] in
theorem nested_hom_ext (M : Superfunctor k C (SVec k)) (z : E)
    {V : Type u} [AddCommGroup V] [Module k V]
    {a b : Obj K (induced J M).toFunctor z →ₗ[k] V}
    (hab : ∀ (v : C) (w : D) (g : K.obj w ⟶ z)
      (h : J.obj v ⟶ w) (m : M.obj v),
      a (tensor K (induced J M).toFunctor w g (tensor J M.toFunctor v h m)) =
      b (tensor K (induced J M).toFunctor w g (tensor J M.toFunctor v h m))) : a = b := by
  apply hom_ext
  intro w g x
  let t : Obj J M.toFunctor w →ₗ[k] Obj K (induced J M).toFunctor z :=
    inclusion K (induced J M).toFunctor z w ∘ₗ
      TensorProduct.mk k (K.obj w ⟶ z) ((induced J M).obj w) g
  have ht : a ∘ₗ t = b ∘ₗ t := by
    apply hom_ext
    intro v h m
    exact hab v w g h m
  exact congrArg (fun f => f x) ht

variable {J}
theorem compForward_transform_inner {p : ZMod 2}
    {α : ∀ v, J.obj v ⟶ J'.obj v} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k)) (z : E) :
    compForward J K M z ∘ₗ mapComponent K (transformComponent hα M) p z =
      transformLinear (hα.whiskerRight K) M z ∘ₗ compForward J' K M z := by
  apply nested_hom_ext J' K M z
  intro v w g h m
  exact compForward_transform_inner_tensor K hα M v w z g h m

variable (J) {K}
theorem compForward_transform_outer {p : ZMod 2}
    {β : ∀ w, K.obj w ⟶ K'.obj w} (hβ : IsSupernatural k p β)
    (M : Superfunctor k C (SVec k)) (z : E) :
    compForward J K M z ∘ₗ transformLinear hβ (induced J M) z =
      transformLinear (hβ.whiskerLeft J) M z ∘ₗ compForward J K' M z := by
  apply nested_hom_ext J K' M z
  intro v w g h m
  exact compForward_transform_outer_tensor J hβ M v w z g h m

end OddMath.QuiverHecke.ELVOld.BalancedInduction
end

end

section

/-! # Homogeneous transformations on iterated induction

The equal-colour crossing in DeformedMatrixComparison (2), (4) is obtained
from its literal two-letter transformation using the chosen induction
flattening. The tensor formula below keeps its parity twist on the complete
composite coefficient arrow.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C A B : Type u} [Category.{u} C] [Category.{u} A] [Category.{u} B]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  {p : ZMod 2} {α : ∀ v, (J ⋙ K).obj v ⟶ (J ⋙ K).obj v}
  (hα : IsSupernatural k p α) (M : Superfunctor k C (SVec k))

private def flattenLinear (w : B) :
    Obj K (induced J M).toFunctor w →ₗ[k] Obj (J ⋙ K) M.toFunctor w :=
  ((inductionComp J K).hom.app M).total w

private def unflattenLinear (w : B) :
    Obj (J ⋙ K) M.toFunctor w →ₗ[k] Obj K (induced J M).toFunctor w :=
  ((inductionComp J K).inv.app M).total w

private theorem flattenLinear_tensor (s : C) (v : A) (w : B)
    (a : J.obj s ⟶ v) (g : K.obj v ⟶ w) (b : M.obj s) :
    flattenLinear J K M w
      (tensor K (induced J M).toFunctor v g (tensor J M.toFunctor s a b)) =
    tensor (J ⋙ K) M.toFunctor s (K.map a ≫ g) b := by
  have h := inductionComp_hom_total_tensor J K M s v w g a b
  set_option backward.dsimp.instances true in
    dsimp only [flattenLinear, induction] at h ⊢
  exact h

private theorem unflattenLinear_tensor (s : C) (w : B)
    (g : K.obj (J.obj s) ⟶ w) (b : M.obj s) :
    unflattenLinear J K M w (tensor (J ⋙ K) M.toFunctor s g b) =
      tensor K (induced J M).toFunctor (J.obj s) g
        (tensor J M.toFunctor s (𝟙 _) b) := by
  have h := inductionComp_inv_total_tensor J K M s w g b
  set_option backward.dsimp.instances true in
    dsimp only [unflattenLinear, induction] at h ⊢
  exact h

/-- The homogeneous two-letter transform, conjugated by the selected
induction-composition isomorphism on the literal iterated coends. -/
def doubleTransformLinear (w : B) :
    Obj K (induced J M).toFunctor w →ₗ[k] Obj K (induced J M).toFunctor w :=
  unflattenLinear J K M w ∘ₗ transformLinear hα M w ∘ₗ flattenLinear J K M w

/-- The inverse flattening inserts a unit in the first induction; the
transformation twists the entire old composite coefficient, in its order. -/
theorem doubleTransformLinear_tensor (s : C) (v : A) (w : B)
    (a : J.obj s ⟶ v) (g : K.obj v ⟶ w) (b : M.obj s) :
    doubleTransformLinear J K hα M w
      (tensor K (induced J M).toFunctor v g (tensor J M.toFunctor s a b)) =
      tensor K (induced J M).toFunctor (J.obj s)
        (α s ≫ twist k p (K.map a ≫ g)) (tensor J M.toFunctor s (𝟙 _) b) := by
  rw [doubleTransformLinear, LinearMap.comp_apply, LinearMap.comp_apply,
    flattenLinear_tensor, transformLinear_tensor, unflattenLinear_tensor]

private theorem transformComponent_total (w : B) :
    (transformComponent hα M).total w = transformLinear hα M w := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp only [SuperNatTrans.total, transformComponent_app,
      ite_true, ite_false, zero_ne_one, one_ne_zero, add_zero, zero_add]

/-- This literal coend operator is the total map of the given homogeneous
module transformation conjugated by the two selected flattenings. -/
theorem doubleTransformLinear_eq_total (w : B)
    (b : Obj K (induced J M).toFunctor w) :
    doubleTransformLinear J K hα M w b =
      (((inductionComp J K).hom.app M ≫ transformComponent hα M ≫
        (inductionComp J K).inv.app M).total w) b := by
  rw [Superfunctor.comp_total, SVec.comp_apply, Superfunctor.comp_total,
    SVec.comp_apply, transformComponent_total]
  unfold doubleTransformLinear
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  unfold flattenLinear unflattenLinear
  rfl

end OddMath.QuiverHecke.ELVOld.BalancedInduction
end

end

section

/-! # The ordered crossing mate between changing content categories

The first crossing-derived entry of DeformedMatrixComparison (2), (4)
uses the unit for the upper append adjunction, the prescribed signed
crossing, and induction of the lower append counit. Keeping the three
categories distinct gives the mate needed by the scalar and fixed-content
matrix charts in DeformedActionAssembly §§5–6.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C A B : Type u} [Category.{u} C] [Category.{u} A] [Category.{u} B]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  {p : ZMod 2} {α : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
  (hα : IsSupernatural k p α)

/-- The given homogeneous crossing conjugated by both chosen flattenings. -/
def gridDoubleCrossComponent (M : Superfunctor k C (SVec k)) :
    (induction J ⋙ induction K).obj M ⟶ (induction J ⋙ induction K).obj M :=
  (inductionComp J K).hom.app M ≫ transformComponent hα M ≫
    (inductionComp J K).inv.app M

private theorem gridDoubleCrossComponent_total_tensor
    (M : Superfunctor k C (SVec k)) (s : C) (v : A) (w : B)
    (a : J.obj s ⟶ v) (g : K.obj v ⟶ w) (b : M.obj s) :
    (((inductionComp J K).hom.app M ≫ transformComponent hα M ≫
      (inductionComp J K).inv.app M).total w)
      (tensor K (induced J M).toFunctor v g (tensor J M.toFunctor s a b)) =
      tensor K (induced J M).toFunctor (J.obj s)
        (α s ≫ twist k p (K.map a ≫ g)) (tensor J M.toFunctor s (𝟙 _) b) :=
  (doubleTransformLinear_eq_total J K hα M w
    (tensor K (induced J M).toFunctor v g (tensor J M.toFunctor s a b))).symm.trans
      (doubleTransformLinear_tensor J K hα M s v w a g b)

private def gridModuleUnit (M : Superfunctor k A (SVec k)) :
    M ⟶ (restriction K).obj (induced K M) := (adjunctionUnit K).app M

private def gridModuleCounit (N : Superfunctor k A (SVec k)) :
    induced J ((restriction J).obj N) ⟶ N := (adjunctionCounit J).app N

private def gridInducedCounit (N : Superfunctor k A (SVec k)) :
    induced K (induced J ((restriction J).obj N)) ⟶ induced K N :=
  (induction K).map (gridModuleCounit J N)

private theorem gridUnit_total_apply (M : Superfunctor k A (SVec k)) (t : A) (b : M.obj t) :
    (gridModuleUnit K M).total t b = unit K M.toFunctor t b := by
  simp only [gridModuleUnit, adjunctionUnit, Superfunctor.homMk, SuperNatTrans.total,
    unitTransform_app, ↓reduceIte, one_ne_zero, add_zero]
  rfl

private theorem gridCounit_total_tensor (N : Superfunctor k A (SVec k))
    (s : C) (t : A) (g : J.obj s ⟶ t) (b : N.obj (J.obj s)) :
    (gridModuleCounit J N).total t
      (tensor J ((restriction J).obj N).toFunctor s g b) = N.map g b := by
  simp only [gridModuleCounit, adjunctionCounit, Superfunctor.homMk, SuperNatTrans.total,
    counitTransform_app, ↓reduceIte, one_ne_zero, add_zero]
  exact counit_tensor J N.toFunctor t s g b

private theorem gridRestriction_total_apply
    {M N : Superfunctor k B (SVec k)} (f : M ⟶ N) (t : A) (b : M.obj (K.obj t)) :
    ((restriction K).map f).total t b = f.total (K.obj t) b := rfl

private theorem gridNeg_total_apply
    {M N : Superfunctor k B (SVec k)} (f : M ⟶ N) (t : B) (b : M.obj t) :
    (-f).total t b = -(f.total t b) := by
  change -(f.app 0 t b) + -(f.app 1 t b) = -(f.app 0 t b + f.app 1 t b)
  exact (neg_add _ _).symm

private theorem gridInduction_map_even_tensor
    {M N : Superfunctor k A (SVec k)} (f : M ⟶ N)
    (hf : f ∈ parity (R := k) M N 0)
    (s : A) (t : B) (g : K.obj s ⟶ t) (b : M.obj s) :
    ((induction K).map f).total t (tensor K M.toFunctor s g b) =
      tensor K N.toFunctor s g (f.total s b) := by
  have h1 := Superfunctor.app_eq_zero_of_mem hf (show (1 : ZMod 2) ≠ 0 by decide)
  change (moduleMap K f).total t _ = _
  rw [moduleMap_total_tensor, h1]
  simp only [SuperNatTrans.total, h1, add_zero]
  change tensor K N.toFunctor s g (f.app 0 s b) +
    tensor K N.toFunctor s (twist k 1 g) 0 = _
  rw [tensor_zero_right, add_zero]

/-- The ordinary-adjunction mate, with the upper append unit, prescribed
signed crossing, and induced lower append counit in their given order. -/
def orderedGridMateComponent (N : Superfunctor k A (SVec k)) :
    induced J ((restriction J).obj N) ⟶ (restriction K).obj (induced K N) :=
  gridModuleUnit K (induced J ((restriction J).obj N)) ≫
    (restriction K).map (-gridDoubleCrossComponent J K hα ((restriction J).obj N)) ≫
    (restriction K).map (gridInducedCounit J K N)

private theorem orderedGridMateComponent_total (N : Superfunctor k A (SVec k))
    (t : A) (x : (induced J ((restriction J).obj N)).obj t) :
    (orderedGridMateComponent J K hα N).total t x =
      (gridInducedCounit J K N).total (K.obj t)
        ((-gridDoubleCrossComponent J K hα ((restriction J).obj N)).total (K.obj t)
          (unit K (induced J ((restriction J).obj N)).toFunctor t x)) := by
  rw [orderedGridMateComponent, Superfunctor.comp_total, Superfunctor.comp_total]
  simp only [SVec.comp_apply]
  rw [gridUnit_total_apply, gridRestriction_total_apply, gridRestriction_total_apply]
  rfl

/-- The mate retains the extra minus and twists the complete appended
coefficient arrow. No homogeneity condition is imposed on that arrow. -/
theorem orderedGridMateComponent_total_tensor (N : Superfunctor k A (SVec k))
    (s : C) (t : A) (g : J.obj s ⟶ t) (b : N.obj (J.obj s)) :
    (orderedGridMateComponent J K hα N).total t
      (tensor J ((restriction J).obj N).toFunctor s g b) =
      -tensor K N.toFunctor (J.obj s) (α s ≫ twist k p (K.map g)) b := by
  rw [orderedGridMateComponent_total, unit_apply, gridNeg_total_apply]
  unfold gridDoubleCrossComponent
  rw [gridDoubleCrossComponent_total_tensor, map_neg]
  have he := gridInduction_map_even_tensor K
    (M := induced J ((restriction J).obj N)) (N := N)
    (gridModuleCounit J N) (adjunctionCounit_mem J N)
    (J.obj s) (K.obj t) (α s ≫ twist k p (K.map g ≫ 𝟙 _))
    (tensor J ((restriction J).obj N).toFunctor s (𝟙 _) b)
  have hc := gridCounit_total_tensor J N s (J.obj s) (𝟙 _) b
  have hi : N.map (𝟙 (J.obj s)) b = b := by
    change (N.toFunctor.map (𝟙 (J.obj s))) b = b
    rw [N.toFunctor.map_id]
    rfl
  have hr := congrArg (fun x : N.obj (J.obj s) =>
    tensor K N.toFunctor (J.obj s) (α s ≫ twist k p (K.map g ≫ 𝟙 _)) x) (hc.trans hi)
  have hn := congrArg Neg.neg (he.trans hr)
  simp only [Category.comp_id] at hn
  simp only [Category.comp_id]
  exact hn

end OddMath.QuiverHecke.ELVOld.BalancedInduction
end

end

section

/-! # Literal coend values of the chosen changing-content crossing mate

The scalar and fixed-content comparisons of the prescribed first matrix
entry in DeformedMatrixComparison (2), (4) need the same given mate on raw
coends. These formulas expose its carriers before substituting concrete
append functors and put the extra minus into the coefficient arrow.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C A B : Type u} [Category.{u} C] [Category.{u} A] [Category.{u} B]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]

/-- The literal coend map of the chosen unit, signed crossing and counit. -/
def orderedGridMateLinear
    {p : ZMod 2} {α : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
    (hα : IsSupernatural k p α) (N : Superfunctor k A (SVec k)) (t : A) :
    Obj J ((restriction J).obj N).toFunctor t →ₗ[k] Obj K N.toFunctor (K.obj t) :=
  (orderedGridMateComponent J K hα N).total t

/-- The extra minus belongs to the complete crossed coefficient; neither
coefficient arrow nor module vector needs to be homogeneous. -/
theorem orderedGridMateLinear_tensor
    {p : ZMod 2} {α : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
    (hα : IsSupernatural k p α) (N : Superfunctor k A (SVec k))
    (s : C) (t : A) (g : J.obj s ⟶ t) (b : N.obj (J.obj s)) :
    orderedGridMateLinear J K hα N t
      (tensor J ((restriction J).obj N).toFunctor s g b) =
      tensor K N.toFunctor (J.obj s) (-(α s ≫ twist k p (K.map g))) b := by
  have h := orderedGridMateComponent_total_tensor J K hα N s t g b
  have hn : tensor K N.toFunctor (J.obj s) (-(α s ≫ twist k p (K.map g))) b =
      -tensor K N.toFunctor (J.obj s) (α s ≫ twist k p (K.map g)) b := by
    change inclusion K N.toFunctor (K.obj t) (J.obj s)
        ((-(α s ≫ twist k p (K.map g))) ⊗ₜ[k] b) =
      -inclusion K N.toFunctor (K.obj t) (J.obj s)
        ((α s ≫ twist k p (K.map g)) ⊗ₜ[k] b)
    rw [TensorProduct.neg_tmul, map_neg]
  set_option backward.dsimp.instances true in
    dsimp only [orderedGridMateLinear, induction] at h ⊢
  exact h.trans hn.symm

end OddMath.QuiverHecke.ELVOld.BalancedInduction
end

end

section

/-! # Generator formula for a canonically transported induction transformation

The existing induction-composition isomorphism conjugates a homogeneous
transformation of a double functor. Its action on nested balanced tensors
retains the ordered composite and the full parity twist. The comparison
is exactly the existing canonical `inductionComp`, in both directions.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k C : Type u} [CommRing k] [Category.{u} C]
  [Preadditive C] [Linear k C] [Supercategory k C]
variable (A : C ⥤ C) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
variable {p : ZMod 2} {α : ∀ s, (A ⋙ A).obj s ⟶ (A ⋙ A).obj s}
  (hα : IsSupernatural k p α)

private theorem transform_total (M : Superfunctor k C (SVec k))
    (w : C) :
    (BalancedInduction.transformComponent (hα) M).total w =
      BalancedInduction.transformLinear (hα) M w := by
  rcases parity_eq_zero_or_one p with h | h
  · simp only [SuperNatTrans.total, BalancedInduction.transformComponent_app, h,
      ↓reduceIte, one_ne_zero, add_zero]
  · simp only [SuperNatTrans.total, BalancedInduction.transformComponent_app, h,
      ↓reduceIte, zero_ne_one, zero_add]

private def flatten (M : Superfunctor k C (SVec k)) :
    BalancedInduction.induced A
      (BalancedInduction.induced A M) ⟶
    BalancedInduction.induced (A ⋙ A) M :=
  (BalancedInduction.inductionComp (k := k) A
    A).hom.app M

private def unflatten (M : Superfunctor k C (SVec k)) :
    BalancedInduction.induced (A ⋙ A) M ⟶
    BalancedInduction.induced A
      (BalancedInduction.induced A M) :=
  (BalancedInduction.inductionComp (k := k) A
    A).inv.app M

private theorem flatten_tensor (M : Superfunctor k C (SVec k))
    (s w t : C) (g : A.obj w ⟶ t) (h : A.obj s ⟶ w) (b : M.obj s) :
    (flatten A M).total t
      (tensor A (induced A M).toFunctor w g (tensor A M.toFunctor s h b)) =
    tensor (A ⋙ A) M.toFunctor s (A.map h ≫ g) b :=
  inductionComp_hom_total_tensor A A M s w t g h b

private theorem unflatten_tensor (M : Superfunctor k C (SVec k))
    (s t : C) (g : (A ⋙ A).obj s ⟶ t) (b : M.obj s) :
    (unflatten A M).total t (tensor (A ⋙ A) M.toFunctor s g b) =
    tensor A (induced A M).toFunctor (A.obj s) g (tensor A M.toFunctor s (𝟙 _) b) :=
  inductionComp_inv_total_tensor A A M s t g b

def doubleCrossComponent (M : Superfunctor k C (SVec k)) :
    End (BalancedInduction.induced A
      (BalancedInduction.induced A M)) :=
  flatten A M ≫
    BalancedInduction.transformComponent (hα) M ≫
      unflatten A M

private theorem doubleCrossComponent_total (M : Superfunctor k C (SVec k))
    (t : C) (x : Obj A (induced A M).toFunctor t) :
    (doubleCrossComponent A hα M).total t x =
      (unflatten A M).total t
        ((transformComponent hα M).total t ((flatten A M).total t x)) := by
  rw [doubleCrossComponent, Superfunctor.comp_total, Superfunctor.comp_total]
  rfl

theorem doubleCrossComponent_total_tensor (M : Superfunctor k C (SVec k))
    (s w t : C)
    (g : A.obj w ⟶ t)
    (h : A.obj s ⟶ w) (b : M.obj s) :
    (doubleCrossComponent A hα M).total t
      (BalancedInduction.tensor A
        (BalancedInduction.induced A M).toFunctor w g
          (BalancedInduction.tensor A M.toFunctor s h b)) =
    BalancedInduction.tensor A
      (BalancedInduction.induced A M).toFunctor
      (A.obj s)
      (α s ≫
        twist k p (A.map h ≫ g))
      (BalancedInduction.tensor A M.toFunctor s (𝟙 _) b) := by
  rw [doubleCrossComponent_total, flatten_tensor]
  have ht := congrArg
    (fun f : Obj (A ⋙ A) M.toFunctor t →ₗ[k] Obj (A ⋙ A) M.toFunctor t =>
      f (tensor (A ⋙ A) M.toFunctor s (A.map h ≫ g) b)) (transform_total A hα M t)
  have he := transformLinear_tensor hα M t s (A.map h ≫ g) b
  have hx := congrArg (fun x : Obj (A ⋙ A) M.toFunctor t =>
    (unflatten A M).total t x) (ht.trans he)
  exact hx.trans (unflatten_tensor A M s t (α s ≫ twist k p (A.map h ≫ g)) b)

end OddMath.QuiverHecke.ELVOld.BalancedInduction
end

end

section

/-! # Tensor evaluation of the ordered induction mate

The cup, canonically transported signed double transformation and cap are
composed in that order. The generator formula keeps the whole parity twist.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k C : Type u} [CommRing k] [Category.{u} C]
  [Preadditive C] [Linear k C] [Supercategory k C]
variable (A : C ⥤ C) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
variable {p : ZMod 2} {α : ∀ s, (A ⋙ A).obj s ⟶ (A ⋙ A).obj s}
  (hα : IsSupernatural k p α)

private def moduleUnit (M : Superfunctor k C (SVec k)) :
    M ⟶ (restriction A).obj (induced A M) := (adjunctionUnit A).app M

private def moduleCounit (N : Superfunctor k C (SVec k)) :
    induced A ((restriction A).obj N) ⟶ N := (adjunctionCounit A).app N

private def inducedCounit (N : Superfunctor k C (SVec k)) :
    induced A (induced A ((restriction A).obj N)) ⟶ induced A N :=
  (induction A).map (moduleCounit A N)

private theorem unit_total_apply_grid (M : Superfunctor k C (SVec k)) (t : C) (b : M.obj t) :
    (moduleUnit A M).total t b = unit A M.toFunctor t b := by
  simp only [moduleUnit, adjunctionUnit, Superfunctor.homMk, SuperNatTrans.total,
    unitTransform_app, ↓reduceIte, one_ne_zero, add_zero]
  rfl

private theorem counit_total_tensor (N : Superfunctor k C (SVec k))
    (s t : C) (g : A.obj s ⟶ t) (b : N.obj (A.obj s)) :
    (moduleCounit A N).total t
      (tensor A ((restriction A).obj N).toFunctor s g b) = N.map g b := by
  simp only [moduleCounit, adjunctionCounit, Superfunctor.homMk, SuperNatTrans.total,
    counitTransform_app, ↓reduceIte, one_ne_zero, add_zero]
  exact counit_tensor A N.toFunctor t s g b

private theorem restriction_map_total_apply
    {M N : Superfunctor k C (SVec k)} (f : M ⟶ N) (t : C) (b : M.obj (A.obj t)) :
    ((restriction A).map f).total t b = f.total (A.obj t) b := rfl

private theorem neg_total_apply
    {P Q : Superfunctor k C (SVec k)} (f : P ⟶ Q) (t : C) (x : P.obj t) :
    (-f).total t x = -(f.total t x) := by
  change -(f.app 0 t x) + -(f.app 1 t x) = -(f.app 0 t x + f.app 1 t x)
  exact (neg_add _ _).symm

private theorem induction_map_even_tensor
    {M N : Superfunctor k C (SVec k)} (f : M ⟶ N)
    (hf : f ∈ parity (R := k) M N 0)
    (s t : C) (g : A.obj s ⟶ t) (b : M.obj s) :
    ((induction A).map f).total t (tensor A M.toFunctor s g b) =
    tensor A N.toFunctor s g (f.total s b) := by
  have h1 := Superfunctor.app_eq_zero_of_mem hf (show (1 : ZMod 2) ≠ 0 by decide)
  change (moduleMap A f).total t _ = _
  rw [moduleMap_total_tensor, h1]
  simp only [SuperNatTrans.total, h1, add_zero]
  change tensor A N.toFunctor s g (f.app 0 s b) +
    tensor A N.toFunctor s (twist k 1 g) 0 = _
  rw [tensor_zero_right, add_zero]

def orderedMateComponent (N : Superfunctor k C (SVec k)) :
    induced A ((restriction A).obj N) ⟶ (restriction A).obj (induced A N) :=
  moduleUnit A (induced A ((restriction A).obj N)) ≫
    (restriction A).map (-doubleCrossComponent A hα ((restriction A).obj N)) ≫
    (restriction A).map (inducedCounit A N)

private theorem orderedMateComponent_total (N : Superfunctor k C (SVec k))
    (t : C) (x : (induced A ((restriction A).obj N)).obj t) :
    (orderedMateComponent A hα N).total t x =
      ((inducedCounit A N).total (A.obj t))
        ((-doubleCrossComponent A hα ((restriction A).obj N)).total (A.obj t)
          (unit A (induced A ((restriction A).obj N)).toFunctor t x)) := by
  rw [orderedMateComponent, Superfunctor.comp_total, Superfunctor.comp_total]
  simp only [SVec.comp_apply]
  rw [unit_total_apply_grid, restriction_map_total_apply, restriction_map_total_apply]

theorem orderedMateComponent_total_tensor (N : Superfunctor k C (SVec k))
    (s t : C) (g : A.obj s ⟶ t) (b : N.obj (A.obj s)) :
    (orderedMateComponent A hα N).total t
      (tensor A ((restriction A).obj N).toFunctor s g b) =
    -tensor A N.toFunctor (A.obj s) (α s ≫ twist k p (A.map g)) b := by
  rw [orderedMateComponent_total, unit_apply, neg_total_apply,
    doubleCrossComponent_total_tensor]
  rw [map_neg]
  have he := induction_map_even_tensor A
    (M := induced A ((restriction A).obj N)) (N := N)
    (moduleCounit A N) (adjunctionCounit_mem A N)
    (A.obj s) (A.obj t) (α s ≫ twist k p (A.map g ≫ 𝟙 _))
    (tensor A ((restriction A).obj N).toFunctor s (𝟙 _) b)
  have hc := counit_total_tensor A N s (A.obj s) (𝟙 _) b
  have hi : N.map (𝟙 (A.obj s)) b = b := by
    change (N.toFunctor.map (𝟙 (A.obj s))) b = b
    rw [N.toFunctor.map_id]
    rfl
  have hr := congrArg (fun x : N.obj (A.obj s) =>
    tensor A N.toFunctor (A.obj s) (α s ≫ twist k p (A.map g ≫ 𝟙 _)) x) (hc.trans hi)
  have hn := congrArg Neg.neg (he.trans hr)
  simp only [Category.comp_id] at hn
  simp only [Category.comp_id]
  exact hn

end OddMath.QuiverHecke.ELVOld.BalancedInduction
end

end

section

/-! # Right append induction of old quotient representables

The existing balanced induction of the old Hom representable is represented
by the appended word. This is the canonical target comparison needed in
DeformedMatrixComparison (4): the mate target is the actual upper old Hom,
rather than an assumed replacement kernel. All full coefficients are retained.
This does not yet transport to the truncated exact-content categories.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (i : I)

namespace OldInductionRepresentable
local notation "J" => CyclotomicCrossingTensor.append D Sc cutoff i
local notation "H" v => oldRepresentableFunctor D Sc cutoff v
variable (v : OldCategory D Sc cutoff)

/-- Composition on an unbalanced tensor summand. -/
def pairing (w : OldCategory D Sc cutoff)
    (z : OldCategory D Sc cutoff) :
    ((J).obj z ⟶ w) ⊗[k] (H v).obj z →ₗ[k] ((J).obj v ⟶ w) :=
  TensorProduct.lift {
    toFun := fun h => {
      toFun := fun g => (J).map g ≫ h
      map_add' := by
        intro g g'
        change v ⟶ z at g g'
        change (J).map (g + g') ≫ h = (J).map g ≫ h + (J).map g' ≫ h
        rw [Functor.map_add, Preadditive.add_comp]
      map_smul' := by
        intro r g
        change v ⟶ z at g
        change (J).map (r • g) ≫ h = r • ((J).map g ≫ h)
        rw [Functor.map_smul, Linear.smul_comp] }
    map_add' := by
      intro h h'
      apply LinearMap.ext
      intro g
      exact Preadditive.comp_add ((J).obj v) ((J).obj z) w ((J).map g) h h'
    map_smul' := by
      intro r h
      apply LinearMap.ext
      intro g
      exact Linear.comp_smul ((J).obj v) ((J).obj z) w ((J).map g) r h }

/-- The forward map on the actual balanced quotient. -/
def forward (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj J (H v) w →ₗ[k] ((J).obj v ⟶ w) :=
  BalancedInduction.lift J (H v) w (pairing D Sc cutoff i v w) (by
    intro z z' f h g
    change v ⟶ z at g
    change (J).map g ≫ ((J).map f ≫ h) = (J).map (g ≫ f) ≫ h
    rw [Functor.map_comp, Category.assoc])

@[simp] theorem forward_tensor (w : OldCategory D Sc cutoff)
    (z : OldCategory D Sc cutoff) (h : (J).obj z ⟶ w) (g : v ⟶ z) :
    forward D Sc cutoff i v w (BalancedInduction.tensor J (H v) z h g) =
      (J).map g ≫ h := by
  exact BalancedInduction.lift_tensor J (H v) w
    (pairing D Sc cutoff i v w) _ z h g

/-- The inverse inserts the identity at the representing source object. -/
def backward (w : OldCategory D Sc cutoff) :
    ((J).obj v ⟶ w) →ₗ[k] BalancedInduction.Obj J (H v) w :=
  BalancedInduction.inclusion J (H v) w v ∘ₗ
    (TensorProduct.mk k ((J).obj v ⟶ w) ((H v).obj v)).flip (𝟙 v)

@[simp] theorem backward_apply (w : OldCategory D Sc cutoff)
    (h : (J).obj v ⟶ w) :
    backward D Sc cutoff i v w h = BalancedInduction.tensor J (H v) v h (𝟙 v) := rfl

theorem forward_backward (w : OldCategory D Sc cutoff) :
    forward D Sc cutoff i v w ∘ₗ backward D Sc cutoff i v w = LinearMap.id := by
  ext h
  simp

theorem backward_forward (w : OldCategory D Sc cutoff) :
    backward D Sc cutoff i v w ∘ₗ forward D Sc cutoff i v w = LinearMap.id := by
  apply BalancedInduction.hom_ext
  intro z h g
  change v ⟶ z at g
  change backward D Sc cutoff i v w
    (forward D Sc cutoff i v w (BalancedInduction.tensor J (H v) z h g)) = _
  rw [forward_tensor, backward_apply]
  have hb := BalancedInduction.balance J (H v) g h (𝟙 v)
  change BalancedInduction.tensor J (H v) v ((J).map g ≫ h) (𝟙 v) =
    BalancedInduction.tensor J (H v) z h (𝟙 v ≫ g) at hb
  dsimp only [LinearMap.id_apply]
  simpa only [Category.id_comp] using hb

/-- Objectwise comparison, with both quotient roundtrips. -/
def equiv (w : OldCategory D Sc cutoff) :
    BalancedInduction.Obj J (H v) w ≃ₗ[k] ((J).obj v ⟶ w) :=
  LinearEquiv.ofLinearMap (forward D Sc cutoff i v w)
    (backward D Sc cutoff i v w) (forward_backward D Sc cutoff i v w)
    (backward_forward D Sc cutoff i v w)

theorem forward_naturality {w z : OldCategory D Sc cutoff}
    (a : w ⟶ z) :
    forward D Sc cutoff i v z ∘ₗ BalancedInduction.postcompose J (H v) a =
      (oldRepresentableFunctor D Sc cutoff ((J).obj v)).map a ∘ₗ
        forward D Sc cutoff i v w := by
  apply BalancedInduction.hom_ext
  intro t h g
  change v ⟶ t at g
  change forward D Sc cutoff i v z
    (BalancedInduction.postcompose J (H v) a (BalancedInduction.tensor J (H v) t h g)) =
      forward D Sc cutoff i v w (BalancedInduction.tensor J (H v) t h g) ≫ a
  calc
    _ = forward D Sc cutoff i v z (BalancedInduction.tensor J (H v) t (h ≫ a) g) :=
      congrArg (forward D Sc cutoff i v z)
        (BalancedInduction.postcompose_tensor J (H v) a t h g)
    _ = _ := by rw [forward_tensor, forward_tensor, Category.assoc]

theorem backward_naturality {w z : OldCategory D Sc cutoff}
    (a : w ⟶ z) :
    backward D Sc cutoff i v z ∘ₗ
      (oldRepresentableFunctor D Sc cutoff ((J).obj v)).map a =
      BalancedInduction.postcompose J (H v) a ∘ₗ backward D Sc cutoff i v w := by
  apply LinearMap.ext
  intro h
  exact (BalancedInduction.postcompose_tensor J (H v) a v h (𝟙 v)).symm

/-- Inserting the even identity preserves total parity. -/
theorem backward_mem (w : OldCategory D Sc cutoff) :
    (backward D Sc cutoff i v w :
      Supercategory.homSVec k (OldCategory D Sc cutoff) ((J).obj v) w ⟶
        BalancedInduction.superspace J (H v) w) ∈ parity (R := k)
      (Supercategory.homSVec k (OldCategory D Sc cutoff) ((J).obj v) w)
      (BalancedInduction.superspace J (H v) w) 0 := by
  change ∀ q, backward D Sc cutoff i v w ∘ₗ
      (Supercategory.homSVec k (OldCategory D Sc cutoff) ((J).obj v) w).proj q =
    (BalancedInduction.superspace J (H v) w).proj (q + 0) ∘ₗ
      backward D Sc cutoff i v w
  intro q
  apply LinearMap.ext
  intro h
  change (J).obj v ⟶ w at h
  change BalancedInduction.tensor J (H v) v
      ((Supercategory.homSVec k (OldCategory D Sc cutoff) ((J).obj v) w).proj q h) (𝟙 v) =
    (BalancedInduction.superspace J (H v) w).proj (q + 0)
      (BalancedInduction.tensor J (H v) v h (𝟙 v))
  rw [add_zero]
  have hp := BalancedInduction.proj_tensor J (H v) w q v h (𝟙 v)
  rw [hp]
  have hid0 : ((H v).obj v).proj 0 (𝟙 v) = 𝟙 v := by
    change 𝟙 v - proj k 1 (𝟙 v) = 𝟙 v
    simp [proj_id]
  have hid1 : ((H v).obj v).proj 1 (𝟙 v) = 0 := by
    change proj k 1 (𝟙 v) = 0
    simp only [proj_id, one_ne_zero, ↓reduceIte]
  rw [hid0, hid1, BalancedInduction.tensor_zero_right, add_zero]
  congr 1
  rcases parity_eq_zero_or_one q with rfl | rfl
  · change h - proj k 1 h = proj k 0 h
    exact eq_sub_iff_add_eq.mpr (proj_add_proj h) |>.symm
  · rfl

/-- The forward quotient map is even, including both odd tensor factors. -/
theorem forward_mem (w : OldCategory D Sc cutoff) :
    (forward D Sc cutoff i v w : BalancedInduction.superspace J (H v) w ⟶
      Supercategory.homSVec k (OldCategory D Sc cutoff) ((J).obj v) w) ∈
      parity (R := k) (BalancedInduction.superspace J (H v) w)
        (Supercategory.homSVec k (OldCategory D Sc cutoff) ((J).obj v) w) 0 := by
  have hb := backward_mem D Sc cutoff i v w
  change ∀ q, _ at hb ⊢
  intro q
  apply LinearMap.ext
  intro x
  apply (equiv D Sc cutoff i v w).symm.injective
  have h := congrArg (fun f => f (forward D Sc cutoff i v w x)) (hb q)
  change backward D Sc cutoff i v w
      ((Supercategory.homSVec k (OldCategory D Sc cutoff) ((J).obj v) w).proj q
        (forward D Sc cutoff i v w x)) =
    (BalancedInduction.superspace J (H v) w).proj (q + 0)
      (backward D Sc cutoff i v w (forward D Sc cutoff i v w x)) at h
  have hr (y) : backward D Sc cutoff i v w (forward D Sc cutoff i v w y) = y :=
    congrArg (fun f => f y) (backward_forward D Sc cutoff i v w)
  change backward D Sc cutoff i v w (forward D Sc cutoff i v w
      ((BalancedInduction.superspace J (H v) w).proj q x)) =
    backward D Sc cutoff i v w
      ((Supercategory.homSVec k (OldCategory D Sc cutoff) ((J).obj v) w).proj (q + 0)
        (forward D Sc cutoff i v w x))
  simpa only [hr, add_zero] using h.symm

/-- The even forward supernatural transformation. -/
def forwardTransform :
    (BalancedInduction.induction J).obj (oldRepresentable D Sc cutoff v) ⟶
      oldRepresentable D Sc cutoff ((J).obj v) :=
  Superfunctor.homMk (IsSupernatural.toSuperNatTrans (p := 0)
    (x := forward D Sc cutoff i v) {
      mem := forward_mem D Sc cutoff i v
      naturality := by
        intro w z q a ha
        simp only [zero_mul, Supercategory.sign_zero, one_smul]
        exact forward_naturality D Sc cutoff i v a })

/-- The even inverse supernatural transformation. -/
def backwardTransform :
    oldRepresentable D Sc cutoff ((J).obj v) ⟶
      (BalancedInduction.induction J).obj (oldRepresentable D Sc cutoff v) :=
  Superfunctor.homMk (IsSupernatural.toSuperNatTrans (p := 0)
    (x := backward D Sc cutoff i v) {
      mem := backward_mem D Sc cutoff i v
      naturality := by
        intro w z q a ha
        simp only [zero_mul, Supercategory.sign_zero, one_smul]
        exact backward_naturality D Sc cutoff i v a })

@[simp] theorem forwardTransform_app (p : ZMod 2)
    (w : OldCategory D Sc cutoff) :
    (forwardTransform D Sc cutoff i v).app p w =
      if p = 0 then forward D Sc cutoff i v w else 0 := rfl

@[simp] theorem backwardTransform_app (p : ZMod 2)
    (w : OldCategory D Sc cutoff) :
    (backwardTransform D Sc cutoff i v).app p w =
      if p = 0 then backward D Sc cutoff i v w else 0 := rfl

/-- Append induction of the covariant old quotient representable is represented by
its appended word. Both maps are even and natural against every target arrow. -/
def iso :
    (BalancedInduction.induction J).obj (oldRepresentable D Sc cutoff v) ≅
      oldRepresentable D Sc cutoff ((J).obj v) where
  hom := forwardTransform D Sc cutoff i v
  inv := backwardTransform D Sc cutoff i v
  hom_inv_id := by
    apply Superfunctor.hom_ext
    intro p w
    rcases parity_eq_zero_or_one p with rfl | rfl <;>
      simp only [Superfunctor.comp_app, forwardTransform_app, backwardTransform_app,
        Superfunctor.id_app_zero, Superfunctor.id_app_one, ↓reduceIte, zero_add, one_ne_zero,
        SVec.zmod2_one_add_one]
    · change backward D Sc cutoff i v w ∘ₗ forward D Sc cutoff i v w +
        (0 : BalancedInduction.Obj J (H v) w →ₗ[k] BalancedInduction.Obj J (H v) w) = LinearMap.id
      rw [add_zero, backward_forward]
    · apply LinearMap.ext
      intro x
      change 0 + backward D Sc cutoff i v w 0 = 0
      rw [map_zero, add_zero]
  inv_hom_id := by
    apply Superfunctor.hom_ext
    intro p w
    rcases parity_eq_zero_or_one p with rfl | rfl <;>
      simp only [Superfunctor.comp_app, forwardTransform_app, backwardTransform_app,
        Superfunctor.id_app_zero, Superfunctor.id_app_one, ↓reduceIte, zero_add, one_ne_zero,
        SVec.zmod2_one_add_one]
    · change forward D Sc cutoff i v w ∘ₗ backward D Sc cutoff i v w +
        (0 : ((J).obj v ⟶ w) →ₗ[k] ((J).obj v ⟶ w)) = LinearMap.id
      rw [add_zero, forward_backward]
    · change (0 : ((J).obj v ⟶ w) →ₗ[k] ((J).obj v ⟶ w)) = 0
      rfl

/-- The actual restriction-induction target is the upper old Hom, canonically. -/
def upperHomEquiv (t : OldCategory D Sc cutoff) :
    ((BalancedInduction.restriction J).obj
      ((BalancedInduction.induction J).obj (oldRepresentable D Sc cutoff v))).obj t ≃ₗ[k]
      ((J).obj v ⟶ (J).obj t) :=
  equiv D Sc cutoff i v ((J).obj t)

theorem upperHomEquiv_tensor (t z : OldCategory D Sc cutoff)
    (h : (J).obj z ⟶ (J).obj t) (g : v ⟶ z) :
    upperHomEquiv D Sc cutoff i v t
      (BalancedInduction.tensor J (H v) z h g) = (J).map g ≫ h :=
  forward_tensor D Sc cutoff i v ((J).obj t) z h g

end OldInductionRepresentable
end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # The Hom kernel of balanced induction
The arbitrary-module tensor step in DeformedMatrixComparison §4 requires
identifying coefficient-kernel tensors with the existing action coends.
This identifies the ordinary-right kernel Hom(J−,w), retaining its literal
balance and the complete input module.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams
namespace OddMath.QuiverHecke.ELVOld.BalancedKernelTensor
universe u
variable {k : Type u} [CommRing k]
  {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive D] [Linear k D]

/-- The ordinary-right Hom kernel of induction at a fixed output. -/
def inductionKernel (J : C ⥤ D) (w : D) : Cᵒᵖ ⥤ ModuleCat k where
  obj v := ModuleCat.of k (J.obj v.unop ⟶ w)
  map a := ModuleCat.ofHom (Linear.leftComp k w (J.map a.unop))
  map_id v := by
    ext g
    change J.map (𝟙 v.unop) ≫ g = g
    rw [J.map_id, Category.id_comp]
  map_comp a b := by
    ext g
    change J.map (b.unop ≫ a.unop) ≫ g = J.map b.unop ≫ (J.map a.unop ≫ g)
    rw [J.map_comp, Category.assoc]

@[simp] theorem inductionKernel_map_apply (J : C ⥤ D) (w : D)
    {v s : C} (a : v ⟶ s) (g : J.obj s ⟶ w) :
    (inductionKernel (k := k) J w).map a.op g = J.map a ≫ g := rfl

/-- The coefficient-kernel quotient is the existing induction quotient. -/
def inductionKernelEquiv (J : C ⥤ D) (M : C ⥤ SVec k) (w : D) :
    Obj (inductionKernel J w) M ≃ₗ[k] BalancedInduction.Obj J M w :=
  LinearEquiv.refl k _

@[simp] theorem inductionKernelEquiv_tensor (J : C ⥤ D) (M : C ⥤ SVec k)
    (w : D) (v : C) (g : J.obj v ⟶ w) (m : M.obj v) :
    inductionKernelEquiv J M w (tensor (inductionKernel J w) M v g m) =
      BalancedInduction.tensor J M v g m := rfl

@[simp] theorem inductionKernelEquiv_symm_tensor (J : C ⥤ D) (M : C ⥤ SVec k)
    (w : D) (v : C) (g : J.obj v ⟶ w) (m : M.obj v) :
    (inductionKernelEquiv J M w).symm (BalancedInduction.tensor J M v g m) =
      tensor (inductionKernel J w) M v g m := rfl

end OddMath.QuiverHecke.ELVOld.BalancedKernelTensor
end

end

section

/-! # Homogeneous transformations under a commuting induction square

The generator transport in DeformedActionAssembly §§5–6 compares the
literal old/truncated coends before comparing their chosen isomorphisms.
A commuting square gives a canonical map of coends. It intertwines every
homogeneous append transformation whose coefficient arrows map through the
square, retaining the full parity twist of arbitrary coefficient arrows.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u

section Coends
variable {k : Type u} [CommRing k]
  {C A B D : Type u} [Category.{u} C] [Category.{u} A]
  [Category.{u} B] [Category.{u} D]
  [Preadditive A] [Linear k A] [Preadditive D] [Linear k D]
  (J : C ⥤ A) (U : A ⥤ D) [U.Additive] [U.Linear k]
  (Q : C ⥤ B) (T : B ⥤ D) (h : J ⋙ U = Q ⋙ T)

/-- The coefficient arrow of the canonical coend map through the square. -/
def coendSquareCoefficient (v : C) (w : A) :
    (J.obj v ⟶ w) →ₗ[k] (T.obj (Q.obj v) ⟶ U.obj w) where
  toFun g := eqToHom (congrArg (fun F : C ⥤ D => F.obj v) h).symm ≫ U.map g
  map_add' g g' := by rw [U.map_add, Preadditive.comp_add]
  map_smul' r g := by
    rw [U.map_smul, Linear.comp_smul]
    rfl

theorem coendSquareCoefficient_balance {v v' : C} (f : v ⟶ v')
    (w : A) (g : J.obj v' ⟶ w) :
    coendSquareCoefficient (k := k) J U Q T h v w (J.map f ≫ g) =
      T.map (Q.map f) ≫ coendSquareCoefficient (k := k) J U Q T h v' w g := by
  have hn := (eqToHom h.symm : Q ⋙ T ⟶ J ⋙ U).naturality f
  simp only [eqToHom_app, Functor.comp_map] at hn
  change eqToHom _ ≫ U.map (J.map f ≫ g) =
    T.map (Q.map f) ≫ (eqToHom _ ≫ U.map g)
  rw [U.map_comp, ← Category.assoc, ← hn, Category.assoc]

variable (M : B ⥤ SVec k)

private def coendSquareTensor (w : A) (v : C) :
    (J.obj v ⟶ w) ⊗[k] (Q ⋙ M).obj v →ₗ[k] Obj T M (U.obj w) :=
  inclusion T M (U.obj w) (Q.obj v) ∘ₗ
    TensorProduct.map (coendSquareCoefficient (k := k) J U Q T h v w) LinearMap.id

private theorem coendSquareTensor_tmul (w : A) (v : C)
    (g : J.obj v ⟶ w) (b : M.obj (Q.obj v)) :
    coendSquareTensor J U Q T h M w v (g ⊗ₜ[k] b) =
      tensor T M (Q.obj v) (coendSquareCoefficient (k := k) J U Q T h v w g) b := rfl

/-- The canonical map on literal coends induced by a commuting functor square.
No fullness, flatness or evenness assumption on coefficient arrows is needed. -/
def coendSquareMap (w : A) : Obj J (Q ⋙ M) w →ₗ[k] Obj T M (U.obj w) :=
  lift J (Q ⋙ M) w (coendSquareTensor J U Q T h M w) (by
    intro v v' f g b
    rw [coendSquareTensor_tmul, coendSquareTensor_tmul,
      coendSquareCoefficient_balance (k := k)]
    exact balance T M (Q.map f) (coendSquareCoefficient (k := k) J U Q T h v' w g) b)

@[simp] theorem coendSquareMap_tensor (w : A) (v : C)
    (g : J.obj v ⟶ w) (b : M.obj (Q.obj v)) :
    coendSquareMap J U Q T h M w (tensor J (Q ⋙ M) v g b) =
      tensor T M (Q.obj v)
        (eqToHom (congrArg (fun F : C ⥤ D => F.obj v) h).symm ≫ U.map g) b := by
  rw [coendSquareMap, lift_tensor, coendSquareTensor_tmul]
  rfl

end Coends

section Transform
variable {k : Type u} [CommRing k]
  {C A B D : Type u} [Category.{u} C] [Category.{u} A]
  [Category.{u} B] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  [Preadditive B] [Linear k B] [Supercategory k B]
  [Preadditive D] [Linear k D] [Supercategory k D]
  (J K : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  (U : A ⥤ D) [U.Additive] [U.Linear k] [IsSuperfunctor k U]
  (Q : C ⥤ B) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
  (T S : B ⥤ D) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
  [S.Additive] [S.Linear k] [IsSuperfunctor k S]
  (hJ : J ⋙ U = Q ⋙ T) (hK : K ⋙ U = Q ⋙ S)
  (M : Superfunctor k B (SVec k))
  {p : ZMod 2} {α : ∀ v, J.obj v ⟶ K.obj v} {β : ∀ v, T.obj v ⟶ S.obj v}
  (hα : IsSupernatural k p α) (hβ : IsSupernatural k p β)

end Transform
end OddMath.QuiverHecke.ELVOld.BalancedInduction
end

end

section

/-! # Composition of coend comparisons across a six-category grid

The two-letter comparison in DeformedActionAssembly §§5–6 must agree
with the selected single-letter comparisons and the canonical induction
flattenings. The coefficient calculation retains the intermediate object
transports, before the generic coend calculation is specialized to the
changing fixed-content scalar quotient.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u

section Squares
variable {C₀ C₁ C₂ D₀ D₁ D₂ : Type u}
  [Category.{u} C₀] [Category.{u} C₁] [Category.{u} C₂]
  [Category.{u} D₀] [Category.{u} D₁] [Category.{u} D₂]
  (J : C₀ ⥤ C₁) (K : C₁ ⥤ C₂)
  (Q₀ : C₀ ⥤ D₀) (Q₁ : C₁ ⥤ D₁) (Q₂ : C₂ ⥤ D₂)
  (T : D₀ ⥤ D₁) (S : D₁ ⥤ D₂)
  (hJ : J ⋙ Q₁ = Q₀ ⋙ T) (hK : K ⋙ Q₂ = Q₁ ⋙ S)

end Squares

section Coefficients
variable {k : Type u} [CommRing k]
  {C₀ C₁ C₂ D₀ D₁ D₂ : Type u}
  [Category.{u} C₀] [Category.{u} C₁] [Category.{u} C₂]
  [Category.{u} D₀] [Category.{u} D₁] [Category.{u} D₂]
  [Preadditive C₁] [Linear k C₁] [Preadditive C₂] [Linear k C₂]
  [Preadditive D₁] [Linear k D₁] [Preadditive D₂] [Linear k D₂]
  (J : C₀ ⥤ C₁) (K : C₁ ⥤ C₂) (Q₀ : C₀ ⥤ D₀) (Q₁ : C₁ ⥤ D₁) [Q₁.Additive] [Q₁.Linear k]
  (Q₂ : C₂ ⥤ D₂) [Q₂.Additive] [Q₂.Linear k]
  (T : D₀ ⥤ D₁) (S : D₁ ⥤ D₂) (hJ : J ⋙ Q₁ = Q₀ ⋙ T) (hK : K ⋙ Q₂ = Q₁ ⋙ S)

end Coefficients

section Nested
variable {k : Type u} [CommRing k]
  {C₀ C₁ C₂ D₀ D₁ D₂ : Type u}
  [Category.{u} C₀] [Category.{u} C₁] [Category.{u} C₂]
  [Category.{u} D₀] [Category.{u} D₁] [Category.{u} D₂]
  [Preadditive C₀] [Linear k C₀]
  [Preadditive C₁] [Linear k C₁] [Preadditive C₂] [Linear k C₂]
  [Supercategory k C₀] [Supercategory k C₁] [Supercategory k C₂]
  [Preadditive D₀] [Linear k D₀]
  [Preadditive D₁] [Linear k D₁] [Preadditive D₂] [Linear k D₂]
  [Supercategory k D₀] [Supercategory k D₁] [Supercategory k D₂]
  (J : C₀ ⥤ C₁) (K : C₁ ⥤ C₂) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  (Q₀ : C₀ ⥤ D₀) [Q₀.Additive] [Q₀.Linear k] [IsSuperfunctor k Q₀]
  (Q₁ : C₁ ⥤ D₁) [Q₁.Additive] [Q₁.Linear k]
  (Q₂ : C₂ ⥤ D₂) [Q₂.Additive] [Q₂.Linear k]
  (T : D₀ ⥤ D₁) (S : D₁ ⥤ D₂) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
  [S.Additive] [S.Linear k] [IsSuperfunctor k S]
  (hJ : J ⋙ Q₁ = Q₀ ⋙ T) (hK : K ⋙ Q₂ = Q₁ ⋙ S)
  (M : Superfunctor k D₀ (SVec k))
private abbrev coendPullback : Superfunctor k C₀ (SVec k) := ⟨Q₀ ⋙ M.toFunctor⟩
local notation "RM" => coendPullback (k := k) Q₀ M

end Nested
end OddMath.QuiverHecke.ELVOld.BalancedInduction
end

end
