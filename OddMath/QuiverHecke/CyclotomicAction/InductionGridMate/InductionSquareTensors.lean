import Mathlib.CategoryTheory.EqToHom
import OddMath.QuiverHecke.CyclotomicAction.ContentModule.ContentParity
import OddMath.QuiverHecke.CyclotomicAction.KernelDegree

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
namespace OddMath.QuiverHecke.ELV.BalancedInduction
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

end OddMath.QuiverHecke.ELV.BalancedInduction
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
namespace OddMath.QuiverHecke.ELV.BalancedInduction
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

end OddMath.QuiverHecke.ELV.BalancedInduction
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
namespace OddMath.QuiverHecke.ELV
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
end OddMath.QuiverHecke.ELV
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
namespace OddMath.QuiverHecke.ELV.BalancedInduction
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

end OddMath.QuiverHecke.ELV.BalancedInduction
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
namespace OddMath.QuiverHecke.ELV.BalancedKernelTensor
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

end OddMath.QuiverHecke.ELV.BalancedKernelTensor
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
namespace OddMath.QuiverHecke.ELV.BalancedInduction
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
end OddMath.QuiverHecke.ELV.BalancedInduction
end

end
