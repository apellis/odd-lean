import OddMath.QuiverHecke.CyclotomicAction.ContentMatrix
import OddMath.QuiverHecke.CyclotomicAction.ModuleInduction
import OddMath.QuiverHecke.CyclotomicAction.ContentModule
import OddMath.QuiverHecke.CyclotomicAction.KernelDegree
import OddMath.Algebra.HomogeneousSuperfunctorIso
import OddMath.QuiverHecke.CyclotomicAction.InductionGridMate

/-!
# Induction mixed

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Polynomial signs under balanced induction

The vacuum probe calculation in `SwappedVacuumBubbles.md`, (5), uses
signed induction: an odd source relation (a²−1)^m becomes (x²+1)^m.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k C B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  {J : C ⥤ B} [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  {a : ∀ v, End (J.obj v)}

omit [IsSuperfunctor k J] in
private theorem squareDefect_supernatural (ha : IsSupernatural k 1 a) :
    IsSupernatural k 0 (fun v => a v ^ 2 - 1) := by
  apply IsSupernatural.of_twist
  · intro v
    have hh := comp_mem (ha.mem v) (ha.mem v)
    change a v ≫ a v ∈ parity (R := k) _ _ 0 at hh
    rw [pow_two, End.mul_def]
    exact sub_mem hh (id_mem _)
  · intro v w f
    have hh := (ha.comp ha).naturality_twist f
    change J.map f ≫ (a w ≫ a w) = (a v ≫ a v) ≫ J.map (twist k 0 f) at hh
    rw [pow_two, pow_two, End.mul_def, End.mul_def]
    change J.map f ≫ (a w ≫ a w - 𝟙 (J.obj w)) =
      (a v ≫ a v - 𝟙 (J.obj v)) ≫ J.map (twist k 0 f)
    rw [twist_zero] at hh ⊢
    rw [Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id, Category.id_comp, hh]

/-- The square of a signed odd induction operator changes the sign of the
source square. This identity holds on every vector of the balanced quotient. -/
theorem transformLinear_square_add_one (ha : IsSupernatural k 1 a)
    (M : Superfunctor k C (SVec k)) (w : B) :
    transformLinear ha M w ^ 2 + 1 = -transformLinear (squareDefect_supernatural ha) M w := by
  change (transformLinear ha M w).comp (transformLinear ha M w) + LinearMap.id = _
  rw [transformLinear_comp, one_mul, sign_one]
  apply hom_ext
  intro v h m
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.neg_apply, LinearMap.id_apply,
    transformLinear_tensor]
  change (-1 : k) • tensor J M.toFunctor v ((a v ≫ a v) ≫ twist k 0 h) m +
    tensor J M.toFunctor v h m = -tensor J M.toFunctor v ((a v ^ 2 - 1) ≫ twist k 0 h) m
  rw [neg_one_smul k, twist_zero, Preadditive.sub_comp, End.one_def, Category.id_comp, pow_two, End.mul_def]
  simp only [tensor, TensorProduct.sub_tmul, map_sub]
  module

/-- A source square-minus-one annihilator gives the required plus-one
annihilator on the signed odd induction dot. -/
theorem transformLinear_odd_probe_polynomial {p : ZMod 2} (ha : IsSupernatural k p a)
    (hp : p = 1) (m : ℕ) (hm : ∀ v, (a v ^ 2 - 1) ^ m = 0)
    (M : Superfunctor k C (SVec k)) (w : B) :
    (transformLinear ha M w ^ 2 + 1) ^ m = 0 := by
  subst p
  rw [transformLinear_square_add_one,
    ← neg_one_smul k (transformLinear (squareDefect_supernatural ha) M w), smul_pow,
    transformLinear_pow_zero (squareDefect_supernatural ha) m hm M w, smul_zero]

end OddMath.QuiverHecke.ELV.BalancedInduction

namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u v w
variable {k : Type w} {A : Type u} [CommRing k] [Category.{v} A] [Preadditive A] [Linear k A]
  {V W : A}

end OddMath.QuiverHecke.ELV.BalancedInduction

namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u v u' v'
variable {A : Type u} {B : Type u'} [Category.{v} A] [Category.{v'} B]
  [Preadditive A] [Preadditive B]

/-- Additive comparison functors, including the chosen parity-shift functor,
preserve the probe polynomial on the prescribed transformed endomorphism. -/
theorem additiveFunctor_odd_probe_polynomial (F : A ⥤ B) [F.Additive]
    {V : A} (x : End V) (m : ℕ) (h : (x ^ 2 + 1) ^ m = 0) :
    ((F.mapEnd V x) ^ 2 + 1) ^ m = 0 := by
  let f : End V →+* End (F.obj V) := {
    toFun := F.mapEnd V
    map_one' := (F.mapEnd V).map_one
    map_mul' := (F.mapEnd V).map_mul
    map_zero' := F.map_zero V V
    map_add' := fun _ _ => by exact F.map_add }
  have hh := congrArg f h
  simp only [map_pow, map_add, map_one, map_zero] at hh
  change (((F.mapEnd V) x) ^ 2 + 1) ^ m = 0 at hh
  exact hh

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # Two-functor induction crossing tensors

Canonical induction composition transports a homogeneous crossing between
two append functors. This is the generator comparison needed to evaluate
the distinct-colour cup-crossing-cap in Brundan–Ellis (1.12).
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k C : Type u} [CommRing k] [Category.{u} C]
  [Preadditive C] [Linear k C] [Supercategory k C]
variable (A B : C ⥤ C) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
  [B.Additive] [B.Linear k] [IsSuperfunctor k B]
variable {p : ZMod 2} {α : ∀ s, (B ⋙ A).obj s ⟶ (A ⋙ B).obj s}
  (hα : IsSupernatural k p α)

private def mixedFlatten (M : Superfunctor k C (SVec k)) :
    induced B (induced A M) ⟶ induced (A ⋙ B) M := (inductionComp A B).hom.app M

private def mixedUnflatten (M : Superfunctor k C (SVec k)) :
    induced (A ⋙ B) M ⟶ induced B (induced A M) := (inductionComp A B).inv.app M

private theorem mixedFlatten_tensor (M : Superfunctor k C (SVec k))
    (s w t : C) (g : B.obj w ⟶ t) (h : A.obj s ⟶ w) (b : M.obj s) :
    (mixedFlatten A B M).total t
      (tensor B (induced A M).toFunctor w g (tensor A M.toFunctor s h b)) =
    tensor (A ⋙ B) M.toFunctor s (B.map h ≫ g) b :=
  inductionComp_hom_total_tensor A B M s w t g h b

private theorem mixedUnflatten_tensor (M : Superfunctor k C (SVec k))
    (s t : C) (g : (A ⋙ B).obj s ⟶ t) (b : M.obj s) :
    (mixedUnflatten A B M).total t (tensor (A ⋙ B) M.toFunctor s g b) =
    tensor B (induced A M).toFunctor (A.obj s) g (tensor A M.toFunctor s (𝟙 _) b) :=
  inductionComp_inv_total_tensor A B M s t g b

/-- Canonical pair contraction, the signed crossing, and canonical expansion. -/
def mixedCrossComponent (M : Superfunctor k C (SVec k)) :
    induced B (induced A M) ⟶ induced A (induced B M) :=
  mixedFlatten A B M ≫ transformComponent hα M ≫ mixedUnflatten B A M

theorem mixedCrossComponent_supernatural :
    IsSupernatural k p (F := induction A ⋙ induction B) (G := induction B ⋙ induction A)
      (mixedCrossComponent A B hα) := by
  have hL := isSupernatural_of_natTrans (inductionComp (k := k) A B).hom
    (fun M => inductionComp_hom_mem A B M)
  have hT := transformComponent_supernatural hα
  have hR := isSupernatural_of_natTrans (inductionComp (k := k) B A).inv
    (fun M => inductionComp_inv_mem B A M)
  change IsSupernatural k p (F := induction A ⋙ induction B)
    (G := induction B ⋙ induction A) (fun M =>
      (inductionComp (k := k) A B).hom.app M ≫
        transformComponent hα M ≫ (inductionComp (k := k) B A).inv.app M)
  simpa only [zero_add, add_zero, Category.assoc] using hL.comp (hT.comp hR)

private theorem mixed_transform_total (M : Superfunctor k C (SVec k)) (w : C) :
    (transformComponent hα M).total w = transformLinear hα M w := by
  rcases parity_eq_zero_or_one p with h | h
  · simp only [SuperNatTrans.total, transformComponent_app, h, ↓reduceIte,
      one_ne_zero, add_zero]
  · simp only [SuperNatTrans.total, transformComponent_app, h, ↓reduceIte,
      zero_ne_one, zero_add]

private theorem mixedCrossComponent_total (M : Superfunctor k C (SVec k))
    (t : C) (x : Obj B (induced A M).toFunctor t) :
    (mixedCrossComponent A B hα M).total t x =
      (mixedUnflatten B A M).total t
        ((transformComponent hα M).total t ((mixedFlatten A B M).total t x)) := by
  rw [mixedCrossComponent, Superfunctor.comp_total, Superfunctor.comp_total]
  rfl

theorem mixedCrossComponent_total_tensor (M : Superfunctor k C (SVec k))
    (s w t : C) (g : B.obj w ⟶ t) (h : A.obj s ⟶ w) (b : M.obj s) :
    (mixedCrossComponent A B hα M).total t
      (tensor B (induced A M).toFunctor w g (tensor A M.toFunctor s h b)) =
    tensor A (induced B M).toFunctor (B.obj s)
      (α s ≫ twist k p (B.map h ≫ g))
      (tensor B M.toFunctor s (𝟙 _) b) := by
  rw [mixedCrossComponent_total, mixedFlatten_tensor]
  have ht := congrArg
    (fun f : Obj (A ⋙ B) M.toFunctor t →ₗ[k] Obj (B ⋙ A) M.toFunctor t =>
      f (tensor (A ⋙ B) M.toFunctor s (B.map h ≫ g) b)) (mixed_transform_total A B hα M t)
  have he := transformLinear_tensor hα M t s (B.map h ≫ g) b
  have hx := congrArg (fun x : Obj (B ⋙ A) M.toFunctor t =>
    (mixedUnflatten B A M).total t x) (ht.trans he)
  exact hx.trans (mixedUnflatten_tensor B A M s t
    (α s ≫ twist k p (B.map h ≫ g)) b)

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # Tensor evaluation of the ordered induction mate

The cup, canonically transported signed double transformation and cap are
composed in that order. The generator formula keeps the whole parity twist.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k C : Type u} [CommRing k] [Category.{u} C]
  [Preadditive C] [Linear k C] [Supercategory k C]
variable (A B : C ⥤ C) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
  [B.Additive] [B.Linear k] [IsSuperfunctor k B]
variable {p : ZMod 2} {α : ∀ s, (B ⋙ A).obj s ⟶ (A ⋙ B).obj s}
  (hα : IsSupernatural k p α)

private def moduleUnit (M : Superfunctor k C (SVec k)) :
    M ⟶ (restriction A).obj (induced A M) := (adjunctionUnit A).app M

private def moduleCounit (N : Superfunctor k C (SVec k)) :
    induced A ((restriction A).obj N) ⟶ N := (adjunctionCounit A).app N

private def inducedCounit (N : Superfunctor k C (SVec k)) :
    induced A (induced B ((restriction B).obj N)) ⟶ induced A N :=
  (induction A).map (moduleCounit B N)

private theorem unit_total_apply_mixed (M : Superfunctor k C (SVec k)) (t : C) (b : M.obj t) :
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

def orderedMixedMateComponent (N : Superfunctor k C (SVec k)) :
    induced A ((restriction B).obj N) ⟶ (restriction B).obj (induced A N) :=
  moduleUnit B (induced A ((restriction B).obj N)) ≫
    (restriction B).map (mixedCrossComponent A B hα ((restriction B).obj N)) ≫
    (restriction B).map (inducedCounit A B N)

private theorem orderedMixedMateComponent_total (N : Superfunctor k C (SVec k))
    (t : C) (x : (induced A ((restriction B).obj N)).obj t) :
    (orderedMixedMateComponent A B hα N).total t x =
      ((inducedCounit A B N).total (B.obj t))
        ((mixedCrossComponent A B hα ((restriction B).obj N)).total (B.obj t)
          (unit B (induced A ((restriction B).obj N)).toFunctor t x)) := by
  rw [orderedMixedMateComponent, Superfunctor.comp_total, Superfunctor.comp_total]
  simp only [SVec.comp_apply]
  rw [unit_total_apply_mixed, restriction_map_total_apply, restriction_map_total_apply]

theorem orderedMixedMateComponent_total_tensor (N : Superfunctor k C (SVec k))
    (s t : C) (g : A.obj s ⟶ t) (b : N.obj (B.obj s)) :
    (orderedMixedMateComponent A B hα N).total t
      (tensor A ((restriction B).obj N).toFunctor s g b) =
    tensor A N.toFunctor (B.obj s) (α s ≫ twist k p (B.map g)) b := by
  rw [orderedMixedMateComponent_total, unit_apply, mixedCrossComponent_total_tensor]
  have he := induction_map_even_tensor A
    (M := induced B ((restriction B).obj N)) (N := N)
    (moduleCounit B N) (adjunctionCounit_mem B N)
    (B.obj s) (B.obj t) (α s ≫ twist k p (B.map g ≫ 𝟙 _))
    (tensor B ((restriction B).obj N).toFunctor s (𝟙 _) b)
  have hc := counit_total_tensor B N s (B.obj s) (𝟙 _) b
  have hi : N.map (𝟙 (B.obj s)) b = b := by
    change (N.toFunctor.map (𝟙 (B.obj s))) b = b
    rw [N.toFunctor.map_id]
    rfl
  have hr := congrArg (fun x : N.obj (B.obj s) =>
    tensor A N.toFunctor (B.obj s) (α s ≫ twist k p (B.map g ≫ 𝟙 _)) x) (hc.trans hi)
  have hn := he.trans hr
  simp only [Category.comp_id] at hn
  simp only [Category.comp_id]
  exact hn

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # Rectangular induction crossing mates

Brundan–Ellis (1.12) on fixed content uses four different append functors:
the two lower appends and the two upper appends. The canonical induction
composition maps, the positive prescribed crossing, and the ordinary
adjunction unit and counit give the rectangular cup-crossing-cap below.
Its tensor formula keeps the twist of the entire coefficient arrow.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C A B E : Type u} [Category.{u} C] [Category.{u} A] [Category.{u} B] [Category.{u} E]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  [Preadditive B] [Linear k B] [Supercategory k B]
  [Preadditive E] [Linear k E] [Supercategory k E]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : C ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  (L : A ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]
  (M : B ⥤ E) [M.Additive] [M.Linear k] [IsSuperfunctor k M]
  {p : ZMod 2} {α : ∀ s, (J ⋙ L).obj s ⟶ (K ⋙ M).obj s}
  (hα : IsSupernatural k p α)

private def rectangularFlatten (P : Superfunctor k C (SVec k)) :
    induced M (induced K P) ⟶ induced (K ⋙ M) P := (inductionComp K M).hom.app P

private def rectangularUnflatten (P : Superfunctor k C (SVec k)) :
    induced (J ⋙ L) P ⟶ induced L (induced J P) := (inductionComp J L).inv.app P

private theorem rectangularFlatten_tensor (P : Superfunctor k C (SVec k))
    (s : C) (v : B) (w : E) (a : K.obj s ⟶ v) (g : M.obj v ⟶ w) (b : P.obj s) :
    (rectangularFlatten K M P).total w
      (tensor M (induced K P).toFunctor v g (tensor K P.toFunctor s a b)) =
      tensor (K ⋙ M) P.toFunctor s (M.map a ≫ g) b :=
  inductionComp_hom_total_tensor K M P s v w g a b

private theorem rectangularUnflatten_tensor (P : Superfunctor k C (SVec k))
    (s : C) (w : E) (g : (J ⋙ L).obj s ⟶ w) (b : P.obj s) :
    (rectangularUnflatten J L P).total w (tensor (J ⋙ L) P.toFunctor s g b) =
      tensor L (induced J P).toFunctor (J.obj s) g (tensor J P.toFunctor s (𝟙 _) b) :=
  inductionComp_inv_total_tensor J L P s w g b

/-- The rectangular crossing uses the two chosen induction-composition maps. -/
def rectangularCrossComponent (P : Superfunctor k C (SVec k)) :
    induced M (induced K P) ⟶ induced L (induced J P) :=
  rectangularFlatten K M P ≫ transformComponent hα P ≫ rectangularUnflatten J L P

private theorem rectangularTransform_total (P : Superfunctor k C (SVec k)) (w : E) :
    (transformComponent hα P).total w = transformLinear hα P w := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp only [SuperNatTrans.total, transformComponent_app,
      ite_true, ite_false, zero_ne_one, one_ne_zero, add_zero, zero_add]

private theorem rectangularCrossComponent_total (P : Superfunctor k C (SVec k))
    (w : E) (x : Obj M (induced K P).toFunctor w) :
    (rectangularCrossComponent J K L M hα P).total w x =
      (rectangularUnflatten J L P).total w
        ((transformComponent hα P).total w ((rectangularFlatten K M P).total w x)) := by
  rw [rectangularCrossComponent, Superfunctor.comp_total, Superfunctor.comp_total]
  rfl

/-- Canonical flattening, crossing and expansion on each nested tensor. -/
theorem rectangularCrossComponent_total_tensor (P : Superfunctor k C (SVec k))
    (s : C) (v : B) (w : E) (a : K.obj s ⟶ v) (g : M.obj v ⟶ w) (b : P.obj s) :
    (rectangularCrossComponent J K L M hα P).total w
      (tensor M (induced K P).toFunctor v g (tensor K P.toFunctor s a b)) =
      tensor L (induced J P).toFunctor (J.obj s)
        (α s ≫ twist k p (M.map a ≫ g)) (tensor J P.toFunctor s (𝟙 _) b) := by
  rw [rectangularCrossComponent_total, rectangularFlatten_tensor]
  have h₁ := congrArg
    (fun f : Obj (K ⋙ M) P.toFunctor w →ₗ[k] Obj (J ⋙ L) P.toFunctor w =>
      f (tensor (K ⋙ M) P.toFunctor s (M.map a ≫ g) b)) (rectangularTransform_total J K L M hα P w)
  have h₂ := transformLinear_tensor hα P w s (M.map a ≫ g) b
  have h₃ := congrArg (fun x : Obj (J ⋙ L) P.toFunctor w =>
    (rectangularUnflatten J L P).total w x) (h₁.trans h₂)
  exact h₃.trans (rectangularUnflatten_tensor J L P s w
    (α s ≫ twist k p (M.map a ≫ g)) b)

/-- The rectangular crossing is supernatural in every input module. -/
theorem rectangularCrossComponent_supernatural :
    IsSupernatural k p (F := induction K ⋙ induction M) (G := induction J ⋙ induction L)
      (rectangularCrossComponent J K L M hα) := by
  have h₁ := isSupernatural_of_natTrans (inductionComp (k := k) K M).hom
    (fun P => inductionComp_hom_mem K M P)
  have h₂ := transformComponent_supernatural hα
  have h₃ := isSupernatural_of_natTrans (inductionComp (k := k) J L).inv
    (fun P => inductionComp_inv_mem J L P)
  change IsSupernatural k p (F := induction K ⋙ induction M) (G := induction J ⋙ induction L)
    (fun P => (inductionComp K M).hom.app P ≫ transformComponent hα P ≫
      (inductionComp J L).inv.app P)
  simpa only [zero_add, add_zero, Category.assoc] using h₁.comp (h₂.comp h₃)

private def rectangularModuleUnit (P : Superfunctor k B (SVec k)) :
    P ⟶ (restriction M).obj (induced M P) := (adjunctionUnit M).app P

private def rectangularModuleCounit (N : Superfunctor k A (SVec k)) :
    induced J ((restriction J).obj N) ⟶ N := (adjunctionCounit J).app N

private def rectangularInducedCounit (N : Superfunctor k A (SVec k)) :
    induced L (induced J ((restriction J).obj N)) ⟶ induced L N :=
  (induction L).map (rectangularModuleCounit J N)

private theorem rectangularUnit_total
    (P : Superfunctor k B (SVec k)) (t : B) (b : P.obj t) :
    (rectangularModuleUnit M P).total t b = unit M P.toFunctor t b := by
  simp only [rectangularModuleUnit, adjunctionUnit, Superfunctor.homMk, SuperNatTrans.total,
    unitTransform_app, ↓reduceIte, one_ne_zero, add_zero]
  rfl

private theorem rectangularCounit_total (N : Superfunctor k A (SVec k))
    (s : C) (t : A) (g : J.obj s ⟶ t) (b : N.obj (J.obj s)) :
    (rectangularModuleCounit J N).total t
      (tensor J ((restriction J).obj N).toFunctor s g b) = N.map g b := by
  simp only [rectangularModuleCounit, adjunctionCounit, Superfunctor.homMk, SuperNatTrans.total,
    counitTransform_app, ↓reduceIte, one_ne_zero, add_zero]
  exact counit_tensor J N.toFunctor t s g b

private theorem rectangularInduction_even_tensor
    {P Q : Superfunctor k A (SVec k)} (f : P ⟶ Q)
    (hf : f ∈ parity (R := k) P Q 0)
    (s : A) (t : E) (g : L.obj s ⟶ t) (b : P.obj s) :
    ((induction L).map f).total t (tensor L P.toFunctor s g b) =
      tensor L Q.toFunctor s g (f.total s b) := by
  have h₁ := Superfunctor.app_eq_zero_of_mem hf (show (1 : ZMod 2) ≠ 0 by decide)
  change (moduleMap L f).total t _ = _
  rw [moduleMap_total_tensor, h₁]
  simp only [SuperNatTrans.total, h₁, add_zero]
  change tensor L Q.toFunctor s g (f.app 0 s b) +
    tensor L Q.toFunctor s (twist k 1 g) 0 = _
  rw [tensor_zero_right, add_zero]

private theorem rectangularRestriction_total
    {P Q : Superfunctor k E (SVec k)} (f : P ⟶ Q) (t : B) (b : P.obj (M.obj t)) :
    ((restriction M).map f).total t b = f.total (M.obj t) b := rfl

/-- The specified positive rectangular cup-crossing-cap with both append adjunctions. -/
def orderedRectangularMateComponent (N : Superfunctor k A (SVec k)) :
    induced K ((restriction J).obj N) ⟶ (restriction M).obj (induced L N) :=
  rectangularModuleUnit M (induced K ((restriction J).obj N)) ≫
    (restriction M).map (rectangularCrossComponent J K L M hα ((restriction J).obj N)) ≫
    (restriction M).map (rectangularInducedCounit J L N)

/-- Both bending maps are even, so the rectangular mate retains the crossing parity. -/
theorem orderedRectangularMateComponent_mem (N : Superfunctor k A (SVec k)) :
    orderedRectangularMateComponent J K L M hα N ∈ parity (R := k) _ _ p := by
  have hu : rectangularModuleUnit M (induced K ((restriction J).obj N)) ∈
      parity (R := k) _ _ 0 := adjunctionUnit_mem M _
  have hx := (rectangularCrossComponent_supernatural J K L M hα).mem ((restriction J).obj N)
  have hc : rectangularModuleCounit J N ∈ parity (R := k) _ _ 0 := adjunctionCounit_mem J N
  have hi : rectangularInducedCounit J L N ∈ parity (R := k) _ _ 0 :=
    map_mem (induction L) hc
  have hmx := map_mem (restriction M) hx
  have hmc := map_mem (restriction M) hi
  change (rectangularModuleUnit M (induced K ((restriction J).obj N)) ≫
    (restriction M).map (rectangularCrossComponent J K L M hα ((restriction J).obj N)) ≫
    (restriction M).map (rectangularInducedCounit J L N)) ∈ parity (R := k) _ _ p
  simpa only [zero_add, add_zero] using comp_mem hu (comp_mem hmx hmc)

private theorem orderedRectangularMateComponent_total (N : Superfunctor k A (SVec k))
    (t : B) (x : (induced K ((restriction J).obj N)).obj t) :
    (orderedRectangularMateComponent J K L M hα N).total t x =
      ((rectangularInducedCounit J L N).total (M.obj t))
        ((rectangularCrossComponent J K L M hα ((restriction J).obj N)).total (M.obj t)
          (unit M (induced K ((restriction J).obj N)).toFunctor t x)) := by
  rw [orderedRectangularMateComponent, Superfunctor.comp_total, Superfunctor.comp_total]
  simp only [SVec.comp_apply]
  rw [rectangularUnit_total, rectangularRestriction_total, rectangularRestriction_total]

/-- The complete coefficient arrow is twisted; no homogeneity hypothesis on it is needed. -/
theorem orderedRectangularMateComponent_total_tensor (N : Superfunctor k A (SVec k))
    (s : C) (t : B) (g : K.obj s ⟶ t) (b : N.obj (J.obj s)) :
    (orderedRectangularMateComponent J K L M hα N).total t
      (tensor K ((restriction J).obj N).toFunctor s g b) =
      tensor L N.toFunctor (J.obj s) (α s ≫ twist k p (M.map g)) b := by
  rw [orderedRectangularMateComponent_total, unit_apply, rectangularCrossComponent_total_tensor]
  unfold rectangularInducedCounit
  have h₁ := rectangularInduction_even_tensor L
    (rectangularModuleCounit J N) (adjunctionCounit_mem J N)
    (J.obj s) (M.obj t) (α s ≫ twist k p (M.map g ≫ 𝟙 _))
    (tensor J ((restriction J).obj N).toFunctor s (𝟙 _) b)
  have h₂ := rectangularCounit_total J N s (J.obj s) (𝟙 _) b
  have h₃ : N.map (𝟙 (J.obj s)) b = b := by
    change (N.toFunctor.map (𝟙 (J.obj s))) b = b
    rw [N.toFunctor.map_id]
    rfl
  have h₄ := congrArg (fun y : N.obj (J.obj s) =>
    tensor L N.toFunctor (J.obj s) (α s ≫ twist k p (M.map g ≫ 𝟙 _)) y) (h₂.trans h₃)
  have h₅ := h₁.trans h₄
  set_option backward.dsimp.instances true in
    dsimp only [induction, restriction] at h₅ ⊢
  simpa only [Category.comp_id] using h₅

/-- The rectangular mate with its two coend endpoints fixed before specialization. -/
def orderedRectangularMateLinear (N : Superfunctor k A (SVec k)) (t : B) :
    Obj K ((restriction J).obj N).toFunctor t →ₗ[k] Obj L N.toFunctor (M.obj t) :=
  (orderedRectangularMateComponent J K L M hα N).total t

/-- The coend map has the prescribed positive tensor formula. -/
theorem orderedRectangularMateLinear_tensor (N : Superfunctor k A (SVec k))
    (s : C) (t : B) (g : K.obj s ⟶ t) (b : N.obj (J.obj s)) :
    orderedRectangularMateLinear J K L M hα N t
      (tensor K ((restriction J).obj N).toFunctor s g b) =
      tensor L N.toFunctor (J.obj s) (α s ≫ twist k p (M.map g)) b :=
  orderedRectangularMateComponent_total_tensor J K L M hα N s t g b

/-- Package bijectivity of the fixed rectangular coend map at generic endpoints. -/
def orderedRectangularMateEquiv (N : Superfunctor k A (SVec k)) (t : B)
    (h : Function.Bijective (orderedRectangularMateLinear J K L M hα N t)) :
    Obj K ((restriction J).obj N).toFunctor t ≃ₗ[k] Obj L N.toFunctor (M.obj t) :=
  LinearEquiv.ofBijective (orderedRectangularMateLinear J K L M hα N t) h

@[simp] theorem orderedRectangularMateEquiv_toLinearMap (N : Superfunctor k A (SVec k)) (t : B)
    (h : Function.Bijective (orderedRectangularMateLinear J K L M hα N t)) :
    (orderedRectangularMateEquiv J K L M hα N t h).toLinearMap =
      orderedRectangularMateLinear J K L M hα N t := rfl

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # Induction crossing comparison under append equalities

The comparison needed to transport Brundan–Ellis (1.12) to weight
products identifies the word-induction crossing with the rectangular
crossing. Append equalities are retained as whole functor equalities
before specializing to successor content certificates.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
universe u
variable {k C A B E : Type u} [CommRing k]
  [Category.{u} C] [Category.{u} A] [Category.{u} B] [Category.{u} E]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  [Preadditive B] [Linear k B] [Supercategory k B]
  [Preadditive E] [Linear k E] [Supercategory k E]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : C ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  (L : A ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]
  (U : B ⥤ E) [U.Additive] [U.Linear k] [IsSuperfunctor k U]
  (F G : C ⥤ E) [F.Additive] [F.Linear k] [IsSuperfunctor k F]
  [G.Additive] [G.Linear k] [IsSuperfunctor k G]
  (hF : J ⋙ L = F) (hG : K ⋙ U = G)
  {p : ZMod 2} {α : ∀ s, (J ⋙ L).obj s ⟶ (K ⋙ U).obj s}
  {β : ∀ s, F.obj s ⟶ G.obj s}
  (hα : IsSupernatural k p α) (hβ : IsSupernatural k p β)

private theorem inductionCompOfEq_refl (P : C ⥤ A) (Q : A ⥤ E)
    [P.Additive] [P.Linear k] [IsSuperfunctor k P]
    [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q] :
    inductionCompOfEq (k := k) P Q (P ⋙ Q) rfl = BalancedInduction.inductionComp P Q := by
  simp only [inductionCompOfEq, eqToIso_refl, Iso.trans_refl]

/-- Flattening to a word, applying its crossing, and expanding is the
rectangular crossing when its coefficient is the transported word crossing. -/
theorem inductionCompOfEq_cross
    (hcoeff : ∀ s, α s = eqToHom (congrArg (fun H : C ⥤ E => H.obj s) hF) ≫
      β s ≫ eqToHom (congrArg (fun H : C ⥤ E => H.obj s) hG).symm)
    (P : Superfunctor k C (SVec k)) :
    ((inductionCompOfEq K U G hG).hom.app P ≫
      BalancedInduction.transformComponent hβ P) ≫
        (inductionCompOfEq J L F hF).inv.app P =
      BalancedInduction.rectangularCrossComponent J K L U hα P := by
  subst F
  subst G
  have hαβ : α = β := by
    funext s
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using hcoeff s
  subst β
  rw [inductionCompOfEq_refl, inductionCompOfEq_refl]
  exact Category.assoc _ _ _

/-- A homogeneous induction transformation has its given component in its own degree. -/
theorem inductionTransform_app_self (P : Superfunctor k C (SVec k)) :
    (BalancedInduction.transform hβ).app p P = BalancedInduction.transformComponent hβ P := by
  simp only [BalancedInduction.transform, IsSupernatural.toSuperNatTrans, ↓reduceIte]

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Coefficient isomorphisms on balanced induction

The ordinary coefficient comparison needed in the arbitrary-module step of
Brundan–Ellis (1.12), `DeformedActionAssembly.md` §4. Coefficients change
before any module induction map or supernatural representing map is formed.
-/
noncomputable section
open CategoryTheory StringDiagrams TensorProduct
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k C D : Type u} [CommRing k] [Category.{u} C] [Category.{u} D]
  [Preadditive D] [Linear k D] (J : C ⥤ D)
variable {M N P : C ⥤ SVec k}

/-- Change only the coefficient in each prescribed balanced summand. -/
def coefficientMap (f : M ⟶ N) (w : D) : Obj J M w →ₗ[k] Obj J N w :=
  lift J M w (fun v => inclusion J N w v ∘ₗ
    TensorProduct.map LinearMap.id (SVec.toLinearMap (f.app v))) (by
      intro v v' r g m
      change tensor J N v (J.map r ≫ g) (f.app v m) =
        tensor J N v' g (f.app v' (M.map r m))
      rw [balance]
      congr 1
      have h := congrArg (fun a : M.obj v ⟶ N.obj v' => a m) (f.naturality r)
      exact h.symm)

@[simp] theorem coefficientMap_tensor (f : M ⟶ N) (w : D)
    (v : C) (g : J.obj v ⟶ w) (m : M.obj v) :
    coefficientMap J f w (tensor J M v g m) = tensor J N v g (f.app v m) := by
  rw [coefficientMap, lift_tensor]
  rfl

@[simp] theorem coefficientMap_id (w : D) : coefficientMap J (𝟙 M) w = LinearMap.id := by
  apply hom_ext
  intro v g m
  rw [coefficientMap_tensor]
  rfl

theorem coefficientMap_comp (f : M ⟶ N) (g : N ⟶ P) (w : D) :
    coefficientMap J (f ≫ g) w = coefficientMap J g w ∘ₗ coefficientMap J f w := by
  apply hom_ext
  intro v h m
  simp only [coefficientMap_tensor, LinearMap.comp_apply]
  rfl

/-- A coefficient natural isomorphism acts on the literal balanced quotient. -/
def coefficientEquiv (e : M ≅ N) (w : D) : Obj J M w ≃ₗ[k] Obj J N w :=
  LinearEquiv.ofLinearMap (coefficientMap J e.hom w) (coefficientMap J e.inv w)
    (by rw [← coefficientMap_comp, e.inv_hom_id, coefficientMap_id])
    (by rw [← coefficientMap_comp, e.hom_inv_id, coefficientMap_id])

@[simp] theorem coefficientEquiv_tensor (e : M ≅ N) (w : D)
    (v : C) (g : J.obj v ⟶ w) (m : M.obj v) :
    coefficientEquiv J e w (tensor J M v g m) = tensor J N v g (e.hom.app v m) :=
  coefficientMap_tensor J e.hom w v g m

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # The two-functor induction-restriction coefficient kernel

The explicit kernel realization needed by DeformedActionAssembly, sections 3–4, for Brundan–Ellis (1.12).
The double balanced quotient reduces by the covariant representable pairing,
using only quotient lifts and identity insertion. The ordinary-right source
action is precomposition. Grading and the prescribed matrix comparison are
separate from this underlying ground-ring equivalence.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory TensorProduct
open scoped Classical
namespace OddMath.QuiverHecke.ELV.MixedIndResKernel
universe u
variable {k : Type u} [CommRing k]
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive D] [Linear k D] [Supercategory k D]

variable (A B : C ⥤ D)

abbrev Component (v t : D) := BalancedInduction.Obj A (B ⋙ IndResKernel.homModule (k := k) v) t

def precompose {u v : D} (a : u ⟶ v) (t : D) :
    Component (k := k) A B v t →ₗ[k] Component (k := k) A B u t :=
  BalancedInduction.lift A (B ⋙ IndResKernel.homModule (k := k) v) t
    (fun s => BalancedInduction.inclusion A (B ⋙ IndResKernel.homModule (k := k) u) t s ∘ₗ
      TensorProduct.map LinearMap.id (Linear.leftComp k (B.obj s) a)) (by
        intro s s' f g b
        change BalancedInduction.tensor A (B ⋙ IndResKernel.homModule (k := k) u) s (A.map f ≫ g) (a ≫ b) =
          BalancedInduction.tensor A (B ⋙ IndResKernel.homModule (k := k) u) s' g (a ≫ (b ≫ B.map f))
        rw [BalancedInduction.balance]
        congr 1
        exact Category.assoc a b (B.map f))

@[simp] theorem precompose_tensor {u v : D} (a : u ⟶ v) (t : D)
    (s : C) (g : A.obj s ⟶ t) (b : v ⟶ B.obj s) :
    precompose (k := k) A B a t (BalancedInduction.tensor A (B ⋙ IndResKernel.homModule (k := k) v) s g b) =
      BalancedInduction.tensor A (B ⋙ IndResKernel.homModule (k := k) u) s g (a ≫ b) := by
  rw [precompose, BalancedInduction.lift_tensor]
  rfl

/-- The ordinary-right coefficient presheaf for induction after restriction. -/
def kernel (t : D) : Dᵒᵖ ⥤ ModuleCat k where
  obj v := ModuleCat.of k (Component (k := k) A B v.unop t)
  map a := ModuleCat.ofHom (precompose (k := k) A B a.unop t)
  map_id v := by
    apply ModuleCat.hom_ext
    apply BalancedInduction.hom_ext
    intro s g b
    change precompose (k := k) A B (𝟙 v.unop) t
      (BalancedInduction.tensor A (B ⋙ IndResKernel.homModule (k := k) v.unop) s g b) = _
    rw [precompose_tensor, Category.id_comp]
    rfl
  map_comp a b := by
    apply ModuleCat.hom_ext
    apply BalancedInduction.hom_ext
    intro s g h
    change precompose (k := k) A B (b.unop ≫ a.unop) t
      (BalancedInduction.tensor A (B ⋙ IndResKernel.homModule (k := k) _) s g h) =
      precompose (k := k) A B b.unop t (precompose (k := k) A B a.unop t
        (BalancedInduction.tensor A (B ⋙ IndResKernel.homModule (k := k) _) s g h))
    simp only [precompose_tensor]
    rw [Category.assoc]

variable (M : D ⥤ SVec k) [M.Additive] [M.Linear k]

/-- Evaluate the old representable factor on an arbitrary module element. -/
def evaluate (v t : D) (m : M.obj v) :
    Component (k := k) A B v t →ₗ[k] BalancedInduction.Obj A (B ⋙ M) t :=
  BalancedInduction.lift A (B ⋙ IndResKernel.homModule (k := k) v) t
    (fun s => BalancedInduction.inclusion A (B ⋙ M) t s ∘ₗ
      TensorProduct.map LinearMap.id
        ((M.mapLinearMap (R := k)).flip m)) (by
        intro s s' f g b
        change BalancedInduction.tensor A (B ⋙ M) s (A.map f ≫ g) (M.map b m) =
          BalancedInduction.tensor A (B ⋙ M) s' g (M.map (b ≫ B.map f) m)
        rw [BalancedInduction.balance, M.map_comp]
        rfl)

@[simp] theorem evaluate_tensor (v t : D) (m : M.obj v)
    (s : C) (g : A.obj s ⟶ t) (b : v ⟶ B.obj s) :
    evaluate A B M v t m (BalancedInduction.tensor A (B ⋙ IndResKernel.homModule (k := k) v) s g b) =
      BalancedInduction.tensor A (B ⋙ M) s g (M.map b m) := by
  rw [evaluate, BalancedInduction.lift_tensor]
  rfl

theorem evaluate_add (v t : D) (m m' : M.obj v) :
    evaluate A B M v t (m + m') = evaluate A B M v t m + evaluate A B M v t m' := by
  apply BalancedInduction.hom_ext
  intro s g b
  change evaluate A B M v t (m + m')
      (BalancedInduction.tensor A (B ⋙ IndResKernel.homModule (k := k) v) s g b) =
    evaluate A B M v t m
      (BalancedInduction.tensor A (B ⋙ IndResKernel.homModule (k := k) v) s g b) +
    evaluate A B M v t m'
      (BalancedInduction.tensor A (B ⋙ IndResKernel.homModule (k := k) v) s g b)
  rw [evaluate_tensor, evaluate_tensor, evaluate_tensor, map_add]
  simp only [BalancedInduction.tensor, tmul_add, map_add]

theorem evaluate_smul (v t : D) (r : k) (m : M.obj v) :
    evaluate A B M v t (r • m) = r • evaluate A B M v t m := by
  apply BalancedInduction.hom_ext
  intro s g b
  change evaluate A B M v t (r • m)
      (BalancedInduction.tensor A (B ⋙ IndResKernel.homModule (k := k) v) s g b) =
    r • evaluate A B M v t m
      (BalancedInduction.tensor A (B ⋙ IndResKernel.homModule (k := k) v) s g b)
  rw [evaluate_tensor, evaluate_tensor, map_smul]
  simp only [BalancedInduction.tensor, tmul_smul, map_smul]

def evaluatePair (v t : D) :
    Component (k := k) A B v t →ₗ[k] M.obj v →ₗ[k] BalancedInduction.Obj A (B ⋙ M) t where
  toFun x := {
    toFun := fun m => evaluate A B M v t m x
    map_add' := fun m m' => congrArg (fun f => f x) (evaluate_add A B M v t m m')
    map_smul' := fun r m => congrArg (fun f => f x) (evaluate_smul A B M v t r m) }
  map_add' x x' := by ext m; exact map_add (evaluate A B M v t m) x x'
  map_smul' r x := by ext m; exact map_smul (evaluate A B M v t m) r x

theorem evaluate_precompose {v w : D} (a : v ⟶ w) (t : D) (m : M.obj v) :
    evaluate A B M v t m ∘ₗ precompose (k := k) A B a t =
      evaluate A B M w t (M.map a m) := by
  apply BalancedInduction.hom_ext
  intro s g b
  simp only [LinearMap.comp_apply, precompose_tensor, evaluate_tensor, M.map_comp]
  rfl

/-- Flatten the two balances by evaluating the representable factor. -/
def forward (t : D) : BalancedKernelTensor.Obj (kernel (k := k) A B t) M →ₗ[k]
    BalancedInduction.Obj A (B ⋙ M) t :=
  BalancedKernelTensor.lift (kernel (k := k) A B t) M
    (fun v => TensorProduct.lift (evaluatePair A B M v t)) (by
      intro v w a x m
      change evaluate A B M v t m (precompose (k := k) A B a t x) =
        evaluate A B M w t (M.map a m) x
      exact congrArg (fun f => f x) (evaluate_precompose (k := k) A B M a t m))

@[simp] theorem forward_tensor (t v : D) (x : Component (k := k) A B v t) (m : M.obj v) :
    forward A B M t (BalancedKernelTensor.tensor (kernel (k := k) A B t) M v x m) =
      evaluate A B M v t m x := by
  rw [forward, BalancedKernelTensor.lift_tensor]
  rfl

/-- Insert the identity into the representable factor. -/
def identityLift (t : D) (s : C) : (A.obj s ⟶ t) →ₗ[k] Component (k := k) A B (B.obj s) t :=
  BalancedInduction.inclusion A (B ⋙ IndResKernel.homModule (k := k) (B.obj s)) t s ∘ₗ
    (TensorProduct.mk k (A.obj s ⟶ t) (B.obj s ⟶ B.obj s)).flip (𝟙 _)

@[simp] theorem identityLift_apply (t : D) (s : C) (g : A.obj s ⟶ t) :
    identityLift (k := k) A B t s g =
      BalancedInduction.tensor A (B ⋙ IndResKernel.homModule (k := k) (B.obj s)) s g (𝟙 _) := rfl

theorem identityLift_balance {s s' : C} (f : s ⟶ s') (t : D) (g : A.obj s' ⟶ t) :
    identityLift (k := k) A B t s (A.map f ≫ g) =
      precompose (k := k) A B (B.map f) t (identityLift (k := k) A B t s' g) := by
  rw [identityLift_apply, identityLift_apply, precompose_tensor,
    BalancedInduction.balance]
  change BalancedInduction.tensor A (B ⋙ IndResKernel.homModule (k := k) (B.obj s)) s' g
    (𝟙 _ ≫ B.map f) =
    BalancedInduction.tensor A (B ⋙ IndResKernel.homModule (k := k) (B.obj s)) s' g (B.map f ≫ 𝟙 _)
  rw [Category.id_comp, Category.comp_id]

def backward (t : D) : BalancedInduction.Obj A (B ⋙ M) t →ₗ[k]
    BalancedKernelTensor.Obj (kernel (k := k) A B t) M :=
  BalancedInduction.lift A (B ⋙ M) t
    (fun s => BalancedKernelTensor.inclusion (kernel (k := k) A B t) M (B.obj s) ∘ₗ
      TensorProduct.map (identityLift (k := k) A B t s) LinearMap.id) (by
      intro s s' f g m
      change BalancedKernelTensor.tensor (kernel (k := k) A B t) M (B.obj s)
        (identityLift (k := k) A B t s (A.map f ≫ g)) m =
        BalancedKernelTensor.tensor (kernel (k := k) A B t) M (B.obj s')
          (identityLift (k := k) A B t s' g) (M.map (B.map f) m)
      rw [identityLift_balance]
      exact BalancedKernelTensor.balance (kernel (k := k) A B t) M (B.map f)
        (identityLift (k := k) A B t s' g) m)

omit [M.Additive] [M.Linear k] in
@[simp] theorem backward_tensor (t : D) (s : C) (g : A.obj s ⟶ t)
    (m : M.obj (B.obj s)) :
    backward A B M t (BalancedInduction.tensor A (B ⋙ M) s g m) =
      BalancedKernelTensor.tensor (kernel (k := k) A B t) M (B.obj s) (identityLift (k := k) A B t s g) m := by
  rw [backward, BalancedInduction.lift_tensor]
  rfl

theorem forward_backward (t : D) : forward A B M t ∘ₗ backward A B M t = LinearMap.id := by
  apply BalancedInduction.hom_ext
  intro s g m
  simp only [LinearMap.comp_apply, backward_tensor, forward_tensor,
    identityLift_apply, evaluate_tensor, M.map_id]
  rfl

theorem backward_forward (t : D) : backward A B M t ∘ₗ forward A B M t = LinearMap.id := by
  apply BalancedKernelTensor.hom_ext
  intro v x m
  have h : backward A B M t ∘ₗ evaluate A B M v t m =
      BalancedKernelTensor.inclusion (kernel (k := k) A B t) M v ∘ₗ
        (TensorProduct.mk k (Component (k := k) A B v t) (M.obj v)).flip m := by
    apply BalancedInduction.hom_ext
    intro s g b
    change backward A B M t (evaluate A B M v t m
      (BalancedInduction.tensor A (B ⋙ IndResKernel.homModule (k := k) v) s g b)) =
      BalancedKernelTensor.tensor (kernel (k := k) A B t) M v
        (BalancedInduction.tensor A (B ⋙ IndResKernel.homModule (k := k) v) s g b) m
    rw [evaluate_tensor, backward_tensor]
    have hb := BalancedKernelTensor.balance (kernel (k := k) A B t) M b (identityLift (k := k) A B t s g) m
    change BalancedKernelTensor.tensor (kernel (k := k) A B t) M v
      (precompose (k := k) A B b t (identityLift (k := k) A B t s g)) m = _ at hb
    rw [identityLift_apply, precompose_tensor, Category.comp_id] at hb
    exact hb.symm
  change backward A B M t (forward A B M t
    (BalancedKernelTensor.tensor (kernel (k := k) A B t) M v x m)) = _
  rw [forward_tensor]
  exact congrArg (fun f => f x) h

/-- The coefficient kernel of induction-restriction acts on every module by
the existing balanced induction after restriction. No exactness is assumed. -/
def equiv (t : D) : BalancedKernelTensor.Obj (kernel (k := k) A B t) M ≃ₗ[k]
    BalancedInduction.Obj A (B ⋙ M) t :=
  LinearEquiv.ofLinearMap (forward A B M t) (backward A B M t)
    (forward_backward A B M t) (backward_forward A B M t)

@[simp] theorem equiv_tensor (t v : D) (x : Component (k := k) A B v t) (m : M.obj v) :
    equiv A B M t (BalancedKernelTensor.tensor (kernel (k := k) A B t) M v x m) =
      evaluate A B M v t m x := forward_tensor A B M t v x m

end OddMath.QuiverHecke.ELV.MixedIndResKernel
end

end

section

/-! # Ordinary-right kernels of two-functor crossing mates

The literal kernel map in `DeformedActionAssembly.md` §4 for
Brundan–Ellis (1.12). Crossing supernaturality proves lower balance;
ordinary right precomposition is retained without a representing sign.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory TensorProduct
namespace OddMath.QuiverHecke.ELV.MixedIndResKernel
universe u
variable {k C : Type u} [CommRing k] [Category.{u} C]
  [Preadditive C] [Linear k C] [Supercategory k C]
variable (A B : C ⥤ C) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
  [B.Additive] [B.Linear k] [IsSuperfunctor k B]
variable {p : ZMod 2} {α : ∀ s, (B ⋙ A).obj s ⟶ (A ⋙ B).obj s}
  (hα : IsSupernatural k p α)

private def matePair (v s t : C) : (A.obj s ⟶ t) →ₗ[k]
    (v ⟶ B.obj s) →ₗ[k] (A.obj v ⟶ B.obj t) where
  toFun g := Linear.rightComp k _ (α s ≫ twist k p (B.map g)) ∘ₗ A.mapLinearMap (R := k)
  map_add' g g' := by
    ext b
    simp only [LinearMap.comp_apply, Linear.rightComp_apply,
      Functor.map_add, map_add, Preadditive.comp_add, LinearMap.add_apply]
  map_smul' a g := by
    ext b
    simp only [LinearMap.comp_apply, Linear.rightComp_apply,
      Functor.map_smul, map_smul, Linear.comp_smul, LinearMap.smul_apply, RingHom.id_apply]

include hα in
private theorem matePair_balance (v s s' t : C) (f : s ⟶ s')
    (g : A.obj s' ⟶ t) (b : v ⟶ B.obj s) :
    matePair (k := k) A B (p := p) (α := α) v s t (A.map f ≫ g) b =
      matePair (k := k) A B (p := p) (α := α) v s' t g (b ≫ B.map f) := by
  have h := hα.naturality_twist f
  change A.map (B.map f) ≫ α s' = α s ≫ B.map (A.map (twist k p f)) at h
  rw [map_twist A, map_twist B] at h
  change A.map b ≫ α s ≫ twist k p (B.map (A.map f ≫ g)) =
    A.map (b ≫ B.map f) ≫ α s' ≫ twist k p (B.map g)
  calc
    _ = A.map b ≫ (α s ≫ twist k p (B.map (A.map f))) ≫ twist k p (B.map g) := by
      rw [Functor.map_comp, twist_comp]
      simp only [Category.assoc]
    _ = A.map b ≫ (A.map (B.map f) ≫ α s') ≫ twist k p (B.map g) :=
      congrArg (fun a : A.obj (B.obj s) ⟶ B.obj (A.obj s') =>
        A.map b ≫ a ≫ twist k p (B.map g)) h.symm
    _ = _ := by rw [Functor.map_comp]; simp only [Category.assoc]

/-- The ordered crossing-mate formula on the ordinary-right source kernel. -/
def mateComponent (v t : C) : Component (k := k) A B v t →ₗ[k] (A.obj v ⟶ B.obj t) :=
  BalancedInduction.lift A (B ⋙ IndResKernel.homModule (k := k) v) t
    (fun s => TensorProduct.lift (matePair (k := k) A B (p := p) (α := α) v s t))
    (fun s s' f g b => matePair_balance A B hα v s s' t f g b)

@[simp] theorem mateComponent_tensor (v s t : C) (g : A.obj s ⟶ t) (b : v ⟶ B.obj s) :
    mateComponent A B hα v t
      (BalancedInduction.tensor A (B ⋙ IndResKernel.homModule (k := k) v) s g b) =
      A.map b ≫ α s ≫ twist k p (B.map g) := by
  rw [mateComponent, BalancedInduction.lift_tensor]
  rfl

theorem mateComponent_precompose (u v t : C) (r : u ⟶ v) :
    mateComponent A B hα u t ∘ₗ precompose (k := k) A B r t =
      (Linear.leftComp k _ (A.map r)) ∘ₗ mateComponent A B hα v t := by
  apply BalancedInduction.hom_ext
  intro s g b
  simp only [LinearMap.comp_apply, precompose_tensor, mateComponent_tensor,
    Linear.leftComp_apply, Functor.map_comp, Category.assoc]

end OddMath.QuiverHecke.ELV.MixedIndResKernel
end

end

section

/-! # Fixed-endpoint linear maps of two-functor mates

The coend-level forward map needed in the arbitrary-module proof of
Brundan–Ellis (1.12), `DeformedActionAssembly.md` §4. The endpoints are fixed
before specializing to the old ELV category.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k C : Type u} [CommRing k] [Category.{u} C]
  [Preadditive C] [Linear k C] [Supercategory k C]
variable (A B : C ⥤ C) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
  [B.Additive] [B.Linear k] [IsSuperfunctor k B]
variable {p : ZMod 2} {α : ∀ s, (B ⋙ A).obj s ⟶ (A ⋙ B).obj s}
  (hα : IsSupernatural k p α)

private def restrictionCoefficientIso (N : Superfunctor k C (SVec k)) :
    B ⋙ N.toFunctor ≅ ((restriction B).obj N).toFunctor := Iso.refl _

private def restrictionSourceEquiv (N : Superfunctor k C (SVec k)) (t : C) :
    Obj A (B ⋙ N.toFunctor) t ≃ₗ[k] (induced A ((restriction B).obj N)).obj t :=
  coefficientEquiv A (restrictionCoefficientIso B N) t

private theorem restrictionSourceEquiv_toLinearMap (N : Superfunctor k C (SVec k)) (t : C) :
    (restrictionSourceEquiv A B N t).toLinearMap = LinearMap.id :=
  coefficientMap_id A t

def orderedMixedMateLinear (N : Superfunctor k C (SVec k)) (t : C) :
    (induced A ((restriction B).obj N)).obj t →ₗ[k] ((restriction B).obj (induced A N)).obj t :=
  (orderedMixedMateComponent (k := k) A B hα N).total t

@[simp] theorem orderedMixedMateLinear_tensor (N : Superfunctor k C (SVec k))
    (s t : C) (g : A.obj s ⟶ t) (b : N.obj (B.obj s)) :
    orderedMixedMateLinear (k := k) A B hα N t
      (tensor A ((restriction B).obj N).toFunctor s g b) =
      tensor A N.toFunctor (B.obj s) (α s ≫ twist k p (B.map g)) b :=
  orderedMixedMateComponent_total_tensor (k := k) A B hα N s t g b

/-- The ordinary coend coordinates are compared before applying the categorical mate. -/
def orderedMixedMateCoend (N : Superfunctor k C (SVec k)) (t : C) :
    Obj A (B ⋙ N.toFunctor) t →ₗ[k] Obj A N.toFunctor (B.obj t) :=
  orderedMixedMateLinear (k := k) A B hα N t ∘ₗ (restrictionSourceEquiv A B N t).toLinearMap

theorem orderedMixedMateCoend_eq_linear (N : Superfunctor k C (SVec k)) (t : C) :
    orderedMixedMateCoend (k := k) A B hα N t = orderedMixedMateLinear (k := k) A B hα N t := by
  rw [orderedMixedMateCoend, restrictionSourceEquiv_toLinearMap, LinearMap.comp_id]

@[simp] theorem orderedMixedMateCoend_tensor (N : Superfunctor k C (SVec k))
    (s t : C) (g : A.obj s ⟶ t) (b : N.obj (B.obj s)) :
    orderedMixedMateCoend (k := k) A B hα N t (tensor A (B ⋙ N.toFunctor) s g b) =
      tensor A N.toFunctor (B.obj s) (α s ≫ twist k p (B.map g)) b := by
  have he := congrArg (fun f : Obj A (B ⋙ N.toFunctor) t →ₗ[k] Obj A N.toFunctor (B.obj t) =>
    f (tensor A (B ⋙ N.toFunctor) s g b)) (orderedMixedMateCoend_eq_linear (k := k) A B hα N t)
  have hs : tensor A (B ⋙ N.toFunctor) s g b = tensor A ((restriction B).obj N).toFunctor s g b := rfl
  have ht := orderedMixedMateLinear_tensor (k := k) A B hα N s t g b
  exact he.trans ((congrArg (orderedMixedMateLinear (k := k) A B hα N t) hs).trans ht)

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # Homogeneous rectangular mate isomorphisms

Brundan–Ellis (1.12) needs module inverses and input-module naturality for
the prescribed rectangular cup-crossing-cap. Pointwise coend bijectivity
is packaged here before specializing the four categories. The fixed old
content proof supplies that bijectivity from its chosen chart square.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C A B E : Type u} [Category.{u} C] [Category.{u} A] [Category.{u} B] [Category.{u} E]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  [Preadditive B] [Linear k B] [Supercategory k B]
  [Preadditive E] [Linear k E] [Supercategory k E]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : C ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  (L : A ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]
  (M : B ⥤ E) [M.Additive] [M.Linear k] [IsSuperfunctor k M]
  {p : ZMod 2} {α : ∀ s, (J ⋙ L).obj s ⟶ (K ⋙ M).obj s}
  (hα : IsSupernatural k p α)

/-- The ordered rectangular mate is supernatural in arbitrary input-module maps. -/
theorem orderedRectangularMateComponent_supernatural :
    IsSupernatural k p (F := restriction (k := k) J ⋙ induction (k := k) K) (G := induction (k := k) L ⋙ restriction (k := k) M)
      (orderedRectangularMateComponent J K L M hα) := by
  have hU₀ := isSupernatural_of_natTrans (R := k) (adjunctionUnit (k := k) M)
    (fun P => adjunctionUnit_mem (k := k) M P)
  have hU := hU₀.whiskerLeft (restriction (k := k) J ⋙ induction (k := k) K)
  have hX := ((rectangularCrossComponent_supernatural J K L M hα).whiskerLeft
    (restriction (k := k) J)).whiskerRight (restriction (k := k) M)
  have hC₀ := isSupernatural_of_natTrans (R := k) (adjunctionCounit (k := k) J)
    (fun N => adjunctionCounit_mem (k := k) J N)
  have hC := (hC₀.whiskerRight (induction (k := k) L)).whiskerRight (restriction (k := k) M)
  change IsSupernatural k p (F := restriction (k := k) J ⋙ induction (k := k) K) (G := induction (k := k) L ⋙ restriction (k := k) M)
    (fun N => (adjunctionUnit (k := k) M).app (induced K ((restriction (k := k) J).obj N)) ≫
      (restriction (k := k) M).map (rectangularCrossComponent J K L M hα ((restriction (k := k) J).obj N)) ≫
      (restriction (k := k) M).map ((induction (k := k) L).map ((adjunctionCounit (k := k) J).app N)))
  have h := hU.comp (hX.comp hC)
  set_option backward.dsimp.instances true in
    dsimp only [induction] at h ⊢
  simpa only [Functor.comp_id, Functor.id_comp, Functor.comp_obj, zero_add, add_zero,
    Category.assoc] using h

/-- Pointwise bijectivity of the prescribed coend map supplies its homogeneous module inverse. -/
def rectangularMateModuleIso (N : Superfunctor k A (SVec k))
    (h : ∀ t, Function.Bijective (orderedRectangularMateLinear J K L M hα N t)) :
    induced K ((restriction (k := k) J).obj N) ≅ (restriction (k := k) M).obj (induced L N) :=
  HomogeneousSuperfunctorIso.ofHom (orderedRectangularMateComponent J K L M hα N)
    (orderedRectangularMateComponent_mem J K L M hα N)
    (fun t => SVec.isoOfLinearEquiv (orderedRectangularMateEquiv J K L M hα N t (h t)))
    (fun _ => rfl)

@[simp] theorem rectangularMateModuleIso_hom (N : Superfunctor k A (SVec k))
    (h : ∀ t, Function.Bijective (orderedRectangularMateLinear J K L M hα N t)) :
    (rectangularMateModuleIso J K L M hα N h).hom =
      orderedRectangularMateComponent J K L M hα N :=
  HomogeneousSuperfunctorIso.ofHom_hom _ _ _ _

/-- The lower restriction followed by lower induction, as a superfunctor on modules. -/
def rectangularMateSourceFunctor :
    Superfunctor k (Superfunctor k A (SVec k)) (Superfunctor k B (SVec k)) :=
  ⟨restriction (k := k) J ⋙ induction (k := k) K⟩

/-- The upper induction followed by upper restriction, as a superfunctor on modules. -/
def rectangularMateTargetFunctor :
    Superfunctor k (Superfunctor k A (SVec k)) (Superfunctor k B (SVec k)) :=
  ⟨induction (k := k) L ⋙ restriction (k := k) M⟩

/-- The homogeneous transformation formed by the prescribed ordered components. -/
def rectangularMateHom : rectangularMateSourceFunctor (k := k) J K ⟶ rectangularMateTargetFunctor (k := k) L M :=
  (orderedRectangularMateComponent_supernatural J K L M hα).toSuperNatTrans

theorem rectangularMateHom_mem :
    rectangularMateHom J K L M hα ∈ parity (R := k) _ _ p :=
  Superfunctor.mem_parity_iff_isHomogeneous.mpr
    (orderedRectangularMateComponent_supernatural J K L M hα).toSuperNatTrans_isHomogeneous

/-- The total input-module component is exactly the prescribed module mate. -/
@[simp] theorem rectangularMateHom_total (N : Superfunctor k A (SVec k)) :
    (rectangularMateHom J K L M hα).total N = orderedRectangularMateComponent J K L M hα N :=
  HomogeneousSuperfunctorIso.homogeneous_total
    (F := rectangularMateSourceFunctor (k := k) J K)
    (G := rectangularMateTargetFunctor (k := k) L M)
    (orderedRectangularMateComponent_supernatural J K L M hα) N

/-- The inverse is supernatural in arbitrary, including odd, input-module maps. -/
def rectangularMateFunctorIso
    (h : ∀ N t, Function.Bijective (orderedRectangularMateLinear J K L M hα N t)) :
    rectangularMateSourceFunctor (k := k) J K ≅ rectangularMateTargetFunctor (k := k) L M :=
  HomogeneousSuperfunctorIso.ofHom (rectangularMateHom J K L M hα)
    (rectangularMateHom_mem J K L M hα)
    (fun N => rectangularMateModuleIso J K L M hα N (h N))
    (fun N => (rectangularMateModuleIso_hom J K L M hα N (h N)).trans
      (rectangularMateHom_total J K L M hα N).symm)

@[simp] theorem rectangularMateFunctorIso_hom
    (h : ∀ N t, Function.Bijective (orderedRectangularMateLinear J K L M hα N t)) :
    (rectangularMateFunctorIso J K L M hα h).hom = rectangularMateHom J K L M hα :=
  HomogeneousSuperfunctorIso.ofHom_hom _ _ _ _

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # Components of induction comparison isomorphisms

The selected E/F charts in the fixed-content proof of Brundan–Ellis (1.12)
are existing supermodule isomorphisms. Their components are bijective on
the actual balanced coends. The coend endpoints are fixed here before
specializing to the old category, including arbitrary coefficient modules.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k : Type u} [CommRing k]

private def evaluationFunctor
    {C : Type u} [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C] (t : C) :
    Superfunctor k C (SVec k) ⥤ SVec k where
  obj P := P.obj t
  map f := f.total t
  map_id P := SuperNatTrans.id_total P.toFunctor t
  map_comp f g := Superfunctor.comp_total f g t

private theorem svecIso_bijective {V W : SVec k} (e : V ≅ W) :
    Function.Bijective (SVec.toLinearMap e.hom) := by
  refine ⟨?_, ?_⟩
  · intro x y h
    have hx := LinearMap.congr_fun e.hom_inv_id x
    have hy := LinearMap.congr_fun e.hom_inv_id y
    exact hx.symm.trans ((congrArg e.inv h).trans hy)
  · intro y
    exact ⟨e.inv y, LinearMap.congr_fun e.inv_hom_id y⟩

variable {C A B O : Type u}
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  [Category.{u} O] [Preadditive O] [Linear k O] [Supercategory k O]
  (K : C ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  (H : A ⥤ O) [H.Additive] [H.Linear k] [IsSuperfunctor k H]
  (Q : B ⥤ O) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
  (P : Superfunctor k C (SVec k)) (N : Superfunctor k A (SVec k))
  (e : induced K P ≅ (restriction Q).obj (induced H N)) (t : B)

/-- The selected isomorphism component on its two literal coend carriers. -/
def coendIsoLinear : Obj K P.toFunctor t →ₗ[k] Obj H N.toFunctor (Q.obj t) :=
  e.hom.total t

/-- Every component of the selected isomorphism is bijective on the entire coend. -/
theorem coendIsoLinear_bijective : Function.Bijective (coendIsoLinear K H Q P N e t) := by
  have h := svecIso_bijective ((evaluationFunctor t).mapIso e)
  exact h

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # Homogeneity of the changing-category crossing mate

DeformedMatrixComparison (2), (4) uses the prescribed ordered mate in
parity-shifted matrix coordinates. Its degree follows from the given
crossing, even induction comparisons and even ordinary adjunction maps.
No invertibility of the mate is assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
private theorem even_comp_homogeneous_comp_even
    {k : Type u} [CommRing k] {E : Type*} [Category E]
    [Preadditive E] [Linear k E] [Supercategory k E]
    {a b c d : E} {p : ZMod 2} {f : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d}
    (hf : f ∈ parity (R := k) _ _ 0) (hg : g ∈ parity (R := k) _ _ p)
    (hh : h ∈ parity (R := k) _ _ 0) :
    f ≫ g ≫ h ∈ parity (R := k) _ _ p := by
  simpa only [zero_add, add_zero] using comp_mem hf (comp_mem hg hh)

variable {k : Type u} [CommRing k]
  {C A B : Type u} [Category.{u} C] [Category.{u} A] [Category.{u} B]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  {p : ZMod 2} {α : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
  (hα : IsSupernatural k p α)

/-- Both flattening comparisons are even, so the prescribed double
crossing retains the given crossing degree. -/
theorem gridDoubleCrossComponent_mem (M : Superfunctor k C (SVec k)) :
    gridDoubleCrossComponent J K hα M ∈ parity (R := k) _ _ p := by
  unfold gridDoubleCrossComponent
  exact even_comp_homogeneous_comp_even (inductionComp_hom_mem J K M)
    (transformComponent_mem hα M) (inductionComp_inv_mem J K M)

/-- The ordinary unit, signed crossing and induced counit have degrees
zero, p and zero respectively. -/
theorem orderedGridMateComponent_mem (N : Superfunctor k A (SVec k)) :
    orderedGridMateComponent J K hα N ∈ parity (R := k) _ _ p := by
  unfold orderedGridMateComponent
  exact even_comp_homogeneous_comp_even
    (adjunctionUnit_mem K (induced J ((restriction J).obj N)))
    (map_mem (restriction K)
      (Submodule.neg_mem _ (gridDoubleCrossComponent_mem J K hα ((restriction J).obj N))))
    (map_mem (restriction K) (map_mem (induction K) (adjunctionCounit_mem J N)))

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end
