import OddMath.QuiverHecke.CyclotomicAction.ELVContentInductionNilpotence

/-! # Polynomial signs under balanced induction

The vacuum probe calculation in `SwappedVacuumBubbles.md`, (5), uses
signed induction: an odd source relation (a²−1)^m becomes (x²+1)^m.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
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

end OddMath.QuiverHecke.ELVOld.BalancedInduction

namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u v w
variable {k : Type w} {A : Type u} [CommRing k] [Category.{v} A] [Preadditive A] [Linear k A]
  {V W : A}

end OddMath.QuiverHecke.ELVOld.BalancedInduction

namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
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

end OddMath.QuiverHecke.ELVOld.BalancedInduction
