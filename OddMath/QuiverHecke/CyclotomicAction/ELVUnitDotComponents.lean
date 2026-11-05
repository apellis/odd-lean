import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedMatrixRows
import OddMath.QuiverHecke.CyclotomicAction.ELVContentInductionNilpotence
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionPolynomialSigns

/-! # Dotted-unit fields in native module component coordinates

The normalization window in `SwappedVacuumNonpositiveBubbles.md`, §2,
uses powers of the actual module dot and the given ordinary unit. We keep
the native F/E superspace throughout total evaluation, before specializing
the regular probe. This also transports its probe polynomial to that
same component endomorphism.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u

private theorem total_add
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    (M : Superfunctor k C (SVec k)) (f g : End M) (w : C) :
    (f + g).total w = f.total w + g.total w := by
  change (f.app 0 w + g.app 0 w) + (f.app 1 w + g.app 1 w) =
    (f.app 0 w + f.app 1 w) + (g.app 0 w + g.app 1 w)
  abel

private theorem homogeneous_total_mem
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {F G : Superfunctor k C (SVec k)} {f : F ⟶ G} {p : ZMod 2}
    (hf : f ∈ parity (R := k) _ _ p) (w : C) :
    f.total w ∈ parity (R := k) (F.obj w) (G.obj w) p := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (by decide : (1 : ZMod 2) ≠ 0) w,
      add_zero]
    exact f.app_mem 0 w
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (by decide : (0 : ZMod 2) ≠ 1) w,
      zero_add]
    exact f.app_mem 1 w

variable {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)

/-- The given module dot after the actual restriction functor. -/
def restrictedDotEnd (M : Superfunctor k C (SVec k)) :
    End ((restriction J).obj ((induction J).obj M)) :=
  (restriction J).mapEnd ((induction J).obj M) (dotEnd J hα M)

/-- Its component is an endomorphism of the native F/E superspace. -/
def restrictedDotComponent (M : Superfunctor k C (SVec k)) (w : C) :
    End (((restriction J).obj ((induction J).obj M)).obj w) :=
  (restrictedDotEnd J hα M).total w

/-- The given dotted-unit column is the actual unit followed by powers of
this native module dot, before taking components. -/
theorem unitDotColumn_eq_restrictedDotEnd (M : Superfunctor k C (SVec k)) (n : ℕ) :
    unitDotColumn J hα M n =
      (adjunction J).unit.app M ≫ restrictedDotEnd J hα M ^ n := by
  unfold unitDotColumn restrictedDotEnd
  congr 1
  exact map_pow ((restriction J).mapEnd ((induction J).obj M)) (dotEnd J hα M) n

end OddMath.QuiverHecke.ELVOld.BalancedInduction
