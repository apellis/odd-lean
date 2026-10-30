import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInductionMap

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
variable (J : C ⥤ D) [J.Additive] [J.Linear k] [IsSuperfunctor k J]

example : (induction (k := k) J).Additive := inferInstance
example : (induction (k := k) J).Linear k := inferInstance
example : IsSuperfunctor k (induction (k := k) J) := inferInstance

example {M N : Superfunctor k C (SVec k)} (f : M ⟶ N)
    (p : ZMod 2) (w : D) (v : C) (h : J.obj v ⟶ w) (m : M.obj v) :
    ((induction J).map f).app p w (tensor J M.toFunctor v h m) =
      tensor J N.toFunctor v (twist k p h) (f.app p v m) :=
  mapComponent_tensor J f p w v h m

example {M N L : Superfunctor k C (SVec k)} (f : M ⟶ N) (g : N ⟶ L) :
    (induction J).map (f ≫ g) = (induction J).map f ≫ (induction J).map g :=
  (induction J).map_comp f g

#print axioms OddMath.QuiverHecke.ELVOld.BalancedInduction.induction
#print axioms OddMath.QuiverHecke.ELVOld.BalancedInduction.induction_super
#print axioms OddMath.QuiverHecke.ELVOld.BalancedInduction.mapComponent_tensor_of_mem
