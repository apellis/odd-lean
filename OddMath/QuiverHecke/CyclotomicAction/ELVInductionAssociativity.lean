/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionWhiskering

/-! # Associativity of induction flattening

The two recursive composition comparisons agree on every superfunctor module.
`compForward_assoc` compares independently constructed flattening trees, using
only the existing balanced quotients. This is the associativity comparison
needed by the content triple E-action assembly. Content equality transports
are not yet included in this statement.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
universe u
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
variable {k : Type u} [CommRing k]
variable {C D E F : Type u} [Category.{u} C] [Category.{u} D]
  [Category.{u} E] [Category.{u} F]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  [Preadditive E] [Linear k E] [Supercategory k E]
  [Preadditive F] [Linear k F] [Supercategory k F]
variable (J : C ⥤ D) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
variable (K : D ⥤ E) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
variable (L : E ⥤ F) [L.Additive] [L.Linear k] [IsSuperfunctor k L]

/-- Both flattening trees compose the three kernel arrows in the same order. -/
theorem compForward_assoc_tensor (M : Superfunctor k C (SVec k))
    (v : C) (w : D) (z : E) (t : F)
    (g : L.obj z ⟶ t) (h : K.obj w ⟶ z) (a : J.obj v ⟶ w) (m : M.obj v) :
    compForward (J ⋙ K) L M t
      (mapComponent L (M := induced K (induced J M)) (N := induced (J ⋙ K) M)
        ((inductionComp J K).hom.app M) 0 t
        (tensor L (induced K (induced J M)).toFunctor z g
          (tensor K (induced J M).toFunctor w h (tensor J M.toFunctor v a m)))) =
    compForward J (K ⋙ L) M t
      (compForward K L (induced J M) t
        (tensor L (induced K (induced J M)).toFunctor z g
          (tensor K (induced J M).toFunctor w h (tensor J M.toFunctor v a m)))) := by
  have hm := mapComponent_tensor L (M := induced K (induced J M))
    (N := induced (J ⋙ K) M) ((inductionComp J K).hom.app M) 0 t z g
    (tensor K (induced J M).toFunctor w h (tensor J M.toFunctor v a m))
  have hc := congrArg (compForward (J ⋙ K) L M t) hm
  simp only [twist_zero] at hc
  have hi := congrArg
    (fun x : Obj (J ⋙ K) M.toFunctor z => compForward (J ⋙ K) L M t
      (tensor L (induced (J ⋙ K) M).toFunctor z g x))
    (inductionComp_hom_tensor J K M v w z h a m)
  have hr := congrArg (compForward J (K ⋙ L) M t)
    (compForward_tensor K L (induced J M) w z t g h (tensor J M.toFunctor v a m))
  have he : tensor ((J ⋙ K) ⋙ L) M.toFunctor v (L.map (K.map a ≫ h) ≫ g) m =
      tensor (J ⋙ (K ⋙ L)) M.toFunctor v ((K ⋙ L).map a ≫ (L.map h ≫ g)) m := by
    simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
    rfl
  have hl := compForward_tensor (J ⋙ K) L M v z t g (K.map a ≫ h) m
  have hrr := compForward_tensor J (K ⋙ L) M v w t (L.map h ≫ g) a m
  calc
    _ = compForward (J ⋙ K) L M t
        (tensor L (induced (J ⋙ K) M).toFunctor z g
          (((inductionComp J K).hom.app M).app 0 z
            (tensor K (induced J M).toFunctor w h (tensor J M.toFunctor v a m)))) := hc
    _ = compForward (J ⋙ K) L M t
        (tensor L (induced (J ⋙ K) M).toFunctor z g
          (tensor (J ⋙ K) M.toFunctor v (K.map a ≫ h) m)) := hi
    _ = tensor ((J ⋙ K) ⋙ L) M.toFunctor v (L.map (K.map a ≫ h) ≫ g) m := hl
    _ = tensor (J ⋙ (K ⋙ L)) M.toFunctor v ((K ⋙ L).map a ≫ (L.map h ≫ g)) m := he
    _ = compForward J (K ⋙ L) M t
        (tensor (K ⋙ L) (induced J M).toFunctor w (L.map h ≫ g)
          (tensor J M.toFunctor v a m)) := hrr.symm
    _ = _ := hr.symm

omit [Supercategory k F] [L.Additive] [L.Linear k] [IsSuperfunctor k L] in
theorem triple_hom_ext (M : Superfunctor k C (SVec k)) (t : F)
    {V : Type u} [AddCommGroup V] [Module k V]
    {a b : Obj L (induced K (induced J M)).toFunctor t →ₗ[k] V}
    (hab : ∀ (v : C) (w : D) (z : E) (g : L.obj z ⟶ t)
      (h : K.obj w ⟶ z) (f : J.obj v ⟶ w) (m : M.obj v),
      a (tensor L (induced K (induced J M)).toFunctor z g
        (tensor K (induced J M).toFunctor w h (tensor J M.toFunctor v f m))) =
      b (tensor L (induced K (induced J M)).toFunctor z g
        (tensor K (induced J M).toFunctor w h (tensor J M.toFunctor v f m)))) : a = b := by
  apply hom_ext
  intro z g x
  let ins : Obj K (induced J M).toFunctor z →ₗ[k]
      Obj L (induced K (induced J M)).toFunctor t :=
    inclusion L (induced K (induced J M)).toFunctor t z ∘ₗ
      TensorProduct.mk k (L.obj z ⟶ t) ((induced K (induced J M)).obj z) g
  have h : a ∘ₗ ins = b ∘ₗ ins := by
    apply nested_hom_ext J K M z
    intro v w h f m
    exact hab v w z g h f m
  exact congrArg (fun f => f x) h

/-- Associativity of flattening as linear maps on arbitrary induced modules. -/
theorem compForward_assoc (M : Superfunctor k C (SVec k)) (t : F) :
    compForward (J ⋙ K) L M t ∘ₗ
        mapComponent L (M := induced K (induced J M)) (N := induced (J ⋙ K) M)
        ((inductionComp J K).hom.app M) 0 t =
      compForward J (K ⋙ L) M t ∘ₗ compForward K L (induced J M) t := by
  apply triple_hom_ext J K L M t
  intro v w z g h a m
  exact compForward_assoc_tensor J K L M v w z t g h a m

end OddMath.QuiverHecke.ELVOld.BalancedInduction
