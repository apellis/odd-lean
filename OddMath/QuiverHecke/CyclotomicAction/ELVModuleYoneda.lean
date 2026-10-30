import OddMath.QuiverHecke.CyclotomicAction.ELVContentYoneda

/-! # Evaluation of content representables on supermodules

The enriched Yoneda equivalence retains both parity components and applies to
any exact-content supermodule. Its inverse uses the total-parity twist.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.ModuleYoneda
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I)
variable {v : ContentCategory D Sc cutoff N β} (M : ContentModules D Sc cutoff N β)

def component (m : M.obj v) (p : ZMod 2) (z : ContentCategory D Sc cutoff N β) :
    (v ⟶ z) →ₗ[k] M.obj z where
  toFun h := M.map (twist k p h) ((M.obj v).proj p m)
  map_add' h h' := by
    simp only [map_add, Superfunctor.map, Functor.map_add, SVec.add_apply]
  map_smul' r h := by
    simp only [map_smul, Superfunctor.map, Functor.map_smul, SVec.smul_apply,
      RingHom.id_apply]

def fromElement (m : M.obj v) : contentRepresentable D Sc cutoff N β v ⟶ M :=
  Superfunctor.homMk {
    app := component D Sc cutoff N β M m
    app_mem := by
      intro p z
      apply SVec.mem_parityHom_of_apply_mem
      intro q h hh
      change h ∈ (contentHomSpace D Sc cutoff N β v z).part q at hh
      rw [contentHomSpace_part] at hh
      change M.map (twist k p h) ((M.obj v).proj p m) ∈ (M.obj z).part (q + p)
      rw [add_comm q p]
      exact SVec.apply_mem_part (M.map_mem (twist_mem p hh)) ((M.obj v).proj_mem_part p m)
    naturality := by
      intro p z t q a ha
      apply LinearMap.ext
      intro h
      change v ⟶ z at h
      change M.map (twist k p (h ≫ a)) ((M.obj v).proj p m) =
        koszulSign p q • M.map a (M.map (twist k p h) ((M.obj v).proj p m))
      rw [twist_comp, twist_of_mem p ha, Linear.comp_smul, koszulSign_smul (R := k)]
      simp only [Superfunctor.map, Functor.map_smul, Functor.map_comp, SVec.smul_apply,
        SVec.comp_apply] }

def componentMap (t : contentRepresentable D Sc cutoff N β v ⟶ M) (p : ZMod 2)
    (z : ContentCategory D Sc cutoff N β) : (v ⟶ z) →ₗ[k] M.obj z := t.app p z

def evaluate (t : contentRepresentable D Sc cutoff N β v ⟶ M) : M.obj v :=
  componentMap D Sc cutoff N β M t 0 v (𝟙 v) + componentMap D Sc cutoff N β M t 1 v (𝟙 v)

theorem evaluate_part (t : contentRepresentable D Sc cutoff N β v ⟶ M) (p : ZMod 2) :
    componentMap D Sc cutoff N β M t p v (𝟙 v) ∈ (M.obj v).part p := by
  have hi : (𝟙 v : v ⟶ v) ∈ (contentHomSpace D Sc cutoff N β v v).part 0 := by
    rw [contentHomSpace_part]; exact id_mem v
  have hp := SVec.apply_mem_part (t.app_mem p v) hi
  rw [zero_add] at hp
  exact hp

@[simp] theorem evaluate_fromElement (m : M.obj v) :
    evaluate D Sc cutoff N β M (fromElement D Sc cutoff N β M m) = m := by
  change M.map (twist k 0 (𝟙 v)) ((M.obj v).proj 0 m) +
    M.map (twist k 1 (𝟙 v)) ((M.obj v).proj 1 m) = m
  rw [twist_id, twist_id]
  have hi : M.map (𝟙 v : v ⟶ v) = 𝟙 (M.obj v) := M.toFunctor.map_id v
  rw [hi]
  exact (M.obj v).proj_apply_add m

theorem app_formula (t : contentRepresentable D Sc cutoff N β v ⟶ M) (p : ZMod 2)
    (z : ContentCategory D Sc cutoff N β) (h : v ⟶ z) :
    componentMap D Sc cutoff N β M t p z h =
      M.map (twist k p h) (componentMap D Sc cutoff N β M t p v (𝟙 v)) := by
  refine induction_on (R := k) h ?_ ?_ ?_
  · simp [Superfunctor.map]
  · intro q h hh
    have hn := congrArg (fun a => a (𝟙 v)) (t.naturality p h hh)
    change componentMap D Sc cutoff N β M t p z (𝟙 v ≫ h) =
      koszulSign p q • M.map h (componentMap D Sc cutoff N β M t p v (𝟙 v)) at hn
    rw [Category.id_comp, koszulSign_smul (R := k)] at hn
    rw [twist_of_mem p hh]
    simpa only [Superfunctor.map, Functor.map_smul, SVec.smul_apply] using hn
  · intro a b ha hb
    simp only [map_add, Superfunctor.map, Functor.map_add, SVec.add_apply, ha, hb]

theorem evaluate_component (t : contentRepresentable D Sc cutoff N β v ⟶ M) (p : ZMod 2) :
    (M.obj v).proj p (evaluate D Sc cutoff N β M t) =
      componentMap D Sc cutoff N β M t p v (𝟙 v) := by
  rw [evaluate, map_add, SVec.proj_apply_of_mem_part _ (evaluate_part D Sc cutoff N β M t 0),
    SVec.proj_apply_of_mem_part _ (evaluate_part D Sc cutoff N β M t 1)]
  rcases parity_eq_zero_or_one p with rfl | rfl <;> simp

theorem fromElement_evaluate (t : contentRepresentable D Sc cutoff N β v ⟶ M) :
    fromElement D Sc cutoff N β M (evaluate D Sc cutoff N β M t) = t := by
  apply Superfunctor.hom_ext
  intro p z
  apply LinearMap.ext
  intro h
  change v ⟶ z at h
  change M.map (twist k p h) ((M.obj v).proj p (evaluate D Sc cutoff N β M t)) =
    componentMap D Sc cutoff N β M t p z h
  rw [evaluate_component]
  exact (app_formula D Sc cutoff N β M t p z h).symm

/-- Enriched Yoneda for every exact-content supermodule. -/
def homEquiv : (contentRepresentable D Sc cutoff N β v ⟶ M) ≃ₗ[k] M.obj v where
  toFun := evaluate D Sc cutoff N β M
  invFun := fromElement D Sc cutoff N β M
  left_inv := fromElement_evaluate D Sc cutoff N β M
  right_inv := evaluate_fromElement D Sc cutoff N β M
  map_add' t s := by
    change (componentMap D Sc cutoff N β M t 0 v (𝟙 v) + componentMap D Sc cutoff N β M s 0 v (𝟙 v)) +
      (componentMap D Sc cutoff N β M t 1 v (𝟙 v) + componentMap D Sc cutoff N β M s 1 v (𝟙 v)) = _
    change _ = (componentMap D Sc cutoff N β M t 0 v (𝟙 v) + componentMap D Sc cutoff N β M t 1 v (𝟙 v)) +
      (componentMap D Sc cutoff N β M s 0 v (𝟙 v) + componentMap D Sc cutoff N β M s 1 v (𝟙 v))
    abel
  map_smul' r t := by
    change r • componentMap D Sc cutoff N β M t 0 v (𝟙 v) +
      r • componentMap D Sc cutoff N β M t 1 v (𝟙 v) =
      r • (componentMap D Sc cutoff N β M t 0 v (𝟙 v) + componentMap D Sc cutoff N β M t 1 v (𝟙 v))
    exact (smul_add _ _ _).symm

/-- Evaluation preserves both parity projections. -/
theorem evaluate_proj (t : contentRepresentable D Sc cutoff N β v ⟶ M) (p : ZMod 2) :
    evaluate D Sc cutoff N β M (proj k p t) = (M.obj v).proj p (evaluate D Sc cutoff N β M t) := by
  rw [evaluate_component]
  rcases parity_eq_zero_or_one p with rfl | rfl
  · change (proj k 0 t).app 0 v (𝟙 v) + (proj k 0 t).app 1 v (𝟙 v) = _
    simp only [Superfunctor.proj_app, ite_true, one_ne_zero, ite_false]
    exact add_zero _
  · change (proj k 1 t).app 0 v (𝟙 v) + (proj k 1 t).app 1 v (𝟙 v) = _
    simp only [Superfunctor.proj_app, ite_true, zero_ne_one, ite_false]
    exact zero_add _

end OddMath.QuiverHecke.ELVOld.ModuleYoneda
