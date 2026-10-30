import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumRepresentable

/-! # Graded coordinates of morphisms between content representables

Covariant representables reverse the representing arrow. Each parity component
precomposes with that arrow and twists the argument by its total parity.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.ContentYoneda
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I)
variable {v w : ContentCategory D Sc cutoff N β}

def component (f : w ⟶ v) (p : ZMod 2) (z : ContentCategory D Sc cutoff N β) :
    (v ⟶ z) →ₗ[k] (w ⟶ z) := by
  let fp : w ⟶ v := proj k p f
  exact {
    toFun := fun h => fp ≫ twist k p h
    map_add' := fun h h' => by rw [map_add, Preadditive.comp_add]
    map_smul' := fun r h => by rw [map_smul, Linear.comp_smul]; rfl }

def fromArrow (f : w ⟶ v) : contentRepresentable D Sc cutoff N β v ⟶ contentRepresentable D Sc cutoff N β w :=
  Superfunctor.homMk {
    app := component D Sc cutoff N β f
    app_mem := by
      intro p z
      apply SVec.mem_parityHom_of_apply_mem
      intro q h hh
      change h ∈ (contentHomSpace D Sc cutoff N β v z).part q at hh
      change proj k p f ≫ twist k p h ∈ (contentHomSpace D Sc cutoff N β w z).part (q + p)
      rw [contentHomSpace_part] at hh ⊢
      change proj k p f ≫ twist k p h ∈ parity (R := k) w z (q + p)
      rw [add_comm q p]
      exact comp_mem (proj_mem p f) (twist_mem p hh)
    naturality := by
      intro p z t q a ha
      apply LinearMap.ext
      intro h
      change v ⟶ z at h
      change proj k p f ≫ twist k p (h ≫ a) =
        koszulSign p q • ((proj k p f ≫ twist k p h) ≫ a)
      rw [twist_comp, twist_of_mem p ha, Linear.comp_smul,
        Linear.comp_smul, koszulSign_smul (R := k), Category.assoc] }

/-- A component with its content-Hom endpoints exposed. -/
def componentMap (t : contentRepresentable D Sc cutoff N β v ⟶
    contentRepresentable D Sc cutoff N β w) (p : ZMod 2)
    (z : ContentCategory D Sc cutoff N β) : (v ⟶ z) →ₗ[k] (w ⟶ z) := t.app p z

def evaluate (t : contentRepresentable D Sc cutoff N β v ⟶
    contentRepresentable D Sc cutoff N β w) : w ⟶ v :=
  componentMap D Sc cutoff N β t 0 v (𝟙 v) + componentMap D Sc cutoff N β t 1 v (𝟙 v)

theorem evaluate_part (t : contentRepresentable D Sc cutoff N β v ⟶
    contentRepresentable D Sc cutoff N β w) (p : ZMod 2) :
    componentMap D Sc cutoff N β t p v (𝟙 v) ∈ parity (R := k) w v p := by
  have hi : (𝟙 v : v ⟶ v) ∈ (contentHomSpace D Sc cutoff N β v v).part 0 := by
    rw [contentHomSpace_part]; exact id_mem v
  have h := SVec.apply_mem_part (t.app_mem p v) hi
  change componentMap D Sc cutoff N β t p v (𝟙 v) ∈ (contentHomSpace D Sc cutoff N β w v).part (0 + p) at h
  rw [zero_add, contentHomSpace_part] at h
  exact h

@[simp] theorem evaluate_fromArrow (f : w ⟶ v) :
    evaluate D Sc cutoff N β (fromArrow D Sc cutoff N β f) = f := by
  change (proj k 0 f ≫ twist k 0 (𝟙 v)) + (proj k 1 f ≫ twist k 1 (𝟙 v)) = f
  simp only [twist_id, Category.comp_id, proj_add_proj]

theorem app_formula (t : contentRepresentable D Sc cutoff N β v ⟶
    contentRepresentable D Sc cutoff N β w) (p : ZMod 2)
    (z : ContentCategory D Sc cutoff N β) (h : v ⟶ z) :
    componentMap D Sc cutoff N β t p z h = componentMap D Sc cutoff N β t p v (𝟙 v) ≫ twist k p h := by
  refine induction_on (R := k) h ?_ ?_ ?_
  · simp
  · intro q h hh
    have hn := congrArg (fun a => a (𝟙 v)) (t.naturality p h hh)
    change componentMap D Sc cutoff N β t p z (𝟙 v ≫ h) = koszulSign p q • (componentMap D Sc cutoff N β t p v (𝟙 v) ≫ h) at hn
    rw [Category.id_comp, koszulSign_smul (R := k)] at hn
    rw [twist_of_mem p hh, Linear.comp_smul]
    exact hn
  · intro a b ha hb
    rw [map_add, map_add, Preadditive.comp_add, ha, hb]

theorem fromArrow_evaluate (t : contentRepresentable D Sc cutoff N β v ⟶
    contentRepresentable D Sc cutoff N β w) :
    fromArrow D Sc cutoff N β (evaluate D Sc cutoff N β t) = t := by
  apply Superfunctor.hom_ext
  intro p z
  apply LinearMap.ext
  intro h
  change v ⟶ z at h
  change proj k p (componentMap D Sc cutoff N β t 0 v (𝟙 v) + componentMap D Sc cutoff N β t 1 v (𝟙 v)) ≫ twist k p h = componentMap D Sc cutoff N β t p z h
  rw [app_formula D Sc cutoff N β t p z h, map_add]
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [proj_of_mem (evaluate_part D Sc cutoff N β t 0),
      proj_of_mem_ne (evaluate_part D Sc cutoff N β t 1) (by decide), add_zero]
  · rw [proj_of_mem_ne (evaluate_part D Sc cutoff N β t 0) (by decide),
      proj_of_mem (evaluate_part D Sc cutoff N β t 1), zero_add]
/-- Evaluation at the identity, with the explicitly constructed inverse. -/
def homEquiv : (contentRepresentable D Sc cutoff N β v ⟶
    contentRepresentable D Sc cutoff N β w) ≃ₗ[k] (w ⟶ v) where
  toFun := evaluate D Sc cutoff N β
  invFun := fromArrow D Sc cutoff N β
  left_inv := fromArrow_evaluate D Sc cutoff N β
  right_inv := evaluate_fromArrow D Sc cutoff N β
  map_add' t s := by
    change (componentMap D Sc cutoff N β t 0 v (𝟙 v) + componentMap D Sc cutoff N β s 0 v (𝟙 v)) +
      (componentMap D Sc cutoff N β t 1 v (𝟙 v) + componentMap D Sc cutoff N β s 1 v (𝟙 v)) = _
    change _ = (componentMap D Sc cutoff N β t 0 v (𝟙 v) + componentMap D Sc cutoff N β t 1 v (𝟙 v)) +
      (componentMap D Sc cutoff N β s 0 v (𝟙 v) + componentMap D Sc cutoff N β s 1 v (𝟙 v))
    abel
  map_smul' r t := by
    change r • componentMap D Sc cutoff N β t 0 v (𝟙 v) +
      r • componentMap D Sc cutoff N β t 1 v (𝟙 v) =
      r • (componentMap D Sc cutoff N β t 0 v (𝟙 v) + componentMap D Sc cutoff N β t 1 v (𝟙 v))
    exact (smul_add _ _ _).symm

/-- Evaluation retains both homogeneous parts of the full coefficient grading. -/
theorem evaluate_proj (t : contentRepresentable D Sc cutoff N β v ⟶
    contentRepresentable D Sc cutoff N β w) (p : ZMod 2) :
    evaluate D Sc cutoff N β (proj k p t) = proj k p (evaluate D Sc cutoff N β t) := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · change (proj k 0 t).app 0 v (𝟙 v) + (proj k 0 t).app 1 v (𝟙 v) = _
    simp only [Superfunctor.proj_app, ite_true, one_ne_zero, ite_false]
    change componentMap D Sc cutoff N β t 0 v (𝟙 v) + 0 =
      proj k 0 (componentMap D Sc cutoff N β t 0 v (𝟙 v) + componentMap D Sc cutoff N β t 1 v (𝟙 v))
    rw [map_add, proj_of_mem (evaluate_part D Sc cutoff N β t 0),
      proj_of_mem_ne (evaluate_part D Sc cutoff N β t 1) (by decide)]
  · change (proj k 1 t).app 0 v (𝟙 v) + (proj k 1 t).app 1 v (𝟙 v) = _
    simp only [Superfunctor.proj_app, zero_ne_one, ite_false, ite_true]
    change 0 + componentMap D Sc cutoff N β t 1 v (𝟙 v) =
      proj k 1 (componentMap D Sc cutoff N β t 0 v (𝟙 v) + componentMap D Sc cutoff N β t 1 v (𝟙 v))
    rw [map_add, proj_of_mem_ne (evaluate_part D Sc cutoff N β t 0) (by decide),
      proj_of_mem (evaluate_part D Sc cutoff N β t 1)]

/-- The parity-r composition coordinate is the super-opposite convolution.
In particular the odd-odd term has a minus sign, not the ordinary opposite law. -/
theorem composition_component {z : ContentCategory D Sc cutoff N β}
    (s : contentRepresentable D Sc cutoff N β v ⟶ contentRepresentable D Sc cutoff N β w)
    (t : contentRepresentable D Sc cutoff N β w ⟶ contentRepresentable D Sc cutoff N β z)
    (p : ZMod 2) :
    componentMap D Sc cutoff N β (s ≫ t) p v (𝟙 v) =
      componentMap D Sc cutoff N β t p w (𝟙 w) ≫ componentMap D Sc cutoff N β s 0 v (𝟙 v) +
      sign k (p + 1) • (componentMap D Sc cutoff N β t (p + 1) w (𝟙 w) ≫
        componentMap D Sc cutoff N β s 1 v (𝟙 v)) := by
  change componentMap D Sc cutoff N β t p v (componentMap D Sc cutoff N β s 0 v (𝟙 v)) +
    componentMap D Sc cutoff N β t (p + 1) v (componentMap D Sc cutoff N β s 1 v (𝟙 v)) = _
  rw [app_formula D Sc cutoff N β t p v, app_formula D Sc cutoff N β t (p + 1) v,
    twist_of_mem p (evaluate_part D Sc cutoff N β s 0),
    twist_of_mem (p + 1) (evaluate_part D Sc cutoff N β s 1)]
  simp only [mul_zero, mul_one, sign_zero, one_smul, Linear.comp_smul]

end OddMath.QuiverHecke.ELVOld.ContentYoneda
