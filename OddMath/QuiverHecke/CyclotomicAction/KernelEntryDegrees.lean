import OddMath.QuiverHecke.CyclotomicAction.ContentTriple
import OddMath.QuiverHecke.CyclotomicAction.CategoryGrading
import OddMath.QuiverHecke.CyclotomicAction.AppendContent
import OddMath.QuiverHecke.CyclotomicAction.ContentModules
import OddMath.QuiverHecke.CyclotomicAction.IndRes
import OddMath.QuiverHecke.CyclotomicAction.KernelMatrixEvaluation
import OddMath.Algebra.IntegerMatrixGrading

/-!
# Kernel entry degrees

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

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
end

end

section

/-! # The supercentre of the content-module category

Evaluation on representables reconstructs a source central family from every
supernatural endomorphism of the module identity. The two Koszul signs in
homogeneous Yoneda naturality cancel over any ordinary commutative ring.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.ModuleCentre
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I)

abbrev Centre := Superfunctor.id k (ContentModules D Sc cutoff N β) ⟶
  Superfunctor.id k (ContentModules D Sc cutoff N β)

theorem total_of_mem {M L : ContentModules D Sc cutoff N β} {t : M ⟶ L}
    {p : ZMod 2} (ht : t ∈ parity (R := k) M L p) (v : ContentCategory D Sc cutoff N β) :
    t.total v = t.app p v := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · change t.app 0 v + t.app 1 v = _
    rw [Superfunctor.app_eq_zero_of_mem ht (q := 1) (by decide), add_zero]
  · change t.app 0 v + t.app 1 v = _
    rw [Superfunctor.app_eq_zero_of_mem ht (q := 0) (by decide), zero_add]

def moduleMap (η : Centre D Sc cutoff N β) (p : ZMod 2)
    (M : ContentModules D Sc cutoff N β) : M ⟶ M := η.app p M

theorem moduleMap_mem (η : Centre D Sc cutoff N β) (p : ZMod 2)
    (M : ContentModules D Sc cutoff N β) :
    moduleMap D Sc cutoff N β η p M ∈ parity (R := k) M M p := η.app_mem p M

theorem total_zsmul {M L : ContentModules D Sc cutoff N β} (t : M ⟶ L)
    (r : ℤ) (v : ContentCategory D Sc cutoff N β) :
    (r • t).total v = r • t.total v := by
  change r • t.app 0 v + r • t.app 1 v = r • (t.app 0 v + t.app 1 v)
  exact (smul_add _ _ _).symm

def coefficient (η : Centre D Sc cutoff N β) (p : ZMod 2)
    (v : ContentCategory D Sc cutoff N β) : v ⟶ v :=
  ContentYoneda.componentMap D Sc cutoff N β (moduleMap D Sc cutoff N β η p (contentRepresentable D Sc cutoff N β v)) p v (𝟙 v)

theorem coefficient_mem (η : Centre D Sc cutoff N β) (p : ZMod 2)
    (v : ContentCategory D Sc cutoff N β) :
    coefficient D Sc cutoff N β η p v ∈ parity (R := k) v v p :=
  ContentYoneda.evaluate_part D Sc cutoff N β _ p

theorem fromElement_mem (M : ContentModules D Sc cutoff N β)
    {v : ContentCategory D Sc cutoff N β} {q : ZMod 2} {m : M.obj v}
    (hm : m ∈ (M.obj v).part q) :
    ModuleYoneda.fromElement D Sc cutoff N β M m ∈ parity (R := k) _ _ q := by
  have he : proj k q (ModuleYoneda.fromElement D Sc cutoff N β M m) =
      ModuleYoneda.fromElement D Sc cutoff N β M m := by
    apply (ModuleYoneda.homEquiv D Sc cutoff N β M).injective
    change ModuleYoneda.evaluate D Sc cutoff N β M (proj k q _) =
      ModuleYoneda.evaluate D Sc cutoff N β M _
    rw [ModuleYoneda.evaluate_proj, ModuleYoneda.evaluate_fromElement,
      (M.obj v).mem_part_iff.mp hm]
  rw [← he]
  exact proj_mem q _

/-- The supernatural sign and the twist sign cancel, including odd against odd. -/
theorem action_of_mem (η : Centre D Sc cutoff N β) (p : ZMod 2)
    (M : ContentModules D Sc cutoff N β) (v : ContentCategory D Sc cutoff N β)
    {q : ZMod 2} {m : M.obj v} (hm : m ∈ (M.obj v).part q) :
    (moduleMap D Sc cutoff N β η p M).app p v m = M.map (coefficient D Sc cutoff N β η p v) m := by
  let t := ModuleYoneda.fromElement D Sc cutoff N β M m
  have ht := fromElement_mem D Sc cutoff N β M hm
  have hn0 : t ≫ moduleMap D Sc cutoff N β η p M =
      koszulSign p q • (moduleMap D Sc cutoff N β η p (contentRepresentable D Sc cutoff N β v) ≫ t) :=
    η.naturality p t ht
  have hn := congrArg (fun s => s.total v (𝟙 v)) hn0
  rw [total_zsmul] at hn
  simp only [Superfunctor.comp_total] at hn
  rw [total_of_mem D Sc cutoff N β (moduleMap_mem D Sc cutoff N β η p M),
    total_of_mem D Sc cutoff N β (moduleMap_mem D Sc cutoff N β η p (contentRepresentable D Sc cutoff N β v)),
    total_of_mem D Sc cutoff N β ht] at hn
  change (moduleMap D Sc cutoff N β η p M).app p v
      (M.map (twist k q (𝟙 v)) ((M.obj v).proj q m)) =
    koszulSign p q • M.map (twist k q (coefficient D Sc cutoff N β η p v))
      ((M.obj v).proj q m) at hn
  rw [(M.obj v).mem_part_iff.mp hm, twist_id] at hn
  have hi : M.map (𝟙 v : v ⟶ v) = 𝟙 (M.obj v) := M.toFunctor.map_id v
  rw [hi, SVec.id_apply, twist_of_mem q (coefficient_mem D Sc cutoff N β η p v)] at hn
  rw [koszulSign_smul (R := k)] at hn
  simp only [Superfunctor.map, Functor.map_smul, SVec.smul_apply] at hn
  rw [mul_comm q p, smul_smul, Supercategory.sign_mul_self, one_smul] at hn
  exact hn

/-- Every module component is the action of its reconstructed coefficient. -/
theorem action (η : Centre D Sc cutoff N β) (p : ZMod 2)
    (M : ContentModules D Sc cutoff N β) (v : ContentCategory D Sc cutoff N β)
    (m : M.obj v) :
    (moduleMap D Sc cutoff N β η p M).app p v m = M.map (coefficient D Sc cutoff N β η p v) m := by
  conv_lhs => rw [← (M.obj v).proj_apply_add m]
  rw [map_add, action_of_mem D Sc cutoff N β η p M v ((M.obj v).proj_mem_part 0 m),
    action_of_mem D Sc cutoff N β η p M v ((M.obj v).proj_mem_part 1 m),
    ← map_add, SVec.proj_apply_add]

/-- The recovered family is supernatural on the entire content source. -/
theorem coefficient_naturality (η : Centre D Sc cutoff N β) (p : ZMod 2)
    {v w : ContentCategory D Sc cutoff N β} {q : ZMod 2} (f : v ⟶ w)
    (hf : f ∈ parity (R := k) v w q) :
    f ≫ coefficient D Sc cutoff N β η p w =
      koszulSign p q • (coefficient D Sc cutoff N β η p v ≫ f) := by
  have ha := action D Sc cutoff N β η p (contentRepresentable D Sc cutoff N β v) w f
  change ContentYoneda.componentMap D Sc cutoff N β
      (moduleMap D Sc cutoff N β η p (contentRepresentable D Sc cutoff N β v)) p w f =
      f ≫ coefficient D Sc cutoff N β η p w at ha
  rw [ContentYoneda.app_formula] at ha
  change coefficient D Sc cutoff N β η p v ≫ twist k p f =
    f ≫ coefficient D Sc cutoff N β η p w at ha
  rw [twist_of_mem p hf, Linear.comp_smul] at ha
  rw [koszulSign_smul (R := k)]
  exact ha.symm

/-- Reconstruct a source-supercentral family by evaluating on representables. -/
def reconstruct (η : Centre D Sc cutoff N β) : ContentCoefficient D Sc cutoff N β :=
  Superfunctor.homMk {
    app := coefficient D Sc cutoff N β η
    app_mem := coefficient_mem D Sc cutoff N β η
    naturality := fun p _ _ _ f hf => coefficient_naturality D Sc cutoff N β η p f hf }

/-- The reconstructed family realizes the original module-centre transformation. -/
theorem realize_reconstruct (η : Centre D Sc cutoff N β) :
    contentRealize D Sc cutoff N β (reconstruct D Sc cutoff N β η) = η := by
  apply Superfunctor.hom_ext
  intro p M
  change Superfunctor.whiskerRight (proj k p (reconstruct D Sc cutoff N β η)) M =
    moduleMap D Sc cutoff N β η p M
  apply Superfunctor.hom_ext
  intro q v
  change M.map ((proj k p (reconstruct D Sc cutoff N β η)).app q v) =
    (moduleMap D Sc cutoff N β η p M).app q v
  rw [Superfunctor.proj_app]
  by_cases h : q = p
  · subst q
    rw [ite_eq_left rfl]
    apply LinearMap.ext
    intro m
    exact (action D Sc cutoff N β η p M v m).symm
  · rw [ite_eq_right h, Superfunctor.app_eq_zero_of_mem (moduleMap_mem D Sc cutoff N β η p M) h]
    exact M.toFunctor.map_zero v v

end OddMath.QuiverHecke.ELVOld.ModuleCentre
end

end

section

/-! # Integer degrees of the chosen old append generators

The represented finite matrix uses the prescribed appended dot and
equal-colour crossing. Their degrees here are inherited from the source
diagrams, independently of their super parity.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory GradedSupercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

/-- The prescribed last dot has integer degree `2 dᵢ`. -/
theorem oldAppendDotComponent_degree (i : I) (s : OldCategory D Sc cutoff) :
    CyclotomicCrossingTensor.oldAppendDotComponent D Sc cutoff i s ∈
      oldDegree D sy Sc hc cutoff (s.word ++ [i]) (s.word ++ [i]) (2 * sy.d i) := by
  apply Submodule.mem_map_of_mem
  apply appendComponent_mem_degree
  unfold dotE genE
  split_ifs
  · apply Presentation.diag_mem_homDeg'
    rw [degree_gdeg_mkD]
    simp [pl, PG.ld, gdeg]
  · exact Submodule.zero_mem _

/-- The prescribed last equal crossing has integer degree `-2 dᵢ`. -/
theorem equalCrossComponent_degree (i : I) (s : OldCategory D Sc cutoff) :
    CyclotomicCrossingTensor.equalCrossComponent D Sc cutoff i s ∈
      oldDegree D sy Sc hc cutoff ((s.word ++ [i]) ++ [i]) ((s.word ++ [i]) ++ [i])
        (-2 * sy.d i) := by
  apply Submodule.mem_map_of_mem
  apply affineUnit_mem_degree D Sc cutoff sy hc
  unfold crossLast cl
  apply Presentation.diag_mem_homDeg'
  rw [degree_gdeg_mkD]
  simp [pl, PG.ld, gdeg, SKM.Datum.d_self]
  ring

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Integer degrees of the prescribed represented matrix entries

The forward finite matrix uses the literal signed mate, ordinary dot/cap
rows and unscaled unit/dot columns. Their degrees are proved on the
intrinsic represented Hom-tensor grading; no grading of arbitrary
module Homs or inverse-degree premise is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory GradedSupercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
private theorem oldComp_degree {v t w : OldCategory D Sc cutoff} {m n : ℤ}
    (f : v ⟶ t) (g : t ⟶ w)
    (hf : f ∈ oldDegree D sy Sc hc cutoff v.word t.word m)
    (hg : g ∈ oldDegree D sy Sc hc cutoff t.word w.word n) :
    f ≫ g ∈ oldDegree D sy Sc hc cutoff v.word w.word (m + n) := by
  obtain ⟨a, ha, rfl⟩ := hf
  obtain ⟨b, hb, rfl⟩ := hg
  let := elvHomGrading D sy Sc hc cutoff
  exact Submodule.mem_map_of_mem (comp_mem_degree ha hb)

private theorem oldTwist_degree {v t : OldCategory D Sc cutoff} {n : ℤ}
    (p : ZMod 2) (f : v ⟶ t) (hf : f ∈ oldDegree D sy Sc hc cutoff v.word t.word n) :
    twist k p f ∈ oldDegree D sy Sc hc cutoff v.word t.word n := by
  rw [twist_apply, oldCategory_proj, oldCategory_proj]
  exact Submodule.add_mem _ (oldProj_mem_oldDegree D sy Sc hc cutoff 0 hf)
    (Submodule.smul_mem _ _ (oldProj_mem_oldDegree D sy Sc hc cutoff 1 hf))

/-- The represented lower-loop degree is the sum of the two Hom degrees. -/
abbrev representedKernelDegree (i : I) (v t : OldCategory D Sc cutoff) (n : ℤ) :=
  letI := oldCategoryGradedSupercategory D Sc cutoff sy hc
  IndResKernel.integerDegree (k := k) (append D Sc cutoff i) v t n

/-- The chosen signed mate has degree `-2 dᵢ` on represented kernels. -/
theorem mateKernelComponent_degree (i : I) (v t : OldCategory D Sc cutoff)
    {n : ℤ} {x : IndResKernel.Component (k := k) (append D Sc cutoff i) v t}
    (hx : x ∈ representedKernelDegree D Sc cutoff sy hc i v t n) :
    mateKernelComponent D Sc cutoff i v t x ∈
      oldDegree D sy Sc hc cutoff (v.word ++ [i]) (t.word ++ [i]) (n - 2 * sy.d i) := by
  let := oldCategoryGradedSupercategory D Sc cutoff sy hc
  let : IsGradedSuperfunctor k (append D Sc cutoff i) := (oldAppendGraded D Sc cutoff sy hc i).isGraded
  refine ((IndResKernel.integerDegree_le_iff (append D Sc cutoff i) v t n
    ((oldDegree D sy Sc hc cutoff (v.word ++ [i]) (t.word ++ [i]) (n - 2 * sy.d i)).comap
      (mateKernelComponent D Sc cutoff i v t))).2 ?_) hx
  intro s q r hqr g hg b hb
  simp only [Submodule.mem_comap]
  rw [IndResKernel.componentTensor, mateKernelComponent_tensor]
  change g ∈ oldDegree D sy Sc hc cutoff ((append D Sc cutoff i).obj s).word t.word q at hg
  change b ∈ oldDegree D sy Sc hc cutoff v.word ((append D Sc cutoff i).obj s).word r at hb
  have hd := oldComp_degree D Sc cutoff sy hc
    ((append D Sc cutoff i).map b)
    (equalCrossComponent D Sc cutoff i s ≫ twist k (D.parity i) ((append D Sc cutoff i).map g))
    (oldAppend_mem_degree D Sc cutoff sy hc i hb)
    (oldComp_degree D Sc cutoff sy hc (equalCrossComponent D Sc cutoff i s)
      (twist k (D.parity i) ((append D Sc cutoff i).map g))
      (equalCrossComponent_degree D Sc cutoff sy hc i s)
      (oldTwist_degree D Sc cutoff sy hc (D.parity i) _ (oldAppend_mem_degree D Sc cutoff sy hc i hg)))
  have he : r + (-2 * sy.d i + q) = n - 2 * sy.d i := by omega
  simpa only [he] using (oldDegree D sy Sc hc cutoff (v.word ++ [i]) (t.word ++ [i])
    (r + (-2 * sy.d i + q))).neg_mem hd

set_option backward.dsimp.instances true in
/-- The chosen induction dot raises represented integer degree by `2 dᵢ`. -/
theorem dotKernelComponent_degree (i : I) (v t : OldCategory D Sc cutoff)
    {n : ℤ} {x : IndResKernel.Component (k := k) (append D Sc cutoff i) v t}
    (hx : x ∈ representedKernelDegree D Sc cutoff sy hc i v t n) :
    dotKernelComponent D Sc cutoff i v t x ∈
      representedKernelDegree D Sc cutoff sy hc i v t (n + 2 * sy.d i) := by
  let := oldCategoryGradedSupercategory D Sc cutoff sy hc
  let : IsGradedSuperfunctor k (append D Sc cutoff i) := (oldAppendGraded D Sc cutoff sy hc i).isGraded
  refine ((IndResKernel.integerDegree_le_iff (append D Sc cutoff i) v t n
    ((representedKernelDegree D Sc cutoff sy hc i v t (n + 2 * sy.d i)).comap
      (dotKernelComponent D Sc cutoff i v t))).2 ?_) hx
  intro s q r hqr g hg b hb
  simp only [Submodule.mem_comap]
  rw [IndResKernel.componentTensor, dotKernelComponent_tensor]
  change g ∈ oldDegree D sy Sc hc cutoff ((append D Sc cutoff i).obj s).word t.word q at hg
  have hnew : oldAppendDotComponent D Sc cutoff i s ≫ twist k (D.parity i) g ∈
      degree (R := k) ((append D Sc cutoff i).obj s) t (2 * sy.d i + q) := by
    change _ ∈ oldDegree D sy Sc hc cutoff ((append D Sc cutoff i).obj s).word t.word _
    exact oldComp_degree D Sc cutoff sy hc _ _ (oldAppendDotComponent_degree D Sc cutoff sy hc i s)
      (oldTwist_degree D Sc cutoff sy hc (D.parity i) g hg)
  have hd := IndResKernel.componentTensor_mem_integerDegree (append D Sc cutoff i) v t s
    (oldAppendDotComponent D Sc cutoff i s ≫ twist k (D.parity i) g) b hnew hb
  have he : 2 * sy.d i + q + r = n + 2 * sy.d i := by omega
  dsimp only [representedKernelDegree, IndResKernel.componentTensor,
    oldCategoryGradedSupercategory] at hd ⊢
  simpa only [he] using hd

/-- The actual dot powers have their prescribed multiple integer degree. -/
theorem dotKernelComponent_power_degree (i : I) (v t : OldCategory D Sc cutoff)
    (m : ℕ) {n : ℤ} {x : IndResKernel.Component (k := k) (append D Sc cutoff i) v t}
    (hx : x ∈ representedKernelDegree D Sc cutoff sy hc i v t n) :
    (dotKernelComponent D Sc cutoff i v t ^ m) x ∈
      representedKernelDegree D Sc cutoff sy hc i v t (n + 2 * sy.d i * m) := by
  let := oldCategoryGradedSupercategory D Sc cutoff sy hc
  induction m with
  | zero => simpa only [pow_zero, Module.End.one_apply, Nat.cast_zero, mul_zero, add_zero] using hx
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h := dotKernelComponent_degree D Sc cutoff sy hc i v t ih
    have he : n + 2 * sy.d i * (m : ℤ) + 2 * sy.d i = n + 2 * sy.d i * (m + 1 : ℕ) := by
      push_cast
      ring
    simpa only [he] using h

/-- The ordinary chosen counit has represented degree zero. -/
theorem counitKernelComponent_degree (i : I) (v t : OldCategory D Sc cutoff)
    {n : ℤ} {x : IndResKernel.Component (k := k) (append D Sc cutoff i) v t}
    (hx : x ∈ representedKernelDegree D Sc cutoff sy hc i v t n) :
    counitKernelComponent D Sc cutoff i v t x ∈ oldDegree D sy Sc hc cutoff v.word t.word n := by
  let := oldCategoryGradedSupercategory D Sc cutoff sy hc
  let : IsGradedSuperfunctor k (append D Sc cutoff i) := (oldAppendGraded D Sc cutoff sy hc i).isGraded
  refine ((IndResKernel.integerDegree_le_iff (append D Sc cutoff i) v t n
    ((oldDegree D sy Sc hc cutoff v.word t.word n).comap
      (counitKernelComponent D Sc cutoff i v t))).2 ?_) hx
  intro s q r hqr g hg b hb
  simp only [Submodule.mem_comap]
  rw [IndResKernel.componentTensor, counitKernelComponent_tensor]
  change g ∈ oldDegree D sy Sc hc cutoff ((append D Sc cutoff i).obj s).word t.word q at hg
  change b ∈ oldDegree D sy Sc hc cutoff v.word ((append D Sc cutoff i).obj s).word r at hb
  have hd := oldComp_degree D Sc cutoff sy hc b g hb hg
  have he : r + q = n := by omega
  simpa only [he] using hd

/-- Every actual ordinary dot/cap row has degree `2 dᵢ m`. -/
theorem capKernelComponent_degree (i : I) (v t : OldCategory D Sc cutoff)
    (m : ℕ) {n : ℤ} {x : IndResKernel.Component (k := k) (append D Sc cutoff i) v t}
    (hx : x ∈ representedKernelDegree D Sc cutoff sy hc i v t n) :
    capKernelComponent D Sc cutoff i m v t x ∈
      oldDegree D sy Sc hc cutoff v.word t.word (n + 2 * sy.d i * m) :=
  counitKernelComponent_degree D Sc cutoff sy hc i v t
    (dotKernelComponent_power_degree D Sc cutoff sy hc i v t m hx)

/-- Every actual unscaled unit/dot column has degree `2 dᵢ m`, including
its prescribed scalar sign and exponent zero. -/
theorem unitKernelComponent_degree (i : I) (v t : OldCategory D Sc cutoff)
    (m : ℕ) {n : ℤ} {b : v ⟶ t}
    (hb : b ∈ oldDegree D sy Sc hc cutoff v.word t.word n) :
    unitKernelComponent D Sc cutoff i m v t b ∈
      oldDegree D sy Sc hc cutoff (v.word ++ [i]) (t.word ++ [i]) (n + 2 * sy.d i * m) := by
  let := oldCategoryGradedSupercategory D Sc cutoff sy hc
  cases v with
  | mk v =>
    cases t with
    | mk t =>
      change inductionUnitDotColumn D Sc cutoff i v t m b ∈ _
      rw [inductionUnitDotColumn_comp]
      have hm : (ideal D Sc cutoff (t ++ [i]) (t ++ [i])).mkQ (appendMovingPower D Sc cutoff i t m) ∈
          oldDegree D sy Sc hc cutoff (t ++ [i]) (t ++ [i]) (2 * sy.d i * m) := by
        apply Submodule.mem_map_of_mem
        rw [appendMovingPower_whisker, ← appendSourcePower_whisker]
        exact appendSourcePower_mem_degree D Sc cutoff sy hc i t m
      exact Submodule.smul_mem _ _ (oldComp_degree D Sc cutoff sy hc _ _
        (oldAppend_mem_degree D Sc cutoff sy hc i hb) hm)

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
end

end

section

/-! # Integer degrees of the actual represented matrix inverses

The homogeneous inverse step (G8) uses the original old-category Hom
degrees and the intrinsic balanced Hom-tensor degrees. The actual finite
unit/cap matrices have degree zero after the prescribed coordinate shifts.
Their existing bijectivity therefore gives homogeneous raw inverses,
including principal inverse degree `+2 dᵢ`. No degree of arbitrary module
Homs or grading transported through a matrix is assumed.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory GradedSupercategory
open OddMath.IntegerMatrix
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

/-- The original coefficient Hom grading, before any finite matrix is used. -/
def oldHomIntegerCoordinates (v t : OldCategory D Sc cutoff) :
    Coordinates (k := k) (v ⟶ t) := by
  letI := oldCategoryGradedSupercategory D Sc cutoff sy hc
  exact {
    degree := degree (R := k) v t
    projection := fun n => dproj k n
    projection_mem := fun n x => dproj_mem n x
    projection_of_mem := fun {m n} {x} hx => by
      by_cases h : m = n
      · subst m
        rw [ite_eq_left rfl]
        exact dproj_of_mem hx
      · rw [ite_eq_right h]
        exact dproj_of_mem_ne hx h
    spanning := (isInternal_degree v t).submodule_iSup_eq_top }

/-- The intrinsic quotient grading of the represented lower loop. -/
def representedKernelCoordinates (i : I) (v t : OldCategory D Sc cutoff) :
    Coordinates (k := k) (IndResKernel.Component (k := k) (append D Sc cutoff i) v t) := by
  letI := oldCategoryGradedSupercategory D Sc cutoff sy hc
  letI : IsGradedSuperfunctor k (append D Sc cutoff i) :=
    (oldAppendGraded D Sc cutoff sy hc i).isGraded
  exact {
    degree := IndResKernel.integerDegree (k := k) (append D Sc cutoff i) v t
    projection := IndResKernel.integerProjection (k := k) (append D Sc cutoff i) v t
    projection_mem := IndResKernel.integerProjection_mem (k := k) (append D Sc cutoff i) v t
    projection_of_mem := IndResKernel.integerProjection_of_mem (k := k) (append D Sc cutoff i) v t
    spanning := IndResKernel.iSup_integerDegree_eq_top (k := k) (append D Sc cutoff i) v t }

/-- The positive source shifts are `+2dᵢ` on the kernel and `-2dᵢr` on row `r`. -/
def positiveKernelShift (i : I) (m : ℕ) : Option (Fin m) → ℤ
  | none => 2 * sy.d i
  | some r => -(2 * sy.d i * r.val)

/-- The negative target shifts are `-2dᵢ` on the upper Hom and `+2dᵢr` on row `r`. -/
def negativeKernelShift (i : I) (m : ℕ) : Option (Fin m) → ℤ
  | none => -(2 * sy.d i)
  | some r => 2 * sy.d i * r.val

private def positiveEntryCoordinates (i : I) (m : ℕ) (v t : OldCategory D Sc cutoff) :
    ∀ a, Coordinates (k := k) ((positiveKernelFamily D Sc cutoff i m t a).obj (op v))
  | none => representedKernelCoordinates D Sc cutoff sy hc i v t
  | some _ => oldHomIntegerCoordinates D Sc cutoff sy hc v t

private def negativeEntryCoordinates (i : I) (m : ℕ) (v t : OldCategory D Sc cutoff) :
    ∀ a, Coordinates (k := k) ((negativeKernelFamily D Sc cutoff i m t a).obj (op v))
  | none => oldHomIntegerCoordinates D Sc cutoff sy hc
      ((append D Sc cutoff i).obj v) ((append D Sc cutoff i).obj t)
  | some _ => oldHomIntegerCoordinates D Sc cutoff sy hc v t

/-- The positive finite source has its prescribed intrinsic shifted decomposition. -/
def positiveKernelIntegerCoordinates (i : I) (m : ℕ) (v t : OldCategory D Sc cutoff) :
    Coordinates (k := k) ((BalancedKernelTensor.piKernel
      (positiveKernelFamily D Sc cutoff i m t)).obj (op v)) :=
  Coordinates.shiftedFamily (positiveEntryCoordinates D Sc cutoff sy hc i m v t)
    (positiveKernelShift D sy i m)

/-- The negative finite target has its prescribed intrinsic shifted decomposition. -/
def negativeKernelIntegerCoordinates (i : I) (m : ℕ) (v t : OldCategory D Sc cutoff) :
    Coordinates (k := k) ((BalancedKernelTensor.piKernel
      (negativeKernelFamily D Sc cutoff i m t)).obj (op v)) :=
  Coordinates.shiftedFamily (negativeEntryCoordinates D Sc cutoff sy hc i m v t)
    (negativeKernelShift D sy i m)

/-- The literal positive matrix preserves the shifted integer degree. -/
theorem positiveKernelMap_degree (i : I) (m : ℕ) (v t : OldCategory D Sc cutoff)
    {n : ℤ} {z : (BalancedKernelTensor.piKernel (positiveKernelFamily D Sc cutoff i m t)).obj (op v)}
    (hz : z ∈ (positiveKernelIntegerCoordinates D Sc cutoff sy hc i m v t).degree n) :
    (positiveKernelMap D Sc cutoff i m t).app (op v) z ∈
      oldDegree D sy Sc hc cutoff (v.word ++ [i]) (t.word ++ [i]) n := by
  have hz' := (Coordinates.mem_shiftedDegree
    (positiveEntryCoordinates D Sc cutoff sy hc i m v t) (positiveKernelShift D sy i m) n z).1 hz
  rw [positiveKernelMap_apply]
  apply Submodule.add_mem
  · have h := mateKernelComponent_degree D Sc cutoff sy hc i v t (hz' none)
    simpa only [positiveEntryCoordinates, representedKernelCoordinates, positiveKernelShift,
      add_sub_cancel_right] using h
  · apply Submodule.sum_mem
    intro r _
    have h := unitKernelComponent_degree D Sc cutoff sy hc i v t r.val (hz' (some r))
    simpa only [positiveEntryCoordinates, oldHomIntegerCoordinates, positiveKernelShift,
      neg_add_cancel_right] using h

/-- The literal negative matrix preserves the shifted integer degree. -/
theorem negativeKernelMap_degree (i : I) (m : ℕ) (v t : OldCategory D Sc cutoff)
    {n : ℤ} {z : IndResKernel.Component (k := k) (append D Sc cutoff i) v t}
    (hz : z ∈ representedKernelDegree D Sc cutoff sy hc i v t n) :
    (negativeKernelMap D Sc cutoff i m t).app (op v) z ∈
      (negativeKernelIntegerCoordinates D Sc cutoff sy hc i m v t).degree n := by
  apply (Coordinates.mem_shiftedDegree
    (negativeEntryCoordinates D Sc cutoff sy hc i m v t) (negativeKernelShift D sy i m) n _).2
  intro a
  cases a with
  | none =>
    rw [negativeKernelMap_none]
    exact mateKernelComponent_degree D Sc cutoff sy hc i v t hz
  | some r =>
    rw [negativeKernelMap_some]
    exact capKernelComponent_degree D Sc cutoff sy hc i v t r.val hz

omit sy hc in
/-- The raw positive kernel equivalence is the existing actual matrix, with its
proved bijectivity at the actual content height. -/
def positiveKernelEquiv (i : I) (v t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I)) :=
  LinearEquiv.ofBijective
    ((positiveKernelMap D Sc cutoff i
      (contentUnitCount D cutoff i (t.word : Multiset I)) t).app (op v)).hom
    (positiveKernelMap_bijective D Sc cutoff i t hh v)

omit sy hc in
/-- The raw negative kernel equivalence is the existing actual cap-row matrix. -/
def negativeKernelEquiv (i : I) (v t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0) :=
  LinearEquiv.ofBijective
    ((negativeKernelMap D Sc cutoff i
      (contentCapCount D cutoff i (t.word : Multiset I)) t).app (op v)).hom
    (negativeKernelMap_bijective D Sc cutoff i t hh v)

/-- The positive inverse preserves the intrinsic shifted coordinate degrees. -/
theorem positiveKernelEquiv_inverse_degree (i : I) (v t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I)) {n : ℤ}
    {y : (append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t}
    (hy : y ∈ oldDegree D sy Sc hc cutoff (v.word ++ [i]) (t.word ++ [i]) n) :
    (positiveKernelEquiv D Sc cutoff i v t hh).symm y ∈
      (positiveKernelIntegerCoordinates D Sc cutoff sy hc i
        (contentUnitCount D cutoff i (t.word : Multiset I)) v t).degree n := by
  exact Coordinates.inverse_mem _ (oldHomIntegerCoordinates D Sc cutoff sy hc _ _)
    (positiveKernelEquiv D Sc cutoff i v t hh)
    (fun n x hx => positiveKernelMap_degree D Sc cutoff sy hc i _ v t hx) hy

/-- The negative inverse preserves the intrinsic shifted coordinate degrees. -/
theorem negativeKernelEquiv_inverse_degree (i : I) (v t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0) {n : ℤ} {y}
    (hy : y ∈ (negativeKernelIntegerCoordinates D Sc cutoff sy hc i
      (contentCapCount D cutoff i (t.word : Multiset I)) v t).degree n) :
    (negativeKernelEquiv D Sc cutoff i v t hh).symm y ∈
      representedKernelDegree D Sc cutoff sy hc i v t n := by
  exact Coordinates.inverse_mem (representedKernelCoordinates D Sc cutoff sy hc i v t) _
    (negativeKernelEquiv D Sc cutoff i v t hh)
    (fun n x hx => negativeKernelMap_degree D Sc cutoff sy hc i _ v t hx) hy

omit sy hc in
/-- Principal positive inverse component, without a changed normalization. -/
def positiveKernelPrincipalInverse (i : I) (v t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I)) :
    ((append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t) →ₗ[k]
      IndResKernel.Component (k := k) (append D Sc cutoff i) v t :=
  LinearMap.proj none ∘ₗ (positiveKernelEquiv D Sc cutoff i v t hh).symm.toLinearMap

/-- The represented principal positive inverse raises raw degree by `2 dᵢ`. -/
theorem positiveKernelPrincipalInverse_degree (i : I) (v t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I)) {n : ℤ}
    {y : (append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t}
    (hy : y ∈ oldDegree D sy Sc hc cutoff (v.word ++ [i]) (t.word ++ [i]) n) :
    positiveKernelPrincipalInverse D Sc cutoff i v t hh y ∈
      representedKernelDegree D Sc cutoff sy hc i v t (n + 2 * sy.d i) :=
  (Coordinates.mem_shiftedDegree _ _ _ _).1
    (positiveKernelEquiv_inverse_degree D Sc cutoff sy hc i v t hh hy) none

omit sy hc in
/-- Principal negative inverse component: first insert the actual upper-Hom column. -/
def negativeKernelPrincipalInverse (i : I) (v t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0) :
    ((append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t) →ₗ[k]
      IndResKernel.Component (k := k) (append D Sc cutoff i) v t :=
  (negativeKernelEquiv D Sc cutoff i v t hh).symm.toLinearMap ∘ₗ
    LinearMap.single k (fun a => (negativeKernelFamily D Sc cutoff i
      (contentCapCount D cutoff i (t.word : Multiset I)) t a).obj (op v)) none

/-- The represented principal negative inverse also raises raw degree by `2 dᵢ`. -/
theorem negativeKernelPrincipalInverse_degree (i : I) (v t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0) {n : ℤ}
    {y : (append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t}
    (hy : y ∈ oldDegree D sy Sc hc cutoff (v.word ++ [i]) (t.word ++ [i]) n) :
    negativeKernelPrincipalInverse D Sc cutoff i v t hh y ∈
      representedKernelDegree D Sc cutoff sy hc i v t (n + 2 * sy.d i) := by
  apply negativeKernelEquiv_inverse_degree D Sc cutoff sy hc i v t hh
  apply (Coordinates.mem_shiftedDegree _ _ _ _).2
  intro a
  cases a with
  | none =>
    change y ∈ oldDegree D sy Sc hc cutoff (v.word ++ [i]) (t.word ++ [i])
      (n + 2 * sy.d i + -(2 * sy.d i))
    simpa only [add_neg_cancel_right] using hy
  | some r =>
    change (Pi.single none y : ∀ a, (negativeKernelFamily D Sc cutoff i
      (contentCapCount D cutoff i (t.word : Multiset I)) t a).obj (op v)) (some r) ∈ _
    rw [Pi.single_eq_of_ne (by simp)]
    exact Submodule.zero_mem _

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
end

end

section

/-! # The selected OLD matrix inverse in balanced kernel coordinates

These equations expose the inverse hidden by the module-matrix construction,
including its action on every pure tensor and the principal finite slot.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
namespace BalancedKernelTensor
variable {k C : Type u} [CommRing k] [Category.{u} C]
  (M : C ⥤ SVec k) {K L : Cᵒᵖ ⥤ ModuleCat k}

/-- The tensor inverse uses the inverse of the actual coefficient map on
its kernel factor, without a flatness or projectivity premise. -/
theorem equivOfBijective_symm_tensor (e : K ⟶ L)
    (he : ∀ v, Function.Bijective (e.app v)) (v : C) (a : L.obj (op v)) (b : M.obj v) :
    (equivOfBijective M e he).symm (tensor L M v a b) =
      tensor K M v ((LinearEquiv.ofBijective (e.app (op v)).hom (he (op v))).symm a) b := by
  exact map_tensor M (coefficientIso e he).inv v a b
end BalancedKernelTensor
namespace CyclotomicCrossingTensor.TensorMatrixCoordinates
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
  (i : I) (t : OldCategory D Sc cutoff)

/-- The selected OLD unit-matrix inverse is the balanced tensor kernel inverse
in the prescribed finite shifted coordinates. -/
theorem moduleUnitMatrixIso_inv_kernel
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (z : mateTargetSpace D Sc cutoff i M t) :
    (moduleUnitMatrixIso D Sc cutoff M i t hh).inv z =
      positiveKernelCoordinates D Sc cutoff M i _ t
        ((BalancedKernelTensor.equivOfBijective M.toFunctor
          (positiveKernelMap D Sc cutoff i _ t)
          (fun v => by
            rcases v with ⟨v⟩
            exact positiveKernelMap_bijective D Sc cutoff i t hh v)).symm
          ((resIndKernelCoordinates D Sc cutoff M i t).symm z)) := rfl

/-- The selected OLD cap-matrix inverse uses the actual negative kernel map. -/
theorem moduleCapMatrixIso_inv_kernel
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0)
    (z : capMatrixTargetSpace D Sc cutoff i M (contentCapCount D cutoff i (t.word : Multiset I)) t) :
    (moduleCapMatrixIso D Sc cutoff M i t hh).inv z =
      indResKernelCoordinates D Sc cutoff M i t
        ((BalancedKernelTensor.equivOfBijective M.toFunctor
          (negativeKernelMap D Sc cutoff i _ t)
          (fun v => by
            rcases v with ⟨v⟩
            exact negativeKernelMap_bijective D Sc cutoff i t hh v)).symm
          ((negativeKernelCoordinates D Sc cutoff M i _ t).symm z)) := rfl

/-- On pure upper-Hom tensors the unit inverse applies the raw coefficient
inverse and leaves the module vector unchanged. -/
theorem moduleUnitMatrixIso_inv_tensor
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (v : OldCategory D Sc cutoff)
    (y : (append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t) (b : M.obj v) :
    (moduleUnitMatrixIso D Sc cutoff M i t hh).inv
      (BalancedInduction.tensor (append D Sc cutoff i) M.toFunctor v y b) =
    positiveKernelCoordinates D Sc cutoff M i _ t
      (BalancedKernelTensor.tensor _ M.toFunctor v
        ((positiveKernelEquiv D Sc cutoff i v t hh).symm y) b) := by
  rw [moduleUnitMatrixIso_inv_kernel, ← resIndKernelCoordinates_tensor,
    LinearEquiv.symm_apply_apply, BalancedKernelTensor.equivOfBijective_symm_tensor]
  rfl

/-- Removing the prescribed principal source parity shift identifies the OLD
unit principal inverse with the raw positive kernel principal inverse. -/
theorem moduleUnitMatrixIso_principal_inv_tensor
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (v : OldCategory D Sc cutoff)
    (y : (append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t) (b : M.obj v) :
    moduleIsoLinearEquiv (unitMatrixFirstSourceIso D Sc cutoff i M
      (contentUnitCount D cutoff i (t.word : Multiset I))) t
      (((moduleUnitMatrixIso D Sc cutoff M i t hh).inv
        (BalancedInduction.tensor (append D Sc cutoff i) M.toFunctor v y b)) none) =
    IndResKernel.evaluate (append D Sc cutoff i) M.toFunctor v t b
      (positiveKernelPrincipalInverse D Sc cutoff i v t hh y) := by
  rw [moduleUnitMatrixIso_inv_tensor, positiveKernelCoordinates_apply,
    BalancedKernelTensor.map_tensor, positiveSlotCoordinates_none]
  change indResKernelCoordinates D Sc cutoff M i t
    (BalancedKernelTensor.tensor (IndResKernel.kernel (k := k) (append D Sc cutoff i) t)
      M.toFunctor v (positiveKernelPrincipalInverse D Sc cutoff i v t hh y) b) = _
  exact indResKernelCoordinates_tensor D Sc cutoff M i v t _ b

/-- The cap inverse likewise acts on the raw finite coefficient family. -/
theorem moduleCapMatrixIso_inv_tensor
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0)
    (v : OldCategory D Sc cutoff)
    (y : (BalancedKernelTensor.piKernel (negativeKernelFamily D Sc cutoff i
      (contentCapCount D cutoff i (t.word : Multiset I)) t)).obj (op v)) (b : M.obj v) :
    (moduleCapMatrixIso D Sc cutoff M i t hh).inv
      (negativeKernelCoordinates D Sc cutoff M i _ t
        (BalancedKernelTensor.tensor _ M.toFunctor v y b)) =
    IndResKernel.evaluate (append D Sc cutoff i) M.toFunctor v t b
      ((negativeKernelEquiv D Sc cutoff i v t hh).symm y) := by
  rw [moduleCapMatrixIso_inv_kernel, LinearEquiv.symm_apply_apply,
    BalancedKernelTensor.equivOfBijective_symm_tensor, indResKernelCoordinates_tensor]
  rfl

/-- The raw upper-Hom insertion selects precisely the principal negative inverse. -/
theorem moduleCapMatrixIso_principal_inv_tensor
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0)
    (v : OldCategory D Sc cutoff)
    (y : (append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t) (b : M.obj v) :
    (moduleCapMatrixIso D Sc cutoff M i t hh).inv
      (negativeKernelCoordinates D Sc cutoff M i _ t
        (BalancedKernelTensor.tensor _ M.toFunctor v (Pi.single none y) b)) =
    IndResKernel.evaluate (append D Sc cutoff i) M.toFunctor v t b
      (negativeKernelPrincipalInverse D Sc cutoff i v t hh y) := by
  rw [moduleCapMatrixIso_inv_tensor]
  rfl

end CyclotomicCrossingTensor.TensorMatrixCoordinates
end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Integer degree of represented unit-inverse-cap closures

The source-coefficient calculation needed by ReservoirClosureDegree applies
ordinary unit/dot columns, the prescribed principal finite inverse, then
ordinary dot/cap rows. Both height orientations have degree
`2 dᵢ (r+s+1)`. The evaluation equations retain the actual OLD module maps
and all their canonical parity coordinates.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open TensorMatrixCoordinates
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Ordinary unit/dot, positive principal inverse, then ordinary dot/cap. -/
def positiveKernelClosure (i : I) (v t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I)) (r s : ℕ) :
    (v ⟶ t) →ₗ[k] (v ⟶ t) :=
  capKernelComponent D Sc cutoff i s v t ∘ₗ
    positiveKernelPrincipalInverse D Sc cutoff i v t hh ∘ₗ
      unitKernelComponent D Sc cutoff i r v t

/-- The same literal closure using the negative principal inverse. -/
def negativeKernelClosure (i : I) (v t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0) (r s : ℕ) :
    (v ⟶ t) →ₗ[k] (v ⟶ t) :=
  capKernelComponent D Sc cutoff i s v t ∘ₗ
    negativeKernelPrincipalInverse D Sc cutoff i v t hh ∘ₗ
      unitKernelComponent D Sc cutoff i r v t

variable (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

/-- The positive represented closure has its prescribed integer degree. -/
theorem positiveKernelClosure_degree (i : I) (v t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I)) (r s : ℕ)
    {n : ℤ} {b : v ⟶ t} (hb : b ∈ oldDegree D sy Sc hc cutoff v.word t.word n) :
    positiveKernelClosure D Sc cutoff i v t hh r s b ∈
      oldDegree D sy Sc hc cutoff v.word t.word (n + 2 * sy.d i * (r + s + 1 : ℕ)) := by
  have h := capKernelComponent_degree D Sc cutoff sy hc i v t s
    (positiveKernelPrincipalInverse_degree D Sc cutoff sy hc i v t hh
      (unitKernelComponent_degree D Sc cutoff sy hc i v t r hb))
  have he : n + 2 * sy.d i * r + 2 * sy.d i + 2 * sy.d i * s =
      n + 2 * sy.d i * (r + s + 1 : ℕ) := by push_cast; ring
  simpa only [positiveKernelClosure, LinearMap.comp_apply, he] using h

/-- The negative represented closure has the same prescribed degree. -/
theorem negativeKernelClosure_degree (i : I) (v t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0) (r s : ℕ)
    {n : ℤ} {b : v ⟶ t} (hb : b ∈ oldDegree D sy Sc hc cutoff v.word t.word n) :
    negativeKernelClosure D Sc cutoff i v t hh r s b ∈
      oldDegree D sy Sc hc cutoff v.word t.word (n + 2 * sy.d i * (r + s + 1 : ℕ)) := by
  have h := capKernelComponent_degree D Sc cutoff sy hc i v t s
    (negativeKernelPrincipalInverse_degree D Sc cutoff sy hc i v t hh
      (unitKernelComponent_degree D Sc cutoff sy hc i v t r hb))
  have he : n + 2 * sy.d i * r + 2 * sy.d i + 2 * sy.d i * s =
      n + 2 * sy.d i * (r + s + 1 : ℕ) := by push_cast; ring
  simpa only [negativeKernelClosure, LinearMap.comp_apply, he] using h

omit sy hc in
/-- On every OLD module, the positive closure acts by the prescribed unit,
canonical principal inverse, and cap; the module vector is unrestricted. -/
theorem positiveKernelClosure_evaluate
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (i : I) (v t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (r s : ℕ) (b : v ⟶ t) (m : M.obj v) :
    M.map (positiveKernelClosure D Sc cutoff i v t hh r s b) m =
      (moduleCapRow D Sc cutoff i M s).total t
        (moduleIsoLinearEquiv (unitMatrixFirstSourceIso D Sc cutoff i M
          (contentUnitCount D cutoff i (t.word : Multiset I))) t
          (((moduleUnitMatrixIso D Sc cutoff M i t hh).inv
            ((moduleUnitColumn D Sc cutoff i M r).total t (M.map b m))) none)) := by
  rw [positiveKernelClosure, LinearMap.comp_apply, LinearMap.comp_apply,
    capKernel_evaluate_moduleCapRow,
    ← moduleUnitMatrixIso_principal_inv_tensor,
    unitKernel_evaluate]

omit sy hc in
/-- Inserting the upper-Hom coefficient before realization is exactly the
principal target insertion with its prescribed canonical parity coordinate. -/
theorem negativeKernelCoordinates_single_tensor
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (i : I) (m : ℕ) (v t : OldCategory D Sc cutoff)
    (y : (append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t) (b : M.obj v) :
    TensorMatrixCoordinates.negativeKernelCoordinates D Sc cutoff M i m t
      (BalancedKernelTensor.tensor _ M.toFunctor v (Pi.single none y) b) =
    Pi.single none ((moduleIsoLinearEquiv (capMatrixFirstTargetIso D Sc cutoff i M m) t).symm
      (BalancedInduction.tensor (append D Sc cutoff i) M.toFunctor v y b)) := by
  classical
  funext a
  rw [negativeKernelCoordinates_apply, BalancedKernelTensor.map_tensor]
  change negativeSlotCoordinates D Sc cutoff M i m t a
    (BalancedKernelTensor.tensor _ M.toFunctor v
      ((Pi.single none y : ∀ c, (negativeKernelFamily D Sc cutoff i m t c).obj (Opposite.op v)) a) b) = _
  cases a with
  | none =>
    simp only [Pi.single_eq_same]
    apply (moduleIsoLinearEquiv (capMatrixFirstTargetIso D Sc cutoff i M m) t).injective
    rw [negativeSlotCoordinates_none, LinearEquiv.apply_symm_apply]
    exact resIndKernelCoordinates_tensor D Sc cutoff M i v t y b
  | some r =>
    simp only [Pi.single_eq_of_ne (by simp : some r ≠ none),
      BalancedKernelTensor.tensor_zero_left, map_zero]

omit sy hc in
/-- The negative closure likewise acts by the ordinary unit, the actual cap
matrix inverse at its canonically shifted principal input, and ordinary cap. -/
theorem negativeKernelClosure_evaluate
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (i : I) (v t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0)
    (r s : ℕ) (b : v ⟶ t) (m : M.obj v) :
    M.map (negativeKernelClosure D Sc cutoff i v t hh r s b) m =
      (moduleCapRow D Sc cutoff i M s).total t
        ((moduleCapMatrixIso D Sc cutoff M i t hh).inv
          (Pi.single none
            ((moduleIsoLinearEquiv (capMatrixFirstTargetIso D Sc cutoff i M
              (contentCapCount D cutoff i (t.word : Multiset I))) t).symm
              ((moduleUnitColumn D Sc cutoff i M r).total t (M.map b m))))) := by
  rw [negativeKernelClosure, LinearMap.comp_apply, LinearMap.comp_apply,
    capKernel_evaluate_moduleCapRow,
    ← moduleCapMatrixIso_principal_inv_tensor,
    negativeKernelCoordinates_single_tensor, unitKernel_evaluate]

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
end

end

section

/-! # Total representable evaluation and source coefficient degree

The reconstruction step in ReservoirClosureDegree can be checked on the
total action at each representable identity. Independent parity projections
then recover both components without grading arbitrary module morphisms.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory GradedSupercategory
namespace OddMath.QuiverHecke.ELVOld.ModuleCentre
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I)

/-- Total source reconstruction is the total module action on its represented
identity. Both off-diagonal parity components vanish by homogeneity. -/
theorem reconstruct_total_evaluate (η : Centre D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N β) :
    (reconstruct D Sc cutoff N β η).total w =
      (η.total (contentRepresentable D Sc cutoff N β w)).total w (𝟙 w) := by
  let R := contentRepresentable D Sc cutoff N β w
  change (η.app 0 R).app 0 w (𝟙 w) + (η.app 1 R).app 1 w (𝟙 w) =
    (((η.app 0 R).app 0 w + (η.app 1 R).app 0 w) +
      ((η.app 0 R).app 1 w + (η.app 1 R).app 1 w)) (𝟙 w)
  rw [Superfunctor.app_eq_zero_of_mem (η.app_mem 1 R) (q := 0) (by decide),
    Superfunctor.app_eq_zero_of_mem (η.app_mem 0 R) (q := 1) (by decide)]
  simp only [add_zero, zero_add, SVec.add_apply]

/-- The parity component of the reconstructed coefficient is its ordinary
source parity projection, independently of integer degree. -/
theorem reconstruct_app_eq_proj_total (η : Centre D Sc cutoff N β) (p : ZMod 2)
    (w : ContentCategory D Sc cutoff N β) :
    (reconstruct D Sc cutoff N β η).app p w =
      proj k p ((reconstruct D Sc cutoff N β η).total w) := by
  symm
  rcases parity_eq_zero_or_one p with rfl | rfl
  · exact proj_eq_of_add rfl
      ((reconstruct D Sc cutoff N β η).app_mem 0 w)
      ((reconstruct D Sc cutoff N β η).app_mem 1 w)
  · exact proj_eq_of_add (add_comm _ _)
      ((reconstruct D Sc cutoff N β η).app_mem 1 w)
      (by simpa using (reconstruct D Sc cutoff N β η).app_mem 0 w)

variable (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

/-- Source integer degree follows from the total action on every represented
identity; both parity projections preserve that same integer degree. -/
theorem reconstruct_mem_degree_of_total_evaluation (η : Centre D Sc cutoff N β) (d : ℤ)
    (h : ∀ w : ContentCategory D Sc cutoff N β,
      (η.total (contentRepresentable D Sc cutoff N β w)).total w (𝟙 w) ∈
        truncatedDegree D Sc cutoff sy hc N w.obj.word w.obj.word d) :
    reconstruct D Sc cutoff N β η ∈ contentCoefficientDegree D Sc cutoff N β sy hc d := by
  intro p w
  change (reconstruct D Sc cutoff N β η).app p w ∈
    truncatedDegree D Sc cutoff sy hc N w.obj.word w.obj.word d
  rw [reconstruct_app_eq_proj_total, reconstruct_total_evaluate]
  exact (contentGradedSupercategory D Sc cutoff N sy hc β).proj_mem_degree p (h w)

end OddMath.QuiverHecke.ELVOld.ModuleCentre
end

end

section

/-! # Degrees of the finite inverse window contractions

The coefficient calculation in SwappedHomInversion §4, equation (7), uses
every window coordinate of the literal finite kernel inverse. The unit
orientation extracts a coordinate after an arbitrary unit/dot column;
the cap orientation inserts a coordinate before an arbitrary dot/cap row.
These raw contractions have degree `2 dᵢ (n-m)` and `2 dᵢ (m-n)` respectively.
This calculation does not identify them with a chosen content local `g'`.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Every window coordinate of the positive raw matrix inverse. -/
def positiveKernelWindowInverse (i : I) (v t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (m : Fin (contentUnitCount D cutoff i (t.word : Multiset I))) :
    ((append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t) →ₗ[k] (v ⟶ t) :=
  LinearMap.proj (some m) ∘ₗ (positiveKernelEquiv D Sc cutoff i v t hh).symm.toLinearMap

/-- Every window column of the negative raw matrix inverse. -/
def negativeKernelWindowInverse (i : I) (v t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0)
    (m : Fin (contentCapCount D cutoff i (t.word : Multiset I))) :
    (v ⟶ t) →ₗ[k] IndResKernel.Component (k := k) (append D Sc cutoff i) v t :=
  (negativeKernelEquiv D Sc cutoff i v t hh).symm.toLinearMap ∘ₗ
    LinearMap.single k (fun a => (negativeKernelFamily D Sc cutoff i
      (contentCapCount D cutoff i (t.word : Multiset I)) t a).obj (op v)) (some m)

/-- Positive boundary: inverse window row `m` after unit/dot column `n`. -/
def positiveKernelBoundary (i : I) (v t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (m : Fin (contentUnitCount D cutoff i (t.word : Multiset I))) (n : ℕ) :
    (v ⟶ t) →ₗ[k] (v ⟶ t) :=
  positiveKernelWindowInverse D Sc cutoff i v t hh m ∘ₗ
    unitKernelComponent D Sc cutoff i n v t

/-- Negative boundary: dot/cap row `m` after inverse window column `n`. -/
def negativeKernelBoundary (i : I) (v t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0)
    (m : ℕ) (n : Fin (contentCapCount D cutoff i (t.word : Multiset I))) :
    (v ⟶ t) →ₗ[k] (v ⟶ t) :=
  capKernelComponent D Sc cutoff i m v t ∘ₗ
    negativeKernelWindowInverse D Sc cutoff i v t hh n

variable (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

/-- The positive inverse window row has raw degree `-2 dᵢ m`. -/
theorem positiveKernelWindowInverse_degree (i : I) (v t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (m : Fin (contentUnitCount D cutoff i (t.word : Multiset I))) {q : ℤ}
    {y : (append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t}
    (hy : y ∈ oldDegree D sy Sc hc cutoff (v.word ++ [i]) (t.word ++ [i]) q) :
    positiveKernelWindowInverse D Sc cutoff i v t hh m y ∈
      oldDegree D sy Sc hc cutoff v.word t.word (q - 2 * sy.d i * m.val) := by
  exact (OddMath.IntegerMatrix.Coordinates.mem_shiftedDegree _ _ _ _).1
    (positiveKernelEquiv_inverse_degree D Sc cutoff sy hc i v t hh hy) (some m)

/-- Inserting window column `m` gives raw inverse degree `-2 dᵢ m`. -/
theorem negativeKernelWindowInverse_degree (i : I) (v t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0)
    (m : Fin (contentCapCount D cutoff i (t.word : Multiset I))) {q : ℤ}
    {y : v ⟶ t} (hy : y ∈ oldDegree D sy Sc hc cutoff v.word t.word q) :
    negativeKernelWindowInverse D Sc cutoff i v t hh m y ∈
      representedKernelDegree D Sc cutoff sy hc i v t (q - 2 * sy.d i * m.val) := by
  classical
  change (negativeKernelEquiv D Sc cutoff i v t hh).symm
    (Pi.single (some m) y) ∈ _
  apply negativeKernelEquiv_inverse_degree D Sc cutoff sy hc i v t hh
  apply (OddMath.IntegerMatrix.Coordinates.mem_shiftedDegree _ _ _ _).2
  intro a
  by_cases ha : a = some m
  · subst a
    simp only [Pi.single_eq_same]
    change y ∈ oldDegree D sy Sc hc cutoff v.word t.word
      (q - 2 * sy.d i * m.val + 2 * sy.d i * m.val)
    simpa only [sub_add_cancel] using hy
  · rw [Pi.single_eq_of_ne ha]
    exact Submodule.zero_mem _

/-- All positive contractions have the difference degree, also outside the window. -/
theorem positiveKernelBoundary_degree (i : I) (v t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (m : Fin (contentUnitCount D cutoff i (t.word : Multiset I))) (n : ℕ) {q : ℤ}
    {y : v ⟶ t} (hy : y ∈ oldDegree D sy Sc hc cutoff v.word t.word q) :
    positiveKernelBoundary D Sc cutoff i v t hh m n y ∈
      oldDegree D sy Sc hc cutoff v.word t.word (q + 2 * sy.d i * ((n : ℤ) - m.val)) := by
  have h := positiveKernelWindowInverse_degree D Sc cutoff sy hc i v t hh m
    (unitKernelComponent_degree D Sc cutoff sy hc i v t n hy)
  have he : q + 2 * sy.d i * n - 2 * sy.d i * m.val =
      q + 2 * sy.d i * ((n : ℤ) - m.val) := by ring
  simpa only [positiveKernelBoundary, LinearMap.comp_apply, he] using h

/-- All negative contractions have the difference degree, also outside the window. -/
theorem negativeKernelBoundary_degree (i : I) (v t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0)
    (m : ℕ) (n : Fin (contentCapCount D cutoff i (t.word : Multiset I))) {q : ℤ}
    {y : v ⟶ t} (hy : y ∈ oldDegree D sy Sc hc cutoff v.word t.word q) :
    negativeKernelBoundary D Sc cutoff i v t hh m n y ∈
      oldDegree D sy Sc hc cutoff v.word t.word (q + 2 * sy.d i * ((m : ℤ) - n.val)) := by
  have h := capKernelComponent_degree D Sc cutoff sy hc i v t m
    (negativeKernelWindowInverse_degree D Sc cutoff sy hc i v t hh n hy)
  have he : q - 2 * sy.d i * n.val + 2 * sy.d i * m =
      q + 2 * sy.d i * ((m : ℤ) - n.val) := by ring
  simpa only [negativeKernelBoundary, LinearMap.comp_apply, he] using h

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
end

end

section

/-! # Evaluation of finite inverse window contractions

SwappedHomInversion §4 (7): every finite OLD module inverse coordinate
acts by its raw balanced-kernel coefficient. Canonical parity charts are
retained. This is the OLD evaluation step, before weighted content transport.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open TensorMatrixCoordinates
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))

local instance boundaryEvaluationPi :
    PiSupercategory k (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
  supermodulePiSupercategory

/-- Removing the finite source parity chart identifies every unit inverse row. -/
theorem moduleUnitMatrixIso_window_inv_tensor
    (i : I) (v t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (j : Fin (contentUnitCount D cutoff i (t.word : Multiset I)))
    (y : (append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t) (b : M.obj v) :
    moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
      (j.val • D.parity i)).iso M) t
      (((moduleUnitMatrixIso D Sc cutoff M i t hh).inv
        (BalancedInduction.tensor (append D Sc cutoff i) M.toFunctor v y b)) (some j)) =
    M.map (positiveKernelWindowInverse D Sc cutoff i v t hh j y) b := by
  rw [moduleUnitMatrixIso_inv_tensor, positiveKernelCoordinates_apply,
    BalancedKernelTensor.map_tensor, positiveSlotCoordinates_some]
  exact identityKernelCoordinates_tensor D Sc cutoff M v t _ b

/-- Single insertion in any finite cap target slot retains the canonical parity chart. -/
theorem negativeKernelCoordinates_window_single_tensor
    (i : I) (m : ℕ) (v t : OldCategory D Sc cutoff) (j : Fin m)
    (y : v ⟶ t) (b : M.obj v) :
    TensorMatrixCoordinates.negativeKernelCoordinates D Sc cutoff M i m t
      (BalancedKernelTensor.tensor _ M.toFunctor v (Pi.single (some j) y) b) =
    Pi.single (some j)
      ((moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
        (j.val • D.parity i)).iso M) t).symm (M.map y b)) := by
  classical
  funext a
  rw [negativeKernelCoordinates_apply, BalancedKernelTensor.map_tensor]
  change negativeSlotCoordinates D Sc cutoff M i m t a
    (BalancedKernelTensor.tensor _ M.toFunctor v
      ((Pi.single (some j) y : ∀ c, (negativeKernelFamily D Sc cutoff i m t c).obj (op v)) a) b) = _
  by_cases ha : a = some j
  · subst a
    simp only [Pi.single_eq_same]
    apply (moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
      (j.val • D.parity i)).iso M) t).injective
    rw [negativeSlotCoordinates_some, LinearEquiv.apply_symm_apply]
    exact identityKernelCoordinates_tensor D Sc cutoff M v t y b
  · simp only [Pi.single_eq_of_ne ha, BalancedKernelTensor.tensor_zero_left, map_zero]

/-- Every cap inverse column evaluates the corresponding raw finite inverse column. -/
theorem moduleCapMatrixIso_window_inv_tensor
    (i : I) (v t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0)
    (j : Fin (contentCapCount D cutoff i (t.word : Multiset I)))
    (y : v ⟶ t) (b : M.obj v) :
    (moduleCapMatrixIso D Sc cutoff M i t hh).inv
      (Pi.single (some j)
        ((moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
          (j.val • D.parity i)).iso M) t).symm (M.map y b))) =
    IndResKernel.evaluate (append D Sc cutoff i) M.toFunctor v t b
      (negativeKernelWindowInverse D Sc cutoff i v t hh j y) := by
  rw [← negativeKernelCoordinates_window_single_tensor,
    moduleCapMatrixIso_inv_tensor]
  rfl

/-- Positive raw boundary coefficients evaluate by the finite unit inverse row. -/
theorem positiveKernelBoundary_evaluate
    (i : I) (v t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (j : Fin (contentUnitCount D cutoff i (t.word : Multiset I)))
    (r : ℕ) (y : v ⟶ t) (b : M.obj v) :
    M.map (positiveKernelBoundary D Sc cutoff i v t hh j r y) b =
    moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
      (j.val • D.parity i)).iso M) t
      (((moduleUnitMatrixIso D Sc cutoff M i t hh).inv
        ((moduleUnitColumn D Sc cutoff i M r).total t (M.map y b))) (some j)) := by
  rw [positiveKernelBoundary, LinearMap.comp_apply,
    ← moduleUnitMatrixIso_window_inv_tensor, unitKernel_evaluate]

/-- Negative raw boundary coefficients evaluate by finite cap inverse insertion and cap. -/
theorem negativeKernelBoundary_evaluate
    (i : I) (v t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0)
    (r : ℕ) (j : Fin (contentCapCount D cutoff i (t.word : Multiset I)))
    (y : v ⟶ t) (b : M.obj v) :
    M.map (negativeKernelBoundary D Sc cutoff i v t hh r j y) b =
    (moduleCapRow D Sc cutoff i M r).total t
      ((moduleCapMatrixIso D Sc cutoff M i t hh).inv
        (Pi.single (some j)
          ((moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
            (j.val • D.parity i)).iso M) t).symm (M.map y b)))) := by
  rw [negativeKernelBoundary, LinearMap.comp_apply,
    capKernel_evaluate_moduleCapRow, ← moduleCapMatrixIso_window_inv_tensor]

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
end

end
