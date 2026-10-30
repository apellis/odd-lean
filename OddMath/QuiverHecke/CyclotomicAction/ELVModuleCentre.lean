import OddMath.QuiverHecke.CyclotomicAction.ELVModuleYoneda

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

theorem reconstruct_realize (c : ContentCoefficient D Sc cutoff N β) :
    reconstruct D Sc cutoff N β (contentRealize D Sc cutoff N β c) = c := by
  apply contentRealize_injective D Sc cutoff N β
  exact realize_reconstruct D Sc cutoff N β _

/-- Every module-supercentral transformation comes from the full source supercentre. -/
theorem contentRealize_surjective : Function.Surjective (contentRealize D Sc cutoff N β) :=
  fun η => ⟨reconstruct D Sc cutoff N β η, realize_reconstruct D Sc cutoff N β η⟩

/-- Source and module supercentres are linearly equivalent, with the explicit inverse. -/
def centreEquiv : ContentCoefficient D Sc cutoff N β ≃ₗ[k] Centre D Sc cutoff N β where
  toFun := contentRealize D Sc cutoff N β
  invFun := reconstruct D Sc cutoff N β
  left_inv := reconstruct_realize D Sc cutoff N β
  right_inv := realize_reconstruct D Sc cutoff N β
  map_add' := (contentRealizeLinear D Sc cutoff N β).map_add
  map_smul' := (contentRealizeLinear D Sc cutoff N β).map_smul

/-- Explicit component formula for the inverse centre map. -/
theorem reconstruct_app (η : Centre D Sc cutoff N β) (p : ZMod 2)
    (v : ContentCategory D Sc cutoff N β) :
    (reconstruct D Sc cutoff N β η).app p v =
      ContentYoneda.componentMap D Sc cutoff N β
        (moduleMap D Sc cutoff N β η p (contentRepresentable D Sc cutoff N β v)) p v (𝟙 v) := rfl

theorem reconstruct_proj (η : Centre D Sc cutoff N β) (p : ZMod 2) :
    reconstruct D Sc cutoff N β (proj k p η) = proj k p (reconstruct D Sc cutoff N β η) := by
  apply contentRealize_injective D Sc cutoff N β
  rw [realize_reconstruct, contentRealize_proj, realize_reconstruct]

/-- The same equivalence has exactly the existing content-module PiSCat target.
Its Pi structure is the one supplied by `contentModulePiIso`. -/
def centrePiEquiv : ContentCoefficient D Sc cutoff N β ≃ₗ[k]
    (𝟙 (contentModuleTarget D Sc cutoff N β) ⟶ 𝟙 (contentModuleTarget D Sc cutoff N β)) :=
  centreEquiv D Sc cutoff N β

end OddMath.QuiverHecke.ELVOld.ModuleCentre
