import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordCoordinates

/-! # Enriched Yoneda for actual regular-power word modules

SwappedVacuumCoordinates §3. The module source is actual induction of the
regular A/T vacuum, with its proved coend kernel. The inverse coordinate
map descends the full-parity twisted module-action formula through that
kernel, including every coefficient vector.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordYoneda
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)
  (ν : List I)
  (M : CoefficientPowerModules D Sc cutoff (elementaryCoefficients (k := k) D cutoff) L)
local notation "v" => (OldCategory.mk ν : OldCategory D Sc cutoff)
local notation "W" => powerWordModule D Sc cutoff L ν
local notation "F" => M.obj

private def rawComponent (m : (F).obj v) (p : ZMod 2) (w : OldCategory D Sc cutoff) :
    (v ⟶ w) →ₗ[k] (F).obj w where
  toFun h := (F).map (twist k p h) (((F).obj v).proj p m)
  map_add' h h' := by
    simp only [map_add, Superfunctor.map, Functor.map_add, SVec.add_apply]
  map_smul' c h := by
    simp only [map_smul, Superfunctor.map, Functor.map_smul, SVec.smul_apply, RingHom.id_apply]

private theorem rawComponent_kills (m : (F).obj v) (p : ZMod 2) (w : OldCategory D Sc cutoff) :
    LinearMap.ker (powerWordGenerator D Sc cutoff L ν w) ≤
      LinearMap.ker (rawComponent D Sc cutoff L ν M m p w) := by
  rw [powerWordGenerator_ker]
  apply Submodule.span_le.mpr
  rintro _ ⟨a, ha, h, rfl⟩
  have hk : KillsCoefficient D Sc cutoff F a :=
    (mem_coefficientAnnihilator D Sc cutoff F a).mp (M.property ha)
  have hz : (F).map (coefficientEndomorphism D Sc cutoff ν a) = 0 := hk ν
  have htw : (F).map (twist k p (coefficientEndomorphism D Sc cutoff ν a)) = 0 := by
    change (F).toFunctor.map (twist k p (coefficientEndomorphism D Sc cutoff ν a)) = 0
    rw [map_twist, show (F).toFunctor.map (coefficientEndomorphism D Sc cutoff ν a) = 0 from hz, map_zero]
  change (F).map (twist k p (coefficientEndomorphism D Sc cutoff ν a ≫ h)) (((F).obj v).proj p m) = 0
  rw [twist_comp]
  simp only [Superfunctor.map, Functor.map_comp, SVec.comp_apply]
  rw [show (F).toFunctor.map (twist k p (coefficientEndomorphism D Sc cutoff ν a)) = 0 from htw,
    SVec.zero_apply, map_zero]

/-- The full-parity module-action formula descends through the actual word
coend generator, using its proved presentation kernel. -/
def component (m : (F).obj v) (p : ZMod 2) (w : OldCategory D Sc cutoff) :
    (W).obj w →ₗ[k] (F).obj w :=
  ((LinearMap.ker (powerWordGenerator D Sc cutoff L ν w)).liftQ
    (rawComponent D Sc cutoff L ν M m p w) (rawComponent_kills D Sc cutoff L ν M m p w)).comp
      ((powerWordGenerator D Sc cutoff L ν w).quotKerEquivOfSurjective
        (powerWordGenerator_surjective D Sc cutoff L ν w)).symm.toLinearMap

/-- Coordinates on every generator, with the complete old-Hom parity twist. -/
theorem component_generator (m : (F).obj v) (p : ZMod 2) (w : OldCategory D Sc cutoff) (h : v ⟶ w) :
    component D Sc cutoff L ν M m p w (powerWordGenerator D Sc cutoff L ν w h) =
      (F).map (twist k p h) (((F).obj v).proj p m) := by
  change (LinearMap.ker (powerWordGenerator D Sc cutoff L ν w)).liftQ
    (rawComponent D Sc cutoff L ν M m p w) (rawComponent_kills D Sc cutoff L ν M m p w)
      (((powerWordGenerator D Sc cutoff L ν w).quotKerEquivOfSurjective
        (powerWordGenerator_surjective D Sc cutoff L ν w)).symm
          (powerWordGenerator D Sc cutoff L ν w h)) = _
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

private theorem tensor_proj_even {C B : Type u} [Category.{u} C] [Category.{u} B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (J : C ⥤ B) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    (R : C ⥤ SVec k) [R.Additive] [R.Linear k] [IsSuperfunctor k R]
    (q : ZMod 2) (z : C) {w : B} (h : J.obj z ⟶ w) (m : R.obj z)
    (hm : m ∈ (R.obj z).part 0) :
    (BalancedInduction.superspace J R w).proj q (BalancedInduction.tensor J R z h m) =
      BalancedInduction.tensor J R z (proj k q h) m := by
  rw [BalancedInduction.proj_tensor]
  simp only [SVec.proj_apply_of_mem_part _ hm, ite_true, one_ne_zero, ite_false,
    BalancedInduction.tensor_zero_right, add_zero]

theorem generator_proj (q : ZMod 2) (w : OldCategory D Sc cutoff) (h : v ⟶ w) :
    ((W).obj w).proj q (powerWordGenerator D Sc cutoff L ν w h) =
      powerWordGenerator D Sc cutoff L ν w (proj k q h) := by
  let J := powerWordCoefficientSource D Sc cutoff ν
  let R := (liftedPowerRegular (k := k) D cutoff L).toFunctor
  have hone : (1 : CoefficientPowerQuotient (k := k) D cutoff L) ∈
      (R.obj (powerCoefficientStar D cutoff)).part 0 :=
    SetLike.GradedOne.one_mem (A := coefficientPowerParity (k := k) D cutoff L)
  change (BalancedInduction.superspace J R w).proj q
      (BalancedInduction.tensor J R (powerCoefficientStar D cutoff) h
        (1 : CoefficientPowerQuotient (k := k) D cutoff L)) =
    BalancedInduction.tensor J R (powerCoefficientStar D cutoff) (proj k q h)
      (1 : CoefficientPowerQuotient (k := k) D cutoff L)
  exact tensor_proj_even J R q _ h _ hone

theorem generator_mem {q : ZMod 2} (w : OldCategory D Sc cutoff) (h : v ⟶ w)
    (hh : h ∈ parity (R := k) v w q) :
    powerWordGenerator D Sc cutoff L ν w h ∈ ((W).obj w).part q := by
  rw [SVec.mem_part_iff, generator_proj, proj_of_mem hh]

theorem generator_naturality {w z : OldCategory D Sc cutoff}
    (a : w ⟶ z) (h : v ⟶ w) :
    (W).map a (powerWordGenerator D Sc cutoff L ν w h) =
      powerWordGenerator D Sc cutoff L ν z (h ≫ a) := by
  let J := powerWordCoefficientSource D Sc cutoff ν
  let R := (liftedPowerRegular (k := k) D cutoff L).toFunctor
  change BalancedInduction.postcompose J R a
    (BalancedInduction.tensor J R (powerCoefficientStar D cutoff) h
      (1 : CoefficientPowerQuotient (k := k) D cutoff L)) =
    BalancedInduction.tensor J R (powerCoefficientStar D cutoff) (h ≫ a)
      (1 : CoefficientPowerQuotient (k := k) D cutoff L)
  exact BalancedInduction.postcompose_tensor J R a (powerCoefficientStar D cutoff) h _

/-- The enriched transformation determined by an arbitrary vector. -/
def fromElement (m : (F).obj v) : W ⟶ F :=
  Superfunctor.homMk {
    app := component D Sc cutoff L ν M m
    app_mem := by
      intro p w
      apply SVec.mem_parityHom_of_apply_mem
      intro q x hx
      obtain ⟨h, rfl⟩ := powerWordGenerator_surjective D Sc cutoff L ν w x
      have hg : powerWordGenerator D Sc cutoff L ν w (proj k q h) =
          powerWordGenerator D Sc cutoff L ν w h := by
        rw [← generator_proj, (SVec.mem_part_iff _).mp hx]
      rw [← hg, component_generator]
      rw [add_comm q p]
      exact SVec.apply_mem_part ((F).map_mem (twist_mem p (proj_mem q h)))
        (((F).obj v).proj_mem_part p m)
    naturality := by
      intro p w z q a ha
      apply LinearMap.ext
      intro x
      obtain ⟨h, rfl⟩ := powerWordGenerator_surjective D Sc cutoff L ν w x
      change component D Sc cutoff L ν M m p z
        ((W).map a (powerWordGenerator D Sc cutoff L ν w h)) =
        koszulSign p q • (F).map a
          (component D Sc cutoff L ν M m p w (powerWordGenerator D Sc cutoff L ν w h))
      rw [generator_naturality, component_generator, component_generator,
        twist_comp, twist_of_mem p ha, Linear.comp_smul, koszulSign_smul (R := k)]
      simp only [Superfunctor.map, Functor.map_smul, Functor.map_comp, SVec.smul_apply,
        SVec.comp_apply] }

/-- The actual regular-power generator at the identity old arrow. -/
def unitVector : (W).obj v := powerWordGenerator D Sc cutoff L ν v (𝟙 v)

theorem unitVector_even : unitVector D Sc cutoff L ν ∈ ((W).obj v).part 0 :=
  generator_mem D Sc cutoff L ν v (𝟙 v) (id_mem v)

/-- Evaluation retains both parity components of an enriched transformation. -/
def evaluate (t : W ⟶ F) : (F).obj v :=
  t.app 0 v (unitVector D Sc cutoff L ν) + t.app 1 v (unitVector D Sc cutoff L ν)

theorem evaluate_part (t : W ⟶ F) (p : ZMod 2) :
    t.app p v (unitVector D Sc cutoff L ν) ∈ ((F).obj v).part p := by
  have hp := SVec.apply_mem_part (t.app_mem p v) (unitVector_even D Sc cutoff L ν)
  rw [zero_add] at hp
  exact hp

@[simp] theorem evaluate_fromElement (m : (F).obj v) :
    evaluate D Sc cutoff L ν M (fromElement D Sc cutoff L ν M m) = m := by
  change component D Sc cutoff L ν M m 0 v (powerWordGenerator D Sc cutoff L ν v (𝟙 v)) +
    component D Sc cutoff L ν M m 1 v (powerWordGenerator D Sc cutoff L ν v (𝟙 v)) = m
  rw [component_generator, component_generator, twist_id, twist_id]
  have hi : (F).map (𝟙 v : v ⟶ v) = 𝟙 ((F).obj v) := (F).toFunctor.map_id v
  rw [hi]
  exact ((F).obj v).proj_apply_add m

/-- Every component on every word generator is forced by enriched naturality. -/
theorem app_generator (t : W ⟶ F) (p : ZMod 2) (w : OldCategory D Sc cutoff) (h : v ⟶ w) :
    t.app p w (powerWordGenerator D Sc cutoff L ν w h) =
      (F).map (twist k p h) (t.app p v (unitVector D Sc cutoff L ν)) := by
  refine induction_on (R := k) h ?_ ?_ ?_
  · simp [Superfunctor.map]
  · intro q h hh
    have hn := congrArg (fun a => a (unitVector D Sc cutoff L ν)) (t.naturality p h hh)
    change t.app p w ((W).map h (powerWordGenerator D Sc cutoff L ν v (𝟙 v))) =
      koszulSign p q • (F).map h (t.app p v (unitVector D Sc cutoff L ν)) at hn
    rw [generator_naturality, Category.id_comp, koszulSign_smul (R := k)] at hn
    rw [twist_of_mem p hh]
    simpa only [Superfunctor.map, Functor.map_smul, SVec.smul_apply] using hn
  · intro a b ha hb
    simp only [map_add, Superfunctor.map, Functor.map_add, SVec.add_apply, ha, hb]

theorem evaluate_component (t : W ⟶ F) (p : ZMod 2) :
    ((F).obj v).proj p (evaluate D Sc cutoff L ν M t) =
      t.app p v (unitVector D Sc cutoff L ν) := by
  rw [evaluate, map_add, SVec.proj_apply_of_mem_part _ (evaluate_part D Sc cutoff L ν M t 0),
    SVec.proj_apply_of_mem_part _ (evaluate_part D Sc cutoff L ν M t 1)]
  rcases parity_eq_zero_or_one p with rfl | rfl <;> simp

theorem fromElement_evaluate (t : W ⟶ F) :
    fromElement D Sc cutoff L ν M (evaluate D Sc cutoff L ν M t) = t := by
  apply Superfunctor.hom_ext
  intro p w
  apply LinearMap.ext
  intro x
  obtain ⟨h, rfl⟩ := powerWordGenerator_surjective D Sc cutoff L ν w x
  change component D Sc cutoff L ν M (evaluate D Sc cutoff L ν M t) p w
    (powerWordGenerator D Sc cutoff L ν w h) = _
  rw [component_generator, evaluate_component]
  exact (app_generator D Sc cutoff L ν M t p w h).symm

/-- Enriched Yoneda for the actual induced regular A/T word module. -/
def homEquiv : (W ⟶ F) ≃ₗ[k] (F).obj v where
  toFun := evaluate D Sc cutoff L ν M
  invFun := fromElement D Sc cutoff L ν M
  left_inv := fromElement_evaluate D Sc cutoff L ν M
  right_inv := evaluate_fromElement D Sc cutoff L ν M
  map_add' t s := by
    change (t.app 0 v (unitVector D Sc cutoff L ν) + s.app 0 v (unitVector D Sc cutoff L ν)) +
      (t.app 1 v (unitVector D Sc cutoff L ν) + s.app 1 v (unitVector D Sc cutoff L ν)) =
      (t.app 0 v (unitVector D Sc cutoff L ν) + t.app 1 v (unitVector D Sc cutoff L ν)) +
      (s.app 0 v (unitVector D Sc cutoff L ν) + s.app 1 v (unitVector D Sc cutoff L ν))
    abel
  map_smul' r t := by
    change r • t.app 0 v (unitVector D Sc cutoff L ν) + r • t.app 1 v (unitVector D Sc cutoff L ν) =
      r • (t.app 0 v (unitVector D Sc cutoff L ν) + t.app 1 v (unitVector D Sc cutoff L ν))
    exact (smul_add _ _ _).symm

theorem evaluate_proj (t : W ⟶ F) (p : ZMod 2) :
    evaluate D Sc cutoff L ν M (proj k p t) =
      ((F).obj v).proj p (evaluate D Sc cutoff L ν M t) := by
  rw [evaluate_component]
  rcases parity_eq_zero_or_one p with rfl | rfl
  · change (proj k 0 t).app 0 v (unitVector D Sc cutoff L ν) +
      (proj k 0 t).app 1 v (unitVector D Sc cutoff L ν) = _
    simp only [Superfunctor.proj_app, ite_true, one_ne_zero, ite_false]
    exact add_zero _
  · change (proj k 1 t).app 0 v (unitVector D Sc cutoff L ν) +
      (proj k 1 t).app 1 v (unitVector D Sc cutoff L ν) = _
    simp only [Superfunctor.proj_app, ite_true, zero_ne_one, ite_false]
    exact zero_add _

end OddMath.QuiverHecke.ELVOld.PowerWordYoneda
