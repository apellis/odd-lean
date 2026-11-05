import OddMath.QuiverHecke.CyclotomicAction.ELVWeightTensorVacuum
import OddMath.QuiverHecke.CyclotomicAction.ELVEmptyCoefficientEmbedding

/-! # The regular empty probe generates the empty block

InverseColumnMoments, open item 1 (faithfulness of the regular-probe
evaluation). Every object of the old empty-content category is the empty
object, and every endomorphism of it is a coefficient. Scalar-evaluated
modules therefore see each endomorphism as one common scalar. Hence every
homogeneous vector of the empty block of a probe weight product is the image of
the prescribed empty idempotent under a morphism out of the regular probe, of
the same parity. This is the generating hypothesis of
`VacuumTensor.hom_ext_of_generating` for `emptyProbe` at `regularProbe`.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct Classical
namespace OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
open CyclotomicAction SwappedAssembly
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ)

local notation "cut" => probeCutoff D m
local notation "ev" => SKM.SYM.elvScalarEvaluation D cut (probeScalarValues D m)
  (probeScalarValues_vanish D m)
local notation "vac" => probeOldVacuumObject D Sc m
local notation "Reg" => probeOldVacuumRegular D Sc m

omit [Fintype I] in
/-- The old empty-content category has the empty object only. -/
theorem emptyObject_eq (v : OldContentCategory D Sc (probeCutoff D m) []) : v = vac := by
  obtain ⟨⟨w⟩, hw⟩ := v
  obtain rfl : w = [] := hw.eq_nil
  rfl

omit [Fintype I] in
/-- Every endomorphism of the empty object is the old coefficient of its
affine empty-word coordinate. -/
theorem vacuumEnd_eq (f : vac ⟶ vac) :
    f = probeOldCoefficient D m Sc [] vac (emptyCoefficientDecoder D Sc cut f) :=
  (emptyCoefficientEncoder_decoder D Sc cut f).symm

omit [Fintype I] in
/-- A scalar-evaluated module sees each empty endomorphism as one scalar,
determined by the endomorphism alone. -/
theorem vacuum_map_eq (N : Superfunctor k (OldContentCategory D Sc (probeCutoff D m) []) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc [] N) (f : vac ⟶ vac) :
    N.map f = ev (emptyCoefficientDecoder D Sc cut f) • 𝟙 (N.obj vac) := by
  have h := hN vac (emptyCoefficientDecoder D Sc cut f)
  rwa [← vacuumEnd_eq] at h

/-- An odd endomorphism of the regular empty probe vanishes: the probe is purely even. -/
theorem regular_odd_eq_zero {g : (Reg).obj vac ⟶ (Reg).obj vac} (hg : g ∈ parity (R := k) _ _ 1) :
    g = 0 := by
  apply SVec.hom_ext
  intro x
  have h := LinearMap.congr_fun (hg 0) x
  change g (((Reg).obj vac).proj 0 x) = ((Reg).obj vac).proj (0 + 1) (g x) at h
  rw [SVec.proj_apply_of_mem_part _ (probeVacuum_even D Sc m x),
    SVec.proj_apply_of_mem_part _ (probeVacuum_even D Sc m (g x))] at h
  simpa using h

section Hom
variable (N : Superfunctor k (OldContentCategory D Sc (probeCutoff D m) []) (SVec k))

/-- The scalar coordinate of the regular probe, followed by `n`. -/
def vacuumLinear (n : N.obj vac) : (Reg).obj vac ⟶ N.obj vac :=
  SVec.ofHom (LinearMap.smulRight (probeVacuumScalarEquiv D Sc m).symm.toLinearMap n)

theorem vacuumLinear_apply (n : N.obj vac) (x : (Reg).obj vac) :
    vacuumLinear D Sc m N n x = (probeVacuumScalarEquiv D Sc m).symm x • n := rfl

theorem vacuumLinear_mem (q : ZMod 2) (n : N.obj vac) (hn : n ∈ (N.obj vac).part q) :
    vacuumLinear D Sc m N n ∈ parity (R := k) ((Reg).obj vac) (N.obj vac) q := by
  apply SVec.mem_parityHom_of_apply_mem
  intro r x hx
  rw [vacuumLinear_apply]
  rcases parity_eq_zero_or_one r with rfl | rfl
  · rw [zero_add]
    exact Submodule.smul_mem _ _ hn
  · have h0 := SVec.proj_apply_of_mem_part ((Reg).obj vac) (p := 0) hx
    rw [SVec.proj_apply_of_mem_part _ (probeVacuum_even D Sc m x)] at h0
    simp only [ite_true, zero_ne_one, ite_false] at h0
    rw [h0, map_zero, zero_smul]
    exact Submodule.zero_mem _

/-- Scalars of empty endomorphisms commute with `vacuumLinear`. -/
theorem vacuumLinear_natural (n : N.obj vac) (hN : ProbeEvaluatesCoefficients D m Sc [] N) (f : vac ⟶ vac) :
    vacuumLinear D Sc m N n ≫ N.map f = (Reg).map f ≫ vacuumLinear D Sc m N n := by
  rw [vacuum_map_eq D Sc m N hN, vacuum_map_eq D Sc m Reg (probeOldVacuumRegular_evaluates D Sc m),
    Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp]

/-- The components of the morphism out of the regular probe. -/
def vacuumApp (q : ZMod 2) (n : N.obj vac) (p : ZMod 2) (Y : OldContentCategory D Sc (probeCutoff D m) []) :
    (Reg).obj Y ⟶ N.obj Y :=
  if p = q then
    eqToHom (congrArg (Reg).obj (emptyObject_eq D Sc m Y)) ≫ vacuumLinear D Sc m N n ≫
      eqToHom (congrArg N.obj (emptyObject_eq D Sc m Y).symm)
  else 0

theorem vacuumApp_vac (q : ZMod 2) (n : N.obj vac) (p : ZMod 2) :
    vacuumApp D Sc m N q n p vac = if p = q then vacuumLinear D Sc m N n else 0 := by
  simp only [vacuumApp, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The morphism out of the regular empty probe carrying the prescribed
empty idempotent to `n`. -/
def vacuumHom (q : ZMod 2) (n : N.obj vac) (hN : ProbeEvaluatesCoefficients D m Sc [] N) (hn : n ∈ (N.obj vac).part q) :
    Reg ⟶ N where
  app := vacuumApp D Sc m N q n
  app_mem p Y := by
    obtain rfl := emptyObject_eq D Sc m Y
    rw [vacuumApp_vac]
    split_ifs with h
    · subst h
      exact vacuumLinear_mem D Sc m N p n hn
    · exact Submodule.zero_mem _
  naturality p Y Z q' f hf := by
    obtain rfl := emptyObject_eq D Sc m Y
    obtain rfl := emptyObject_eq D Sc m Z
    change (Reg).map f ≫ vacuumApp D Sc m N q n p vac =
      koszulSign p q' • (vacuumApp D Sc m N q n p vac ≫ N.map f)
    rw [vacuumApp_vac]
    split_ifs with h
    · rw [vacuumLinear_natural D Sc m N n hN f]
      rcases parity_eq_zero_or_one q' with rfl | rfl
      · rw [koszulSign_zero_right, one_smul]
      · rw [regular_odd_eq_zero D Sc m ((Reg).map_mem hf), Limits.zero_comp, smul_zero]
    · rw [Limits.comp_zero, Limits.zero_comp, smul_zero]

theorem vacuumHom_mem (q : ZMod 2) (n : N.obj vac) (hN : ProbeEvaluatesCoefficients D m Sc [] N)
    (hn : n ∈ (N.obj vac).part q) :
    vacuumHom D Sc m N q n hN hn ∈ parity (R := k) Reg N q := by
  apply Superfunctor.mem_parityHom.mpr
  change vacuumApp D Sc m N q n (q + 1) = 0
  funext Y
  obtain rfl := emptyObject_eq D Sc m Y
  have hne : q + 1 ≠ q := by
    intro h
    have : (1 : ZMod 2) = 0 := by simpa using congrArg (· - q) h
    exact one_ne_zero this
  rw [vacuumApp_vac]
  simp only [hne, ↓reduceIte]
  rfl

theorem vacuumHom_vector (q : ZMod 2) (n : N.obj vac) (hN : ProbeEvaluatesCoefficients D m Sc [] N)
    (hn : n ∈ (N.obj vac).part q) :
    (vacuumHom D Sc m N q n hN hn).app q vac (probeOldVacuumVector D Sc m) = n := by
  change vacuumApp D Sc m N q n q vac (probeOldVacuumVector D Sc m) = n
  rw [vacuumApp_vac, ite_eq_left_iff.mpr (fun h => (h rfl).elim), vacuumLinear_apply, ← probeVacuumScalarEquiv_one,
    LinearEquiv.symm_apply_apply, one_smul]

end Hom

omit [Fintype I] in
/-- The empty forgetful functor preserves scalar evaluation. -/
theorem emptyContentForget_evaluates (ν : List I) (h : ν = [])
    (M : ProbeEvaluatedModules D Sc m ν) :
    ProbeEvaluatesCoefficients D m Sc [] ((emptyContentForget D Sc m ν h).obj M) := by
  subst h
  exact M.property

omit [Fintype I] in
/-- The empty forgetful functor is full, with parity. -/
theorem emptyContentForget_preimage (ν : List I) (h : ν = [])
    {M M' : ProbeEvaluatedModules D Sc m ν} {q : ZMod 2}
    (τ : (emptyContentForget D Sc m ν h).obj M ⟶ (emptyContentForget D Sc m ν h).obj M')
    (hτ : τ ∈ parity (R := k) _ _ q) :
    ∃ g : M ⟶ M', g ∈ parity (R := k) M M' q ∧ (emptyContentForget D Sc m ν h).map g = τ := by
  subst h
  exact ⟨⟨τ⟩, hτ, rfl⟩

omit [Fintype I] in
private theorem eqToHom_comp_app {F G H : Superfunctor k (OldContentCategory D Sc
    (probeCutoff D m) []) (SVec k)} (e : F = G) (e' : G = F) (τ : G ⟶ H) (q : ZMod 2) (Y)
    (y : G.obj Y) : ((eqToHom e ≫ τ).app q Y) ((eqToHom e' : G ⟶ F).app 0 Y y) = τ.app q Y y := by
  subst e
  simp only [eqToHom_refl, Category.id_comp, Superfunctor.id_app_zero]
  rfl

/-- The prescribed empty idempotent, as a vector of the empty block of the regular probe. -/
def regularVector (Λ : X) : ((emptyProbe D Sc m Λ).obj (regularProbe D Sc m Λ)).obj vac :=
  (eqToHom (emptyProbe_regular D Sc m Λ).symm).app 0 vac (probeOldVacuumVector D Sc m)

/-- Every homogeneous vector of the empty block is the image of the regular
vector under a morphism out of the regular probe of the same parity. -/
theorem regularProbe_generating (Λ : X) (Y : ProbeOldWeightProduct D Sc m Λ (-Λ))
    (q : ZMod 2) (n : ((emptyProbe D Sc m Λ).obj Y).obj vac)
    (hn : n ∈ (((emptyProbe D Sc m Λ).obj Y).obj vac).part q) :
    ∃ f : regularProbe D Sc m Λ ⟶ Y, f ∈ parity (R := k) _ _ q ∧
      ((emptyProbe D Sc m Λ).map f).app q vac (regularVector D Sc m Λ) = n := by
  have hN := emptyContentForget_evaluates D Sc m _ Multiset.toList_zero (Y (emptyBlock D Λ))
  let τ := vacuumHom D Sc m _ q n hN hn
  have hτ' : eqToHom (emptyProbe_regular D Sc m Λ) ≫ τ ∈ parity (R := k) _ _ q := by
    simpa only [zero_add] using
      comp_mem (eqToHom_mem_parity_zero (emptyProbe_regular D Sc m Λ))
        (vacuumHom_mem D Sc m _ q n hN hn)
  obtain ⟨g, hg, hgm⟩ := emptyContentForget_preimage D Sc m _ Multiset.toList_zero
    (M := regularProbe D Sc m Λ (emptyBlock D Λ)) (M' := Y (emptyBlock D Λ)) _ hτ'
  let f : regularProbe D Sc m Λ ⟶ Y := fun β =>
    if h : β = emptyBlock D Λ then (by subst h; exact g) else 0
  have hf : f (emptyBlock D Λ) = g := by
    simp only [f, ↓reduceDIte]
  refine ⟨f, ?_, ?_⟩
  · intro β
    by_cases h : β = emptyBlock D Λ
    · subst h
      rw [hf]
      exact hg
    · simp only [f, h, ↓reduceDIte]
      exact Submodule.zero_mem _
  · change ((emptyContentForget D Sc m _ Multiset.toList_zero).map
      (f (emptyBlock D Λ))).app q vac (regularVector D Sc m Λ) = n
    rw [hf, hgm, regularVector]
    exact (eqToHom_comp_app D Sc m _ _ τ q vac _).trans (vacuumHom_vector D Sc m _ q n hN hn)

end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
