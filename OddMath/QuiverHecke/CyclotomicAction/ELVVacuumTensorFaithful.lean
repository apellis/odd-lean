import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumTensor

/-! # Faithfulness of tensor vacuum transformations at a generating module

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §8, the
Nondegeneracy Conjecture (research scope of `FieldScopeBoundary.md`): input to
the vacuum-entry match of the positive-height bubble field.

For the tensor vacuum superfunctor `M ↦ W ⊗ M(a)`, a supernatural
transformation out of it is determined by its components at one module `Y₀`,
provided every homogeneous vector of every `M(a)` is the image of a fixed vector
`y₀ ∈ Y₀(a)` under a homogeneous morphism `Y₀ ⟶ M` of the same parity. This is
the Yoneda step: the vacuum entries of the tensor vacuum are read at the regular
probe.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld.VacuumTensor
universe u
variable {k A C : Type u} [CommRing k]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]

/-- The signed naturality of a transformation out of the tensor vacuum,
evaluated on `v ⊗ y` along a morphism `f` of parity `q`. -/
theorem app_tmul_of_naturality (W : Superfunctor k C (SVec k)) (a : A)
    {H : Superfunctor k (Superfunctor k A (SVec k)) (Superfunctor k C (SVec k))}
    (χ : superfunctor W a ⟶ H) (p r : ZMod 2) {Y M : Superfunctor k A (SVec k)}
    {q : ZMod 2} (f : Y ⟶ M) (hf : f.app (q + 1) = 0) (c : C) {s : ZMod 2}
    {v : W.obj c} (hv : v ∈ (W.obj c).part s) (y : Y.obj a) :
    sign k (s * q) • (χ.app p M).app (r + q) c (v ⊗ₜ[k] f.app q a y) =
      koszulSign p q • ((χ.app p Y ≫ H.map f).app r c) (v ⊗ₜ[k] y) := by
  have hfm : f ∈ parity (R := k) Y M q := Superfunctor.mem_parityHom.mpr hf
  have h := congrArg (fun x : (superfunctor W a).obj Y ⟶ H.obj M => (x.app r c) (v ⊗ₜ[k] y)) (χ.naturality p f hfm)
  rw [Superfunctor.zsmul_app, SVec.zsmul_apply] at h
  rw [← h, Superfunctor.comp_app, SVec.add_apply, SVec.comp_apply, SVec.comp_apply]
  have hz : ∀ c', ((superfunctor W a).map f).app (q + 1) c' = 0 := fun c' => by
    rw [superfunctor_map_app, congrFun hf a]; exact SVec.whiskerLeft_zero _
  rcases parity_eq_zero_or_one q with rfl | rfl
  · have h1 := hz c
    simp only [zero_add] at h1
    rw [h1, SVec.zero_apply, map_zero, add_zero, add_zero,
      superfunctor_map_app_tmul W a f s 0 c v hv y]
    simp
  · have h0 := hz c
    rw [SVec.zmod2_one_add_one] at h0
    rw [h0, SVec.zero_apply, map_zero, zero_add,
      superfunctor_map_app_tmul W a f s 1 c v hv y, map_smul]

/-- **Faithfulness at a generating module.** Two transformations out of the
tensor vacuum `M ↦ W ⊗ M(a)` agree if they agree at `Y₀`, provided every
homogeneous vector of every `M(a)` is `f(y₀)` for a homogeneous `f : Y₀ ⟶ M`
of its parity. -/
theorem hom_ext_of_generating (W : Superfunctor k C (SVec k)) (a : A)
    {H : Superfunctor k (Superfunctor k A (SVec k)) (Superfunctor k C (SVec k))}
    {Y₀ : Superfunctor k A (SVec k)} (y₀ : Y₀.obj a)
    (hgen : ∀ (M : Superfunctor k A (SVec k)) (q : ZMod 2) (m : M.obj a),
      m ∈ (M.obj a).part q → ∃ f : Y₀ ⟶ M, f.app (q + 1) = 0 ∧ f.app q a y₀ = m)
    {φ ψ : superfunctor W a ⟶ H} (h : ∀ p, φ.app p Y₀ = ψ.app p Y₀) : φ = ψ := by
  apply Superfunctor.hom_ext
  intro p M
  apply Superfunctor.hom_ext
  intro r c
  apply SVec.hom_ext
  intro x
  change SVec.toLinearMap ((φ.app p M).app r c) x = SVec.toLinearMap ((ψ.app p M).app r c) x
  congr 1
  apply SVec.ext_tensor
  intro s q v m hv hm
  obtain ⟨f, hf, rfl⟩ := hgen M q m hm
  have hφ := app_tmul_of_naturality W a φ p (r + q) f hf c hv y₀
  have hψ := app_tmul_of_naturality W a ψ p (r + q) f hf c hv y₀
  rw [h p] at hφ
  have hrq : r + q + q = r := by
    rcases parity_eq_zero_or_one q with rfl | rfl <;> simp [add_assoc]
  rw [hrq] at hφ hψ
  have := hφ.trans hψ.symm
  have := congrArg (fun z => sign k (s * q) • z) this
  simp only [sign_smul_sign_smul] at this
  exact this

/-- Faithfulness at a generating module, read on the total components. -/
theorem hom_ext_of_generating_total (W : Superfunctor k C (SVec k)) (a : A)
    {H : Superfunctor k (Superfunctor k A (SVec k)) (Superfunctor k C (SVec k))}
    {Y₀ : Superfunctor k A (SVec k)} (y₀ : Y₀.obj a)
    (hgen : ∀ (M : Superfunctor k A (SVec k)) (q : ZMod 2) (m : M.obj a),
      m ∈ (M.obj a).part q → ∃ f : Y₀ ⟶ M, f.app (q + 1) = 0 ∧ f.app q a y₀ = m)
    {φ ψ : superfunctor W a ⟶ H}
    (h : SuperNatTrans.total φ Y₀ = SuperNatTrans.total ψ Y₀) : φ = ψ := by
  apply hom_ext_of_generating W a y₀ hgen
  intro p
  have hp : ∀ χ : superfunctor W a ⟶ H, ∀ p,
      χ.app p Y₀ = Supercategory.proj (R := k) p (SuperNatTrans.total χ Y₀) := by
    intro χ p
    rcases parity_eq_zero_or_one p with rfl | rfl
    · exact (Supercategory.proj_eq_of_add (R := k) rfl (χ.app_mem 0 Y₀) (χ.app_mem 1 Y₀)).symm
    · exact (Supercategory.proj_eq_of_add (R := k) (add_comm _ _) (χ.app_mem 1 Y₀)
        (χ.app_mem 0 Y₀)).symm
  rw [hp φ, hp ψ, h]

end OddMath.QuiverHecke.ELVOld.VacuumTensor
