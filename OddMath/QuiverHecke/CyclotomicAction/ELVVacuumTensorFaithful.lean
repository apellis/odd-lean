import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumTensor

/-! # Faithfulness of tensor vacuum transformations at a generating module

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §8, the
Nondegeneracy Conjecture (research scope of `FieldScopeBoundary.md`): input to
the vacuum-entry match of the positive-height bubble field.

For a superfunctor `G` followed by the tensor vacuum `M ↦ W ⊗ M(a)`, a
supernatural transformation out of it is determined by its components at one
object `Y₀`, provided every homogeneous vector of every `(G X)(a)` is the image of
a fixed vector `y₀ ∈ (G Y₀)(a)` under `G f` for a homogeneous `f : Y₀ ⟶ X` of the
same parity. This is
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

variable {P : Type u} [Category.{u} P] [Preadditive P] [Linear k P] [Supercategory k P]

/-- The signed naturality of a transformation out of `G` followed by the tensor
vacuum, evaluated on `v ⊗ y` along a morphism `f` of parity `q`. -/
theorem app_tmul_of_naturality (W : Superfunctor k C (SVec k)) (a : A)
    (G : Superfunctor k P (Superfunctor k A (SVec k)))
    {H : Superfunctor k P (Superfunctor k C (SVec k))}
    (χ : G.comp (superfunctor W a) ⟶ H) (p r : ZMod 2) {Y M : P}
    {q : ZMod 2} (f : Y ⟶ M) (hfm : f ∈ parity (R := k) Y M q) (c : C) {s : ZMod 2}
    {v : W.obj c} (hv : v ∈ (W.obj c).part s) (y : (G.obj Y).obj a) :
    sign k (s * q) • (χ.app p M).app (r + q) c (v ⊗ₜ[k] (G.map f).app q a y) =
      koszulSign p q • ((χ.app p Y ≫ H.map f).app r c) (v ⊗ₜ[k] y) := by
  have hf : (G.map f).app (q + 1) = 0 := Superfunctor.mem_parityHom.mp (G.map_mem hfm)
  have h := congrArg
    (fun x : (G.comp (superfunctor W a)).obj Y ⟶ H.obj M => (x.app r c) (v ⊗ₜ[k] y))
    (χ.naturality p f hfm)
  rw [Superfunctor.zsmul_app, SVec.zsmul_apply] at h
  rw [← h, Superfunctor.comp_app, SVec.add_apply, SVec.comp_apply, SVec.comp_apply]
  have hz : ((G.comp (superfunctor W a)).map f).app (q + 1) c = 0 := by
    change SVec.whiskerLeft (W.obj c) ((G.map f).app (q + 1) a) = 0
    rw [congrFun hf a]; exact SVec.whiskerLeft_zero _
  have ht : ∀ q', ((G.comp (superfunctor W a)).map f).app q' c (v ⊗ₜ[k] y) =
      sign k (s * q') • (v ⊗ₜ[k] (G.map f).app q' a y) := fun q' =>
    superfunctor_map_app_tmul W a (G.map f) s q' c v hv y
  rcases parity_eq_zero_or_one q with rfl | rfl
  · rw [zero_add] at hz
    rw [hz, SVec.zero_apply, map_zero, add_zero, add_zero, ht]
    simp
  · rw [SVec.zmod2_one_add_one] at hz
    rw [hz, SVec.zero_apply, map_zero, zero_add, ht, map_smul]

/-- **Faithfulness at a generating object.** Two transformations out of `G`
followed by the tensor vacuum `M ↦ W ⊗ M(a)` agree if they agree at `Y₀`,
provided every homogeneous vector of every `(G X)(a)` is `(G f)(y₀)` for a
homogeneous `f : Y₀ ⟶ X` of its parity. -/
theorem hom_ext_of_generating (W : Superfunctor k C (SVec k)) (a : A)
    (G : Superfunctor k P (Superfunctor k A (SVec k)))
    {H : Superfunctor k P (Superfunctor k C (SVec k))}
    {Y₀ : P} (y₀ : (G.obj Y₀).obj a)
    (hgen : ∀ (X : P) (q : ZMod 2) (m : (G.obj X).obj a),
      m ∈ ((G.obj X).obj a).part q →
        ∃ f : Y₀ ⟶ X, f ∈ parity (R := k) Y₀ X q ∧ (G.map f).app q a y₀ = m)
    {φ ψ : G.comp (superfunctor W a) ⟶ H} (h : ∀ p, φ.app p Y₀ = ψ.app p Y₀) : φ = ψ := by
  apply Superfunctor.hom_ext
  intro p X
  apply Superfunctor.hom_ext
  intro r c
  apply SVec.hom_ext
  intro x
  change SVec.toLinearMap ((φ.app p X).app r c) x = SVec.toLinearMap ((ψ.app p X).app r c) x
  congr 1
  apply SVec.ext_tensor
  intro s q v m hv hm
  obtain ⟨f, hf, rfl⟩ := hgen X q m hm
  have hφ := app_tmul_of_naturality W a G φ p (r + q) f hf c hv y₀
  have hψ := app_tmul_of_naturality W a G ψ p (r + q) f hf c hv y₀
  rw [h p] at hφ
  have hrq : r + q + q = r := by
    rcases parity_eq_zero_or_one q with rfl | rfl <;> simp [add_assoc]
  rw [hrq] at hφ hψ
  have := hφ.trans hψ.symm
  have := congrArg (fun z => sign k (s * q) • z) this
  simp only [sign_smul_sign_smul] at this
  exact this

/-- Faithfulness at a generating object, read on the total components. -/
theorem hom_ext_of_generating_total (W : Superfunctor k C (SVec k)) (a : A)
    (G : Superfunctor k P (Superfunctor k A (SVec k)))
    {H : Superfunctor k P (Superfunctor k C (SVec k))}
    {Y₀ : P} (y₀ : (G.obj Y₀).obj a)
    (hgen : ∀ (X : P) (q : ZMod 2) (m : (G.obj X).obj a),
      m ∈ ((G.obj X).obj a).part q →
        ∃ f : Y₀ ⟶ X, f ∈ parity (R := k) Y₀ X q ∧ (G.map f).app q a y₀ = m)
    {φ ψ : G.comp (superfunctor W a) ⟶ H}
    (h : SuperNatTrans.total φ Y₀ = SuperNatTrans.total ψ Y₀) : φ = ψ := by
  apply hom_ext_of_generating W a G y₀ hgen
  have hp : ∀ χ : G.comp (superfunctor W a) ⟶ H, ∀ p,
      χ.app p Y₀ = Supercategory.proj (R := k) p (SuperNatTrans.total χ Y₀) := by
    intro χ p
    rcases parity_eq_zero_or_one p with rfl | rfl
    · exact (Supercategory.proj_eq_of_add (R := k) rfl (χ.app_mem 0 Y₀) (χ.app_mem 1 Y₀)).symm
    · exact (Supercategory.proj_eq_of_add (R := k) (add_comm _ _) (χ.app_mem 1 Y₀)
        (χ.app_mem 0 Y₀)).symm
  intro p
  rw [hp φ, hp ψ, h]

end OddMath.QuiverHecke.ELVOld.VacuumTensor
