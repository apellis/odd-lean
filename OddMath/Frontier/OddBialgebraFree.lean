import OddMath.Frontier.OddBialgebraShuffle
import OddMath.Frontier.OddBialgebraWindow

/-!
# `ONH_{a+b}` is free over `ONH_a ⊗ ONH_b`

EKL arXiv:1111.1320v1, §6, pp. 46–47: restriction along `ONH_a ⊗ ONH_b ⊂ ONH_{a+b}`. Here
`a = m+2`, `b = m'+2`, `B = OnhStructure.tensorImage m m' ⊂ ONH_{a+b}` is the image of
`ONH_a ⊗ ONH_b`.

* `psi_bijective`: `⊕_{u} (ONH_a ⊗_ℤ ONH_b) → ONH_{a+b}`, `(t_u) ↦ ∑_u t_u ∂_u` (`u` running
  over the shuffles), is a bijection of `ℤ`-modules: it carries the tensor PBW basis to `±` the PBW basis
  of `ONH_{a+b}`, `x^{A₁}∂_{y₁} ⊗ x^{A₂}∂_{y₂} ⊗ u ↦ ± x^{A₁ ⊔ A₂} ∂_{(y₁ × y₂)u}` (Prop 2.11,
  `exists_factor`, `factor_unique`, `length_blockPerm_mul`).
* `freeBasis : Basis (Shuffle m m') B ONH_{a+b}`, `u ↦ ∂_u`: `ONH_{a+b}` is a free left
  `B`-module of rank `C(a+b, a)` (`card_shuffle`).
* The coordinates are graded: for `x` of degree `d`, the `∂_u`-coordinate of `x` has degree
  `d + 2ℓ(u)` (`coord_mem`), for the grading `gradB` of `B` restricted from `ONH_{a+b}`.
-/

noncomputable section
open scoped TensorProduct

namespace OddMath.Frontier.OddBialgebra
open NilCoxeterWords NilHeckeAction NilHeckeBasis OnhStructure OnhWindow GradedK0
  OddCategorification

variable {m m' : ℕ}

/-! ### The shuffle basis over `ℤ` -/

/-- `∂_u`. -/
def dshuf (u : Shuffle m m') : Presented (m+2+m') := dividedElement u.1

/-- The PBW index of `x^{A₁}∂_{y₁} ⊗ x^{A₂}∂_{y₂} ⊗ ∂_u`. -/
def shufIndex (x : Σ _ : Shuffle m m', ((Fin (m+2) → ℕ) × Perm m) × ((Fin (m'+2) → ℕ) × Perm m')) :
    (Fin (m+2+m'+2) → ℕ) × Perm (m+2+m') :=
  (appendExp x.2.1.1 x.2.2.1, blockPerm x.2.1.2 x.2.2.2 * x.1.1)

theorem shufIndex_bijective : Function.Bijective (shufIndex (m := m) (m' := m')) := by
  refine ⟨fun x y h => ?_, fun p => ?_⟩
  · obtain ⟨u, ⟨A, w⟩, ⟨A', v⟩⟩ := x
    obtain ⟨u', ⟨C, w'⟩, ⟨C', v'⟩⟩ := y
    simp only [shufIndex, Prod.mk.injEq] at h
    obtain ⟨hA, hw⟩ := h
    have eA : A = C := funext fun i => by
      simpa [appendExp] using congrFun hA (Fin.castAdd (m'+2) i)
    have eB : A' = C' := funext fun j => by
      simpa [appendExp] using congrFun hA (Fin.natAdd (m+2) j)
    obtain ⟨hy, hu⟩ := factor_unique (y := (w, v)) (z := (w', v')) u.2 u'.2 hw
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 hy
    obtain rfl : u = u' := Subtype.ext hu
    rw [eA, eB]
  · obtain ⟨A, w⟩ := p
    obtain ⟨y, u, hu, rfl⟩ := exists_factor w
    refine ⟨⟨⟨u, hu⟩, ⟨fun i => A (Fin.castAdd (m'+2) i), y.1⟩,
      ⟨fun j => A (Fin.natAdd (m+2) j), y.2⟩⟩, ?_⟩
    simp only [shufIndex, appendExp, Fin.append_castAdd_natAdd]

theorem signed_mul_dshuf (A : Fin (m+2) → ℕ) (w : Perm m) (A' : Fin (m'+2) → ℕ) (v : Perm m')
    (u : Shuffle m m') :
    Signed (tensorMap m m' (basis m (A, w) ⊗ₜ basis m' (A', v)) * dshuf u)
      (basis (m+2+m') (appendExp A A', blockPerm w v * u.1)) := by
  rw [tensorMap_tmul, basis_apply, basis_apply, basis_apply]
  have h1 := incL_mul_incR_basis A w A' v
  have h2 : Signed (dividedElement (blockPerm w v) * dshuf u)
      (dividedElement (blockPerm w v * u.1)) :=
    dividedElement_mul_additive _ _ (length_blockPerm_mul w v u.2)
  refine (h1.mul (Signed.refl (dshuf u))).trans ?_
  rw [basisElement, basisElement, mul_assoc]
  exact (Signed.refl _).mul h2

/-- `(t_u) ↦ ∑_u t_u ∂_u`. -/
def psi : (Shuffle m m' →₀ Presented m ⊗[ℤ] Presented m') →ₗ[ℤ] Presented (m+2+m') :=
  Finsupp.lsum ℤ fun u => (LinearMap.mulRight ℤ (dshuf u)) ∘ₗ tensorMap m m'

theorem psi_single (u : Shuffle m m') (t : Presented m ⊗[ℤ] Presented m') :
    psi (Finsupp.single u t) = tensorMap m m' t * dshuf u := by
  simp [psi]

/-- The `ℤ`-basis of `⊕_u ONH_a ⊗ ONH_b`. -/
def tensorShufBasis :
    Basis (Σ _ : Shuffle m m', ((Fin (m+2) → ℕ) × Perm m) × ((Fin (m'+2) → ℕ) × Perm m')) ℤ
      (Shuffle m m' →₀ Presented m ⊗[ℤ] Presented m') :=
  Finsupp.basis fun _ => (basis m).tensorProduct (basis m')

theorem psi_basis (x : Σ _ : Shuffle m m', ((Fin (m+2) → ℕ) × Perm m) ×
    ((Fin (m'+2) → ℕ) × Perm m')) :
    Signed (psi (tensorShufBasis x)) (basis (m+2+m') (shufIndex x)) := by
  obtain ⟨u, ⟨A, w⟩, ⟨A', v⟩⟩ := x
  rw [tensorShufBasis, Finsupp.coe_basis, psi_single, Basis.tensorProduct_apply]
  exact signed_mul_dshuf A w A' v u

/-- A linear map carrying a basis to `±` a basis along a surjection is surjective. -/
theorem surjective_of_signed_basis {ι ι' M M' : Type*} [AddCommGroup M] [AddCommGroup M']
    (b : Basis ι ℤ M) (b' : Basis ι' ℤ M') (T : M →ₗ[ℤ] M') (φ : ι → ι')
    (hφ : Function.Surjective φ) (hT : ∀ i, Signed (T (b i)) (b' (φ i))) :
    Function.Surjective T := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← b'.span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  obtain ⟨i, rfl⟩ := hφ j
  rcases hT i with h | h
  · exact ⟨b i, h⟩
  · exact ⟨-b i, by rw [map_neg, h, neg_neg]⟩

/-- `⊕_u ONH_a ⊗ ONH_b ≅ ONH_{a+b}`, `(t_u) ↦ ∑_u t_u ∂_u`, as `ℤ`-modules. -/
theorem psi_bijective : Function.Bijective (psi (m := m) (m' := m')) :=
  ⟨injective_of_signed_basis tensorShufBasis (basis _) psi shufIndex shufIndex_bijective.1
      psi_basis,
    surjective_of_signed_basis tensorShufBasis (basis _) psi shufIndex shufIndex_bijective.2
      psi_basis⟩

/-! ### The basis over `B = ONH_a ⊗ ONH_b` -/

/-- `t ↦ tensorMap t ∈ B`. -/
def toB : Presented m ⊗[ℤ] Presented m' →+ tensorImage m m' where
  toFun t := ⟨tensorMap m m' t, t, rfl⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-- A preimage in `ONH_a ⊗ ONH_b` of an element of `B`. -/
def ofB : tensorImage m m' →+ Presented m ⊗[ℤ] Presented m' :=
  ((tensorEquiv m m').symm.toLinearMap.toAddMonoidHom).comp
    { toFun := fun b => ⟨b, LinearMap.mem_range.2 b.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

theorem toB_ofB (b : tensorImage m m') : toB (ofB b) = b := by
  refine Subtype.ext ?_
  show tensorMap m m' ((tensorEquiv m m').symm _) = _
  have := (tensorEquiv m m').apply_symm_apply ⟨b, LinearMap.mem_range.2 b.2⟩
  exact congrArg Subtype.val this

/-- `(b_u) ↦ ∑_u b_u ∂_u`. -/
def lcomb : (Shuffle m m' →₀ tensorImage m m') →ₗ[tensorImage m m'] Presented (m+2+m') :=
  Finsupp.linearCombination _ dshuf

theorem lcomb_single (u : Shuffle m m') (b : tensorImage m m') :
    lcomb (Finsupp.single u b) = (b : Presented (m+2+m')) * dshuf u := by
  simp [lcomb, Finsupp.linearCombination_single]
  rfl

theorem lcomb_mapRange (f : Shuffle m m' →₀ Presented m ⊗[ℤ] Presented m') :
    lcomb (Finsupp.mapRange.addMonoidHom toB f) = psi f := by
  have h : (lcomb (m := m) (m' := m')).toAddMonoidHom.comp (Finsupp.mapRange.addMonoidHom toB) =
      psi.toAddMonoidHom := Finsupp.addHom_ext fun u t => by
    simp only [AddMonoidHom.comp_apply, Finsupp.mapRange.addMonoidHom_apply,
      Finsupp.mapRange_single, LinearMap.toAddMonoidHom_coe, lcomb_single, psi_single]
    rfl
  exact DFunLike.congr_fun h f

theorem lcomb_bijective : Function.Bijective (lcomb (m := m) (m' := m')) := by
  have hid : (Finsupp.mapRange.addMonoidHom (toB (m := m) (m' := m'))).comp
      (Finsupp.mapRange.addMonoidHom ofB) =
      AddMonoidHom.id (Shuffle m m' →₀ tensorImage m m') := by
    rw [← Finsupp.mapRange.addMonoidHom_comp]
    have : toB.comp ofB = AddMonoidHom.id (tensorImage m m') := AddMonoidHom.ext toB_ofB
    rw [this, Finsupp.mapRange.addMonoidHom_id]
  have hl : ∀ l, l = Finsupp.mapRange.addMonoidHom toB (Finsupp.mapRange.addMonoidHom ofB l) :=
    fun l => (DFunLike.congr_fun hid l).symm
  refine ⟨fun l l' h => ?_, fun x => ?_⟩
  · rw [hl l, hl l', lcomb_mapRange, lcomb_mapRange] at h
    rw [hl l, hl l', psi_bijective.1 h]
  · obtain ⟨f, rfl⟩ := psi_bijective.2 x
    exact ⟨_, lcomb_mapRange f⟩

/-- **`ONH_{a+b}` is a free left module over `ONH_a ⊗ ONH_b`**, with basis `∂_u`, `u` a shuffle
(`C(a+b, a)` elements, `card_shuffle`). -/
def freeBasis : Basis (Shuffle m m') (tensorImage m m') (Presented (m+2+m')) :=
  Basis.ofRepr (LinearEquiv.ofBijective (lcomb (m := m) (m' := m')) lcomb_bijective).symm

theorem freeBasis_apply (u : Shuffle m m') : freeBasis u = dshuf u := by
  have h := (freeBasis (m := m) (m' := m')).repr_symm_single u 1
  rw [one_smul] at h
  rw [← h]
  show lcomb (Finsupp.single u 1) = _
  rw [lcomb_single, OneMemClass.coe_one, one_mul]

theorem freeBasis_repr_symm (l : Shuffle m m' →₀ tensorImage m m') :
    freeBasis.repr.symm l = lcomb l := rfl

/-! ### Gradings -/

/-- The grading of `B = ONH_a ⊗ ONH_b ⊂ ONH_{a+b}`, restricted from `ONH_{a+b}`. -/
def gradB (m m' : ℕ) (d : ℤ) : AddSubgroup (tensorImage m m') :=
  (onhGrading (m+2+m') d).comap (tensorImage m m').subtype.toAddMonoidHom

theorem mem_gradB {d : ℤ} {b : tensorImage m m'} :
    b ∈ gradB m m' d ↔ (b : Presented (m+2+m')) ∈ onhGrading (m+2+m') d := Iff.rfl

instance gradB.gradedMonoid : SetLike.GradedMonoid (gradB m m') where
  one_mem := NilHeckeGrading.unit_mem
  mul_mem _ _ _ _ hx hy := NilHeckeGrading.degreePiece_mul hx hy

theorem sum_appendExp (A : Fin (m+2) → ℕ) (A' : Fin (m'+2) → ℕ) :
    ∑ j, appendExp A A' j = ∑ i, A i + ∑ j, A' j := by
  have h := Fin.sum_univ_add (a := m+2) (b := m'+2) (Fin.append A A')
  simp only [Fin.append_left, Fin.append_right] at h
  exact h

theorem tensorMap_basis_mem (i : (Fin (m+2) → ℕ) × Perm m) (i' : (Fin (m'+2) → ℕ) × Perm m') :
    tensorMap m m' (basis m i ⊗ₜ basis m' i') ∈
      onhGrading (m+2+m') (NilHeckeGrading.weight i + NilHeckeGrading.weight i') := by
  rw [tensorMap_tmul, basis_apply, basis_apply]
  exact NilHeckeGrading.degreePiece_mul
    (winPiece_le _ _ _ (windowHom_mem _ (NilHeckeGrading.basisElement_mem i)))
    (winPiece_le _ _ _ (windowHom_mem _ (NilHeckeGrading.basisElement_mem i')))

theorem weight_shufIndex (u : Shuffle m m') (i : (Fin (m+2) → ℕ) × Perm m)
    (i' : (Fin (m'+2) → ℕ) × Perm m') :
    NilHeckeGrading.weight (shufIndex ⟨u, (i, i')⟩) =
      NilHeckeGrading.weight i + NilHeckeGrading.weight i' - 2 * (length u.1 : ℤ) := by
  simp only [NilHeckeGrading.weight, shufIndex, sum_appendExp,
    length_blockPerm_mul _ _ u.2, length_blockPerm]
  push_cast
  ring

theorem repr_psi_basis (x : Σ _ : Shuffle m m', ((Fin (m+2) → ℕ) × Perm m) ×
    ((Fin (m'+2) → ℕ) × Perm m')) :
    freeBasis.repr (psi (tensorShufBasis x)) =
      Finsupp.single x.1 (toB (basis m x.2.1 ⊗ₜ basis m' x.2.2)) := by
  rw [← lcomb_mapRange, ← freeBasis_repr_symm, LinearEquiv.apply_symm_apply, tensorShufBasis,
    Finsupp.coe_basis, Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_single,
    Basis.tensorProduct_apply]

/-- **The coordinates are graded**: for `x` of degree `e`, its `∂_u`-coordinate has degree
`e + 2ℓ(u)`. -/
theorem coord_mem {e : ℤ} {x : Presented (m+2+m')} (hx : x ∈ onhGrading (m+2+m') e)
    (u : Shuffle m m') : freeBasis.repr x u ∈ gradB m m' (e + 2 * (length u.1 : ℤ)) := by
  have hx' : x ∈ NilHeckeGrading.leftPiece (m+2+m') e := by
    rw [← NilHeckeGrading.degreePiece_eq_leftPiece]; exact hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨i, hi⟩, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := shufIndex_bijective.2 i
    obtain ⟨u', i₁, i₂⟩ := y
    have hs := (psi_basis ⟨u', (i₁, i₂)⟩).symm
    show freeBasis.repr (basisElement (shufIndex ⟨u', (i₁, i₂)⟩)) u ∈ _
    rw [← basis_apply]
    have hmem : toB (basis m i₁ ⊗ₜ basis m' i₂) ∈ gradB m m' (e + 2 * (length u'.1 : ℤ)) :=
      mem_of_deg_eq (tensorMap_basis_mem i₁ i₂)
        (by rw [← hi, weight_shufIndex]; ring)
    by_cases hu : u' = u
    · subst hu
      rcases hs with h | h <;> rw [h]
      · rw [repr_psi_basis, Finsupp.single_eq_same]; exact hmem
      · rw [map_neg, Finsupp.neg_apply, repr_psi_basis, Finsupp.single_eq_same]
        exact neg_mem hmem
    · rcases hs with h | h <;> rw [h]
      · rw [repr_psi_basis, Finsupp.single_eq_of_ne hu]; exact zero_mem _
      · rw [map_neg, Finsupp.neg_apply, repr_psi_basis, Finsupp.single_eq_of_ne hu, neg_zero]
        exact zero_mem _
  | zero => rw [map_zero, Finsupp.zero_apply]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add, Finsupp.add_apply]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [← Int.cast_smul_eq_zsmul (tensorImage m m'), map_smul, Finsupp.smul_apply, smul_eq_mul,
      ← zsmul_eq_mul]
    exact zsmul_mem hx c

/-! ### The regular representation over `B` -/

theorem repr_dshuf (u : Shuffle m m') : freeBasis.repr (dshuf u) = Finsupp.single u 1 := by
  rw [← freeBasis_apply, Basis.repr_self]

/-- Right multiplication on `ONH_{a+b} = ⊕_u B ∂_u`: `ρ(x)_{uv}` is the `∂_v`-coordinate of
`∂_u x`. A ring map `ONH_{a+b} → Mat_{Shuffle}(B)`. -/
def rho (m m' : ℕ) :
    Presented (m+2+m') →+* Matrix (Shuffle m m') (Shuffle m m') (tensorImage m m') where
  toFun x u v := freeBasis.repr (dshuf u * x) v
  map_one' := by
    ext u v
    rw [mul_one, repr_dshuf, Matrix.one_apply, Finsupp.single_apply]
  map_mul' x y := by
    ext u w
    rw [Matrix.mul_apply, ← mul_assoc]
    conv_lhs => rw [← freeBasis.sum_repr (dshuf u * x), Finset.sum_mul]
    simp only [smul_mul_assoc, map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply,
      Finsupp.smul_apply, smul_eq_mul, freeBasis_apply]
  map_zero' := by
    ext u v
    rw [mul_zero, map_zero]
    rfl
  map_add' x y := by
    ext u v
    rw [mul_add, map_add]
    rfl

theorem rho_apply (x : Presented (m+2+m')) (u v : Shuffle m m') :
    rho m m' x u v = freeBasis.repr (dshuf u * x) v := rfl

/-- `ρ` is graded for the matrix grading with shifts `2ℓ(u)`. -/
theorem rho_mem {d : ℤ} {x : Presented (m+2+m')} (hx : x ∈ onhGrading (m+2+m') d) :
    rho m m' x ∈ matGrading (gradB m m') (fun u => 2 * (length u.1 : ℤ)) d := by
  intro u v
  have h := NilHeckeGrading.degreePiece_mul (NilHeckeGrading.dividedElement_mem u.1) hx
  exact mem_of_deg_eq (coord_mem h v) (by ring)

end OddMath.Frontier.OddBialgebra
