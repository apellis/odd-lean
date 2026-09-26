import OddMath.Frontier.OddBialgebraSmallShuffle
import OddMath.Frontier.OddBialgebraCornerB

/-!
# Restriction along `R₁ ⊗ R₂ ⊂ ONH_{n+2}` for window data

EKL arXiv:1111.1320v1, §6, pp. 46–47. A uniform interface for the inclusions
`ONH_a ⊗ ONH_b ⊂ ONH_{a+b}` which also covers windows of size `1` (`ONH_1 = OPol_1`).

`WinData A₁ A₂ n p` consists of a super pair `ι₁ : R₁ → ONH_{n+2} ← R₂ : ι₂`, homogeneous
`ℤ`-bases `b₁`, `b₂` of even degrees, and an injective map `φ` onto the PBW indices `(A, y)` with
`y` in the Young subgroup `S_p × S_q` (`q = n+2-p`) such that `ι₁(b₁ i) ι₂(b₂ j) = ± x^A ∂_y`.

* `tmap`, `Bsub`: the image `B` of `R₁ ⊗ R₂`, a subring; `gradS`, its grading;
  `pairS : R₁ → B ← R₂`.
* `psi_bijective`: `⊕_u R₁ ⊗ R₂ → ONH_{n+2}`, `(t_u) ↦ ∑ t_u ∂_u` (`u` a shuffle), is bijective;
  `freeBasis : Basis (ShufT n p) B ONH_{n+2}`, `u ↦ ∂_u`.
* `coord_mem`: the `∂_u`-coordinate of an element of degree `e` has degree `e + 2ℓ(u)`.
* `rho : ONH_{n+2} →+* Mat_{Shuffle}(B)`, graded (`rho_mem`); `resIdem`, `res`: restriction
  `K₀(ONH_{n+2}) → K₀(B)`; `res_one`: `Res [ONH_{n+2}] = ∑_u q^{-2ℓ(u)} [B]`.
-/

noncomputable section
open scoped TensorProduct
open LaurentPolynomial

namespace OddMath.Frontier.OddBialgebra
open NilCoxeterWords NilHeckeAction NilHeckeBasis GradedK0 OddCategorification

local notation "L" => LaurentPolynomial ℤ

/-- The shifts `2ℓ(u)` of the free basis `∂_u`. -/
abbrev sShift {n p : ℕ} (u : ShufT n p) : ℤ := 2 * (length u.1 : ℤ)

/-- Window data for `R₁ ⊗ R₂ ⊂ ONH_{n+2}` with blocks `[0, p)`, `[p, n+2)`. -/
structure WinData {R₁ R₂ : Type*} [Ring R₁] [Ring R₂] (A₁ : ℤ → AddSubgroup R₁)
    (A₂ : ℤ → AddSubgroup R₂) (n p : ℕ) where
  /-- The two embeddings. -/
  P : SuperPair A₁ A₂ (onhGrading n)
  /-- Index of the basis of `R₁`. -/
  I₁ : Type
  /-- Index of the basis of `R₂`. -/
  I₂ : Type
  /-- A homogeneous basis of `R₁`. -/
  b₁ : Basis I₁ ℤ R₁
  /-- A homogeneous basis of `R₂`. -/
  b₂ : Basis I₂ ℤ R₂
  /-- Half-degrees of `b₁`. -/
  wt₁ : I₁ → ℤ
  /-- Half-degrees of `b₂`. -/
  wt₂ : I₂ → ℤ
  mem₁ : ∀ i, b₁ i ∈ A₁ (2 * wt₁ i)
  mem₂ : ∀ j, b₂ j ∈ A₂ (2 * wt₂ j)
  /-- The PBW index of `ι₁(b₁ i) ι₂(b₂ j)`. -/
  φ : I₁ × I₂ → (Fin (n+2) → ℕ) × Perm n
  inj : Function.Injective φ
  weight : ∀ ij, NilHeckeGrading.weight (φ ij) = 2 * wt₁ ij.1 + 2 * wt₂ ij.2
  young : ∀ ij, IsYoung p (φ ij).2
  surj : ∀ A y, IsYoung p y → ∃ ij, φ ij = (A, y)
  sign : ∀ i j, Signed (P.ι₁ (b₁ i) * P.ι₂ (b₂ j)) (basis n (φ (i, j)))

namespace WinData

variable {R₁ R₂ : Type*} [Ring R₁] [Ring R₂] {A₁ : ℤ → AddSubgroup R₁}
  {A₂ : ℤ → AddSubgroup R₂} {n p : ℕ} (D : WinData A₁ A₂ n p)

/-- `x ⊗ y ↦ ι₁(x) ι₂(y)`. -/
def tmap : R₁ ⊗[ℤ] R₂ →ₗ[ℤ] Presented n :=
  TensorProduct.lift (LinearMap.mk₂ ℤ (fun x y => D.P.ι₁ x * D.P.ι₂ y)
    (fun x₁ x₂ y => by simp only [map_add, add_mul])
    (fun c x y => by simp only [map_zsmul, smul_mul_assoc])
    (fun x y₁ y₂ => by simp only [map_add, mul_add])
    (fun c x y => by simp only [map_zsmul, mul_smul_comm]))

@[simp] theorem tmap_tmul (x : R₁) (y : R₂) : D.tmap (x ⊗ₜ y) = D.P.ι₁ x * D.P.ι₂ y := rfl

/-- The tensor basis of `R₁ ⊗ R₂`. -/
def bT : Basis (D.I₁ × D.I₂) ℤ (R₁ ⊗[ℤ] R₂) := D.b₁.tensorProduct D.b₂

theorem tmap_bT (ij : D.I₁ × D.I₂) :
    D.tmap (D.bT ij) = D.P.ι₁ (D.b₁ ij.1) * D.P.ι₂ (D.b₂ ij.2) := by
  rw [bT, Basis.tensorProduct_apply, tmap_tmul]

theorem tmap_injective : Function.Injective D.tmap :=
  OnhStructure.injective_of_signed_basis D.bT (basis n) D.tmap D.φ D.inj fun ij => by
    rw [tmap_bT]; exact D.sign ij.1 ij.2

theorem tmap_bT_mul (ij kl : D.I₁ × D.I₂) :
    ∃ t, D.tmap (D.bT ij) * D.tmap (D.bT kl) = D.tmap t := by
  rw [tmap_bT, tmap_bT, mul_assoc, ← mul_assoc (D.P.ι₂ _), D.P.comm (D.mem₁ kl.1) (D.mem₂ ij.2),
    smul_mul_assoc, mul_smul_comm]
  rw [show D.P.ι₁ (D.b₁ ij.1) * (D.P.ι₁ (D.b₁ kl.1) * D.P.ι₂ (D.b₂ ij.2) * D.P.ι₂ (D.b₂ kl.2)) =
    D.P.ι₁ (D.b₁ ij.1 * D.b₁ kl.1) * D.P.ι₂ (D.b₂ ij.2 * D.b₂ kl.2) by
      rw [map_mul, map_mul]; simp only [mul_assoc]]
  exact ⟨((D.wt₁ kl.1 * D.wt₂ ij.2).negOnePow : ℤ) •
    ((D.b₁ ij.1 * D.b₁ kl.1) ⊗ₜ (D.b₂ ij.2 * D.b₂ kl.2)), by
      rw [map_zsmul, tmap_tmul, Units.smul_def]⟩

/-- The image `B` of `R₁ ⊗ R₂` in `ONH_{n+2}`, a subring. -/
def Bsub : Subring (Presented n) where
  carrier := Set.range D.tmap
  one_mem' := ⟨1 ⊗ₜ 1, by rw [tmap_tmul, map_one, map_one, one_mul]⟩
  zero_mem' := ⟨0, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
    exact ⟨s + t, map_add _ _ _⟩
  neg_mem' := by
    rintro _ ⟨s, rfl⟩
    exact ⟨-s, map_neg _ _⟩
  mul_mem' := by
    rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
    let M := LinearMap.range D.tmap
    have hs : s ∈ Submodule.span ℤ (Set.range D.bT) := by rw [D.bT.span_eq]; trivial
    have ht : t ∈ Submodule.span ℤ (Set.range D.bT) := by rw [D.bT.span_eq]; trivial
    show D.tmap s * D.tmap t ∈ M
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨ij, rfl⟩ := hx
      induction ht using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨kl, rfl⟩ := hy
        obtain ⟨u, hu⟩ := D.tmap_bT_mul ij kl
        exact ⟨u, hu.symm⟩
      | zero => rw [map_zero, mul_zero]; exact M.zero_mem
      | add y y' _ _ h h' => rw [map_add, mul_add]; exact M.add_mem h h'
      | smul c y _ h => rw [map_smul, mul_smul_comm]; exact M.smul_mem c h
    | zero => rw [map_zero, zero_mul]; exact M.zero_mem
    | add x x' _ _ h h' => rw [map_add, add_mul]; exact M.add_mem h h'
    | smul c x _ h => rw [map_smul, smul_mul_assoc]; exact M.smul_mem c h

theorem mem_Bsub {z : Presented n} : z ∈ D.Bsub ↔ ∃ t, D.tmap t = z := Iff.rfl

/-- The grading of `B`, restricted from `ONH_{n+2}`. -/
def gradS (d : ℤ) : AddSubgroup D.Bsub := (onhGrading n d).comap D.Bsub.subtype.toAddMonoidHom

instance gradS.gradedMonoid : SetLike.GradedMonoid D.gradS where
  one_mem := NilHeckeGrading.unit_mem
  mul_mem _ _ _ _ hx hy := NilHeckeGrading.degreePiece_mul hx hy

theorem ι₁_mem (x : R₁) : D.P.ι₁ x ∈ D.Bsub := ⟨x ⊗ₜ 1, by rw [tmap_tmul, map_one, mul_one]⟩

theorem ι₂_mem (y : R₂) : D.P.ι₂ y ∈ D.Bsub := ⟨1 ⊗ₜ y, by rw [tmap_tmul, map_one, one_mul]⟩

/-- `R₁ → B ← R₂`, as a super pair. -/
def pairS : SuperPair A₁ A₂ D.gradS where
  ι₁ := D.P.ι₁.codRestrict D.Bsub D.ι₁_mem
  ι₂ := D.P.ι₂.codRestrict D.Bsub D.ι₂_mem
  map₁ hx := D.P.map₁ hx
  map₂ hy := D.P.map₂ hy
  even₁ := D.P.even₁
  even₂ := D.P.even₂
  comm hx hy := Subtype.ext <| by
    have := D.P.comm hx hy
    rw [Units.smul_def] at this ⊢
    exact this

@[simp] theorem pairS_ι₁ (x : R₁) : ((D.pairS.ι₁ x : D.Bsub) : Presented n) = D.P.ι₁ x := rfl

@[simp] theorem pairS_ι₂ (y : R₂) : ((D.pairS.ι₂ y : D.Bsub) : Presented n) = D.P.ι₂ y := rfl

/-! ### Freeness over `B` -/

/-- `∂_u`. -/
def dsh (u : ShufT n p) : Presented n := dividedElement u.1

/-- `(t_u) ↦ ∑_u tmap(t_u) ∂_u`. -/
def psi : (ShufT n p →₀ R₁ ⊗[ℤ] R₂) →ₗ[ℤ] Presented n :=
  Finsupp.lsum ℤ fun u => (LinearMap.mulRight ℤ (dsh u)) ∘ₗ D.tmap

theorem psi_single (u : ShufT n p) (t : R₁ ⊗[ℤ] R₂) :
    D.psi (Finsupp.single u t) = D.tmap t * dsh u := by
  simp [psi]

/-- The `ℤ`-basis of `⊕_u R₁ ⊗ R₂`. -/
def tsBasis : Basis (Σ _ : ShufT n p, D.I₁ × D.I₂) ℤ (ShufT n p →₀ R₁ ⊗[ℤ] R₂) :=
  Finsupp.basis fun _ => D.bT

/-- The PBW index `(A, y u)` of `x^A ∂_y ∂_u`. -/
def sIdx (x : Σ _ : ShufT n p, D.I₁ × D.I₂) : (Fin (n+2) → ℕ) × Perm n :=
  ((D.φ x.2).1, (D.φ x.2).2 * x.1.1)

theorem sIdx_bijective : Function.Bijective D.sIdx := by
  refine ⟨fun x y h => ?_, fun w => ?_⟩
  · obtain ⟨u, ij⟩ := x
    obtain ⟨u', kl⟩ := y
    simp only [sIdx, Prod.mk.injEq] at h
    obtain ⟨hA, hw⟩ := h
    obtain ⟨hy, hu⟩ := young_factor_unique (D.young ij) (D.young kl) u.2 u'.2 hw
    obtain rfl : u = u' := Subtype.ext hu
    obtain rfl : ij = kl := D.inj (Prod.ext hA hy)
    rfl
  · obtain ⟨A, w⟩ := w
    obtain ⟨y, u, hy, hu, rfl⟩ := exists_young_factor (p := p) w
    obtain ⟨ij, hij⟩ := D.surj A y hy
    exact ⟨⟨⟨u, hu⟩, ij⟩, by simp [sIdx, hij]⟩

theorem psi_basis (x : Σ _ : ShufT n p, D.I₁ × D.I₂) :
    Signed (D.psi (D.tsBasis x)) (basis n (D.sIdx x)) := by
  obtain ⟨u, ij⟩ := x
  rw [tsBasis, Finsupp.coe_basis, psi_single, tmap_bT]
  refine ((D.sign ij.1 ij.2).mul (Signed.refl (dsh u))).trans ?_
  rw [basis_apply, basis_apply, basisElement, basisElement, mul_assoc]
  exact (Signed.refl _).mul (dividedElement_mul_additive _ _ (length_young_mul (D.young ij) u.2))

theorem psi_bijective : Function.Bijective D.psi :=
  ⟨OnhStructure.injective_of_signed_basis D.tsBasis (basis n) D.psi D.sIdx
      D.sIdx_bijective.1 D.psi_basis,
    surjective_of_signed_basis D.tsBasis (basis n) D.psi D.sIdx D.sIdx_bijective.2 D.psi_basis⟩

/-- `t ↦ tmap t ∈ B`. -/
def toB : R₁ ⊗[ℤ] R₂ →+ D.Bsub where
  toFun t := ⟨D.tmap t, t, rfl⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-- A preimage in `R₁ ⊗ R₂` of an element of `B`. -/
def ofB : D.Bsub →+ R₁ ⊗[ℤ] R₂ :=
  ((LinearEquiv.ofInjective D.tmap D.tmap_injective).symm.toLinearMap.toAddMonoidHom).comp
    { toFun := fun b => ⟨b, LinearMap.mem_range.2 b.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

theorem toB_ofB (b : D.Bsub) : D.toB (D.ofB b) = b := by
  refine Subtype.ext ?_
  show D.tmap ((LinearEquiv.ofInjective D.tmap D.tmap_injective).symm _) = _
  have := (LinearEquiv.ofInjective D.tmap D.tmap_injective).apply_symm_apply
    ⟨b, LinearMap.mem_range.2 b.2⟩
  exact congrArg Subtype.val this

/-- `(b_u) ↦ ∑_u b_u ∂_u`. -/
def lcomb : (ShufT n p →₀ D.Bsub) →ₗ[D.Bsub] Presented n :=
  Finsupp.linearCombination _ dsh

theorem lcomb_single (u : ShufT n p) (b : D.Bsub) :
    D.lcomb (Finsupp.single u b) = (b : Presented n) * dsh u := by
  simp [lcomb, Finsupp.linearCombination_single]
  rfl

theorem lcomb_mapRange (f : ShufT n p →₀ R₁ ⊗[ℤ] R₂) :
    D.lcomb (Finsupp.mapRange.addMonoidHom D.toB f) = D.psi f := by
  have h : D.lcomb.toAddMonoidHom.comp (Finsupp.mapRange.addMonoidHom D.toB) =
      D.psi.toAddMonoidHom := Finsupp.addHom_ext fun u t => by
    simp only [AddMonoidHom.comp_apply, Finsupp.mapRange.addMonoidHom_apply,
      Finsupp.mapRange_single, LinearMap.toAddMonoidHom_coe, lcomb_single, psi_single]
    rfl
  exact DFunLike.congr_fun h f

theorem lcomb_bijective : Function.Bijective D.lcomb := by
  have hid : (Finsupp.mapRange.addMonoidHom D.toB).comp (Finsupp.mapRange.addMonoidHom D.ofB) =
      AddMonoidHom.id (ShufT n p →₀ D.Bsub) := by
    rw [← Finsupp.mapRange.addMonoidHom_comp]
    have : D.toB.comp D.ofB = AddMonoidHom.id D.Bsub := AddMonoidHom.ext D.toB_ofB
    rw [this, Finsupp.mapRange.addMonoidHom_id]
  have hl : ∀ l, l = Finsupp.mapRange.addMonoidHom D.toB
      (Finsupp.mapRange.addMonoidHom D.ofB l) := fun l => (DFunLike.congr_fun hid l).symm
  refine ⟨fun l l' h => ?_, fun x => ?_⟩
  · rw [hl l, hl l', lcomb_mapRange, lcomb_mapRange] at h
    rw [hl l, hl l', D.psi_bijective.1 h]
  · obtain ⟨f, rfl⟩ := D.psi_bijective.2 x
    exact ⟨_, D.lcomb_mapRange f⟩

/-- **`ONH_{n+2}` is a free left `B`-module** with basis the `∂_u`, `u` a shuffle. -/
def freeBasis : Basis (ShufT n p) D.Bsub (Presented n) :=
  Basis.ofRepr (LinearEquiv.ofBijective D.lcomb D.lcomb_bijective).symm

theorem freeBasis_apply (u : ShufT n p) : D.freeBasis u = dsh u := by
  have h := D.freeBasis.repr_symm_single u 1
  rw [one_smul] at h
  rw [← h]
  show D.lcomb (Finsupp.single u 1) = _
  rw [lcomb_single, OneMemClass.coe_one, one_mul]

theorem freeBasis_repr_symm (l : ShufT n p →₀ D.Bsub) : D.freeBasis.repr.symm l = D.lcomb l :=
  rfl

/-! ### Graded coordinates -/

theorem tmap_bT_mem (ij : D.I₁ × D.I₂) :
    D.tmap (D.bT ij) ∈ onhGrading n (NilHeckeGrading.weight (D.φ ij)) := by
  rw [tmap_bT]
  rcases D.sign ij.1 ij.2 with h | h <;> rw [h, basis_apply]
  · exact NilHeckeGrading.basisElement_mem _
  · exact neg_mem (NilHeckeGrading.basisElement_mem _)

theorem weight_sIdx (x : Σ _ : ShufT n p, D.I₁ × D.I₂) :
    NilHeckeGrading.weight (D.sIdx x) =
      NilHeckeGrading.weight (D.φ x.2) - 2 * (length x.1.1 : ℤ) := by
  simp only [NilHeckeGrading.weight, sIdx, length_young_mul (D.young x.2) x.1.2]
  push_cast
  ring

theorem repr_psi_basis (x : Σ _ : ShufT n p, D.I₁ × D.I₂) :
    D.freeBasis.repr (D.psi (D.tsBasis x)) = Finsupp.single x.1 (D.toB (D.bT x.2)) := by
  rw [← lcomb_mapRange, ← freeBasis_repr_symm, LinearEquiv.apply_symm_apply, tsBasis,
    Finsupp.coe_basis, Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_single]

/-- **The coordinates are graded**: for `x` of degree `e`, its `∂_u`-coordinate has degree
`e + 2ℓ(u)`. -/
theorem coord_mem {e : ℤ} {x : Presented n} (hx : x ∈ onhGrading n e) (u : ShufT n p) :
    D.freeBasis.repr x u ∈ D.gradS (e + 2 * (length u.1 : ℤ)) := by
  have hx' : x ∈ NilHeckeGrading.leftPiece n e := by
    rw [← NilHeckeGrading.degreePiece_eq_leftPiece]; exact hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨i, hi⟩, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := D.sIdx_bijective.2 i
    obtain ⟨u', ij⟩ := y
    have hs := (D.psi_basis ⟨u', ij⟩).symm
    show D.freeBasis.repr (basisElement (D.sIdx ⟨u', ij⟩)) u ∈ _
    rw [← basis_apply]
    have hmem : D.toB (D.bT ij) ∈ D.gradS (e + 2 * (length u'.1 : ℤ)) :=
      mem_of_deg_eq (D.tmap_bT_mem ij) (by rw [← hi, weight_sIdx]; ring)
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
    rw [← Int.cast_smul_eq_zsmul D.Bsub, map_smul, Finsupp.smul_apply, smul_eq_mul,
      ← zsmul_eq_mul]
    exact zsmul_mem hx c

/-! ### Restriction -/

theorem repr_dsh (u : ShufT n p) : D.freeBasis.repr (dsh u) = Finsupp.single u 1 := by
  rw [← D.freeBasis_apply, Basis.repr_self]

/-- Right multiplication on `ONH_{n+2} = ⊕_u B ∂_u`: `ρ(x)_{uv}` is the `∂_v`-coordinate of
`∂_u x`. -/
def rho : Presented n →+* Matrix (ShufT n p) (ShufT n p) D.Bsub where
  toFun x u v := D.freeBasis.repr (dsh u * x) v
  map_one' := by
    ext u v
    rw [mul_one, repr_dsh, Matrix.one_apply, Finsupp.single_apply]
  map_mul' x y := by
    ext u w
    rw [Matrix.mul_apply, ← mul_assoc]
    conv_lhs => rw [← D.freeBasis.sum_repr (dsh u * x), Finset.sum_mul]
    simp only [smul_mul_assoc, map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply,
      Finsupp.smul_apply, smul_eq_mul, D.freeBasis_apply]
  map_zero' := by
    ext u v
    rw [mul_zero, map_zero]
    rfl
  map_add' x y := by
    ext u v
    rw [mul_add, map_add]
    rfl

theorem rho_mem {d : ℤ} {x : Presented n} (hx : x ∈ onhGrading n d) :
    D.rho x ∈ matGrading D.gradS sShift d := by
  intro u v
  have h := NilHeckeGrading.degreePiece_mul (NilHeckeGrading.dividedElement_mem u.1) hx
  exact mem_of_deg_eq (D.coord_mem h v) (by ring)

/-- Restriction of graded idempotents `ONH_{n+2} → B`. -/
def resIdem (P : GIdem (onhGrading n)) : GIdem D.gradS :=
  (GIdem.mapHom (B := matGrading D.gradS sShift) D.rho D.rho_mem P).flatten

set_option maxHeartbeats 1000000 in
/-- **Restriction** `K₀(ONH_{n+2}) → K₀(B)`. -/
def res : K0 (onhGrading n) →ₗ[L] K0 D.gradS :=
  (K0.morita (A := D.gradS) (d := sShift)).toLinearMap ∘ₗ
    k0Map (B := matGrading D.gradS sShift) D.rho D.rho_mem

theorem res_of (P : GIdem (onhGrading n)) : D.res (K0.of P) = K0.of (D.resIdem P) := by
  rw [res, LinearMap.comp_apply, k0Map_of, LinearEquiv.coe_coe, K0.morita_of]
  rfl

/-- `Res [ONH_{n+2}] = ∑_u q^{-2ℓ(u)} [B]`. -/
theorem res_one : D.res (K0.of (GIdem.single 0)) =
    ∑ u : ShufT n p, (T (-(2 * (length u.1 : ℤ))) : L) •
      K0.of (GIdem.single 0 : GIdem D.gradS) := by
  rw [res_of]
  set Q := GIdem.mapHom (B := matGrading D.gradS sShift) D.rho D.rho_mem
    (GIdem.single 0 : GIdem (onhGrading n))
  have hQ : Q.e = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h1 : flat Q.e = 1 := by
    rw [hQ]
    exact (Matrix.compRingEquiv (Fin 1) (ShufT n p) D.Bsub).map_one
  let σ := Fintype.equivFin (Fin Q.n × ShufT n p)
  let t : Fin (Fintype.card (Fin Q.n × ShufT n p)) → ℤ :=
    fun i => Q.s (σ.symm i).1 - sShift (σ.symm i).2
  have h2 : MvN D.gradS (fun x : Fin Q.n × ShufT n p => Q.s x.1 - sShift x.2)
      (flat Q.e) (GIdem.free (A := D.gradS) t).s (GIdem.free (A := D.gradS) t).e := by
    rw [h1]
    refine MvN.of_equiv σ (IsHom.one (A := D.gradS)) (mul_one 1)
      (fun x => by simp [t, GIdem.free]) ?_
    intro x y
    simp only [GIdem.free, Matrix.one_apply, σ.injective.eq_iff]
  have h3 : D.resIdem (GIdem.single 0) ≈ GIdem.free (A := D.gradS) t :=
    MvN.trans (D.resIdem _).idem (GIdem.flat_idem Q) (GIdem.free t).idem
      (GIdem.mvn_flatten Q).symm h2
  rw [K0.of_eq h3, K0.of_free,
    ← Equiv.sum_comp σ (fun a => K0.of (GIdem.single (A := D.gradS) (t a))),
    Fintype.sum_prod_type]
  simp only [t, Equiv.symm_apply_apply]
  change ∑ _x : Fin 1, ∑ u : ShufT n p,
    K0.of (GIdem.single (A := D.gradS) (0 - sShift u)) = _
  rw [Fin.sum_univ_one]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [K0.T_smul_single, zero_sub]

end WinData

end OddMath.Frontier.OddBialgebra
