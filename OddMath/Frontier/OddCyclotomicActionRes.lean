import OddMath.Frontier.OddBialgebraAction

/-!
# Restriction along a relatively free extension

Auxiliary results on graded `K₀` (`GradedK0`) for the action of `F` on `K₀(ONH^N)`, EKL
arXiv:1111.1320v1, §6, last paragraph (p. 47).

Let `φ : R → S` be a graded ring map and `E ∈ R` a degree-zero idempotent. A *relative basis*
(`RelBasis`) is a family `vᵢ ∈ S`, `i ∈ ι` finite, with `φ(E) vᵢ = vᵢ`, such that every `y ∈ S` is
uniquely `y = ∑ᵢ φ(cᵢ) vᵢ` with `cᵢ ∈ RE`. Then `S ≅ ⊕ᵢ RE · vᵢ` as a left `R`-module: the
restriction of `S` to `R` is the graded projective `⊕ᵢ RE{sᵢ}` when `vᵢ` is homogeneous of
degree `sᵢ` (for `E = 1` this is a graded basis of `S` over `R`).

* `RelBasis.rho`: right multiplication on `⊕ᵢ RE vᵢ`, `ρ(y)ᵢⱼ = cⱼ(vᵢ y)`, a non-unital ring map
  `S → Mat_ι(R)` with `ρ(1) = diag(E)`; graded for the shifts `-sᵢ` (`RelBasis.rho_mem`) when the
  gradings of `R` and `S` are direct sum decompositions (`RelBasis.coeff_mem`).
* `k0MapNU`: `K₀` of a graded non-unital ring map, `(n, s, e) ↦ (n, s, ρ(e))`.
* `RelBasis.res`: restriction `K₀(S) → K₀(R)`, `[P] ↦ [ρ(P)]` followed by graded Morita
  invariance; `[S{k}] ↦ ∑ᵢ [RE{k + sᵢ}]` (`RelBasis.res_single`).
-/

noncomputable section
open LaurentPolynomial Matrix

namespace OddMath.Frontier.OddCyclotomicAction
open GradedK0 OddCategorification Cyclotomic

local notation "L" => LaurentPolynomial ℤ

/-! ### `K₀` of a non-unital graded ring map -/

section NonUnital

variable {S T : Type*} [Ring S] [Ring T] {B : ℤ → AddSubgroup S} {C : ℤ → AddSubgroup T}
  [SetLike.GradedMonoid B] [SetLike.GradedMonoid C] (ρ : S →ₙ+* T)
  (hρ : ∀ {d : ℤ} {x : S}, x ∈ B d → ρ x ∈ C d)

omit [SetLike.GradedMonoid B] [SetLike.GradedMonoid C] in
theorem map_mul_nu {ι κ μ : Type*} [Fintype κ] (u : Matrix ι κ S) (v : Matrix κ μ S) :
    (u * v).map ρ = u.map ρ * v.map ρ := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul]

omit [SetLike.GradedMonoid B] [SetLike.GradedMonoid C] in
include hρ in
theorem isHom_mapNU {ι κ : Type*} {s : ι → ℤ} {t : κ → ℤ} {u : Matrix ι κ S}
    (hu : IsHom B s t u) : IsHom C s t (u.map ρ) := fun i j => hρ (hu i j)

omit [SetLike.GradedMonoid B] [SetLike.GradedMonoid C] in
include hρ in
theorem mvn_mapNU {ι κ : Type*} [Fintype ι] [Fintype κ] {s : ι → ℤ} {e : Matrix ι ι S}
    {t : κ → ℤ} {f : Matrix κ κ S} (h : MvN B s e t f) : MvN C s (e.map ρ) t (f.map ρ) := by
  obtain ⟨u, v, hu, hv, h1, h2, h3, h4⟩ := h
  exact ⟨u.map ρ, v.map ρ, isHom_mapNU ρ hρ hu, isHom_mapNU ρ hρ hv,
    by rw [← map_mul_nu, h1], by rw [← map_mul_nu, h2],
    by rw [← map_mul_nu, ← map_mul_nu, h3], by rw [← map_mul_nu, ← map_mul_nu, h4]⟩

/-- `(n, s, e) ↦ (n, s, ρ(e))` for a graded non-unital ring map `ρ`. -/
def GIdem.mapNU (P : GIdem B) : GIdem C where
  n := P.n
  s := P.s
  e := P.e.map ρ
  hom := isHom_mapNU ρ hρ P.hom
  idem := by rw [← map_mul_nu, P.idem]

omit [SetLike.GradedMonoid B] in
theorem GIdem.mapNU_sum (P Q : GIdem B) :
    GIdem.mapNU ρ hρ (P.sum Q) ≈ (GIdem.mapNU ρ hρ P).sum (GIdem.mapNU ρ hρ Q) := by
  refine MvN.of_equiv (Equiv.refl _) (GIdem.mapNU ρ hρ (P.sum Q)).hom
    (GIdem.mapNU ρ hρ (P.sum Q)).idem (fun i => ?_) (fun i j => ?_)
  · rfl
  · show fromBlocks (P.e.map ρ) 0 0 (Q.e.map ρ) (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) =
      ρ (fromBlocks P.e 0 0 Q.e (finSumFinEquiv.symm i) (finSumFinEquiv.symm j))
    generalize finSumFinEquiv.symm i = x
    generalize finSumFinEquiv.symm j = y
    cases x <;> cases y <;> simp

/-- `(n, s, e) ↦ (n, s, ρ(e))` on isomorphism classes. -/
def gprojMapNU : GProj B →+ GProj C where
  toFun := Quotient.map (GIdem.mapNU ρ hρ) fun _ _ h => mvn_mapNU ρ hρ h
  map_zero' := GProj.mk_eq_mk.2 (MvN.of_equiv (Equiv.refl _)
    (GIdem.mapNU ρ hρ GIdem.zero).hom (GIdem.mapNU ρ hρ GIdem.zero).idem
    (fun i => i.elim0) (fun i => i.elim0))
  map_add' := by
    refine GProj.ind fun P => GProj.ind fun Q => ?_
    exact GProj.mk_eq_mk.2 (GIdem.mapNU_sum ρ hρ P Q)

/-- `K₀` of a graded non-unital ring map, `ℤ[q,q⁻¹]`-linear. -/
def k0MapNU : K0 B →ₗ[L] K0 C :=
  let F : K0 B →+ K0 C := GrothendieckGroup.map (gprojMapNU ρ hρ)
  { F with
    map_smul' := K0.map_smul_of_shift F fun k x => by
      rw [K0.T_smul]
      have : F.comp (K0.shift k) = (K0.shift k).comp F := K0.hom_ext fun P => by
        rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, K0.shift_of,
          show F (K0.of (P.shift k)) = K0.of (GIdem.mapNU ρ hρ (P.shift k)) from
            GrothendieckGroup.map_of _ _,
          show F (K0.of P) = K0.of (GIdem.mapNU ρ hρ P) from GrothendieckGroup.map_of _ _,
          K0.shift_of]
        rfl
      exact DFunLike.congr_fun this x }

theorem k0MapNU_of (P : GIdem B) : k0MapNU ρ hρ (K0.of P) = K0.of (GIdem.mapNU ρ hρ P) :=
  GrothendieckGroup.map_of _ _

end NonUnital

/-! ### Relative bases -/

section RelBasis

variable {R S : Type*} [Ring R] [Ring S]

/-- A relative basis of `S` over `R` along `φ`, relative to the idempotent `E`: every `y ∈ S` is
uniquely `∑ᵢ φ(cᵢ) vᵢ` with `cᵢ E = cᵢ`. -/
structure RelBasis (φ : R →+* S) (E : R) (ι : Type*) [Fintype ι] where
  /-- The basis vectors. -/
  vec : ι → S
  idem : E * E = E
  E_vec : ∀ i, φ E * vec i = vec i
  existsUnique : ∀ y : S, ∃! c : ι → R, (∀ i, c i * E = c i) ∧ ∑ i, φ (c i) * vec i = y

namespace RelBasis

variable {φ : R →+* S} {E : R} {ι : Type*} [Fintype ι] (b : RelBasis φ E ι)

/-- The coordinates of `y`. -/
def coeff (y : S) : ι → R := (b.existsUnique y).exists.choose

theorem coeff_mul_E (y : S) (i : ι) : b.coeff y i * E = b.coeff y i :=
  (b.existsUnique y).exists.choose_spec.1 i

theorem sum_coeff (y : S) : ∑ i, φ (b.coeff y i) * b.vec i = y :=
  (b.existsUnique y).exists.choose_spec.2

theorem coeff_eq {c : ι → R} (hc : ∀ i, c i * E = c i) {y : S}
    (h : ∑ i, φ (c i) * b.vec i = y) : b.coeff y = c :=
  (b.existsUnique y).unique ⟨b.coeff_mul_E y, b.sum_coeff y⟩ ⟨hc, h⟩

theorem coeff_zero : b.coeff 0 = 0 :=
  b.coeff_eq (fun _ => zero_mul E) (by simp)

theorem coeff_add (y z : S) : b.coeff (y + z) = b.coeff y + b.coeff z :=
  b.coeff_eq (fun i => by rw [Pi.add_apply, add_mul, b.coeff_mul_E, b.coeff_mul_E])
    (by simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib, b.sum_coeff])

theorem coeff_mul_left (r : R) (y : S) : b.coeff (φ r * y) = fun i => r * b.coeff y i :=
  b.coeff_eq (fun i => by rw [mul_assoc, b.coeff_mul_E])
    (by simp only [map_mul, mul_assoc, ← Finset.mul_sum, b.sum_coeff])

theorem coeff_vec [DecidableEq ι] (i : ι) : b.coeff (b.vec i) = Pi.single i E :=
  b.coeff_eq (fun j => by
      rcases eq_or_ne j i with rfl | h
      · rw [Pi.single_eq_same, b.idem]
      · rw [Pi.single_eq_of_ne h, zero_mul])
    (by
      rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, map_zero, zero_mul])
        (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, b.E_vec])

/-- Right multiplication on `⊕ᵢ RE vᵢ`: `ρ(y)ᵢⱼ = cⱼ(vᵢ y)`. -/
def rho : S →ₙ+* Matrix ι ι R where
  toFun y i j := b.coeff (b.vec i * y) j
  map_mul' y z := by
    ext i k
    rw [Matrix.mul_apply]
    have h := b.coeff_eq (c := fun k => ∑ j, b.coeff (b.vec i * y) j * b.coeff (b.vec j * z) k)
      (y := b.vec i * (y * z)) (fun k => by rw [Finset.sum_mul]; simp only [mul_assoc,
        b.coeff_mul_E]) (by
        calc ∑ k, φ (∑ j, b.coeff (b.vec i * y) j * b.coeff (b.vec j * z) k) * b.vec k
            = ∑ j, φ (b.coeff (b.vec i * y) j) *
                ∑ k, φ (b.coeff (b.vec j * z) k) * b.vec k := by
              simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
              exact Finset.sum_comm
          _ = ∑ j, φ (b.coeff (b.vec i * y) j) * (b.vec j * z) := by
              simp only [b.sum_coeff]
          _ = b.vec i * (y * z) := by
              simp only [← mul_assoc, ← Finset.sum_mul, b.sum_coeff])
    exact congrFun h k
  map_zero' := by
    ext i j
    rw [mul_zero, b.coeff_zero]
    rfl
  map_add' y z := by
    ext i j
    rw [mul_add, b.coeff_add]
    rfl

theorem rho_apply (y : S) (i j : ι) : b.rho y i j = b.coeff (b.vec i * y) j := rfl

theorem rho_one [DecidableEq ι] : b.rho 1 = diagonal fun _ => E := by
  ext i j
  rw [rho_apply, mul_one, b.coeff_vec, diagonal_apply]
  rcases eq_or_ne i j with rfl | h
  · rw [Pi.single_eq_same, if_pos rfl]
  · rw [Pi.single_eq_of_ne (Ne.symm h), if_neg h]

/-! #### Gradings -/

variable {A : ℤ → AddSubgroup R} {B : ℤ → AddSubgroup S} [SetLike.GradedMonoid A]
  [SetLike.GradedMonoid B]

omit [SetLike.GradedMonoid A] in
/-- The degree-`e` component of `φ(r) v` is `φ(r_{e - s}) v` for `v` of degree `s`. -/
theorem dec_map_mul (hA : UniqueDecomposition A) (hB : UniqueDecomposition B)
    (hφ : ∀ {d : ℤ} {x : R}, x ∈ A d → φ x ∈ B d) {v : S} {s : ℤ} (hv : v ∈ B s) (r : R)
    (t : ℤ) : hB.dec (φ r * v) t = φ (hA.dec r (t - s)) * v := by
  let g : ℤ →₀ S := Finsupp.embDomain (addRightEmbedding s)
    ((hA.dec r).mapRange (fun x => φ x * v) (by simp))
  have hg : ∀ t, g t = φ (hA.dec r (t - s)) * v := fun t => by
    have ht : t = addRightEmbedding s (t - s) := by simp
    rw [ht, Finsupp.embDomain_apply, Finsupp.mapRange_apply]
    simp
  have hdec : hB.dec (φ r * v) = g := by
    refine hB.dec_eq (fun t => ?_) ?_
    · rw [hg]
      exact mem_of_deg_eq (SetLike.GradedMul.mul_mem (hφ (hA.dec_mem r (t - s))) hv) (by ring)
    · rw [Finsupp.sum_embDomain, Finsupp.sum_mapRange_index (fun _ => rfl)]
      conv_rhs => rw [← hA.dec_sum r]
      rw [Finsupp.sum, Finsupp.sum, map_sum, Finset.sum_mul]
  rw [hdec, hg]

/-- **The coordinates are graded**: for `y` of degree `d` and `vᵢ` of degree `sᵢ`, the coordinate
`cᵢ(y)` has degree `d - sᵢ`. -/
theorem coeff_mem (hA : UniqueDecomposition A) (hB : UniqueDecomposition B)
    (hφ : ∀ {d : ℤ} {x : R}, x ∈ A d → φ x ∈ B d) (hE : E ∈ A 0) (s : ι → ℤ)
    (hvec : ∀ i, b.vec i ∈ B (s i)) {d : ℤ} {y : S} (hy : y ∈ B d) (i : ι) :
    b.coeff y i ∈ A (d - s i) := by
  set c := b.coeff y
  -- components of the coordinates are again in `RE`
  have hcE : ∀ j e, hA.dec (c j) e * E = hA.dec (c j) e := by
    intro j e
    have h1 : hA.dec (c j * E) = (hA.dec (c j)).mapRange (· * E) (zero_mul E) := by
      refine hA.dec_eq (fun t => ?_) ?_
      · rw [Finsupp.mapRange_apply]
        exact mem_of_deg_eq (SetLike.GradedMul.mul_mem (hA.dec_mem (c j) t) hE) (by ring)
      · rw [Finsupp.sum_mapRange_index (fun _ => rfl)]
        conv_rhs => rw [← hA.dec_sum (c j)]
        rw [Finsupp.sum, Finsupp.sum, Finset.sum_mul]
    rw [show c j * E = c j from b.coeff_mul_E y j] at h1
    have h2 := congrArg (fun f : ℤ →₀ R => f e) h1
    simp only [Finsupp.mapRange_apply] at h2
    exact h2.symm
  -- the degree-`t` component of `y`
  have hcomp : ∀ t, hB.dec y t = ∑ j, φ (hA.dec (c j) (t - s j)) * b.vec j := by
    intro t
    conv_lhs => rw [← b.sum_coeff y]
    rw [show hB.dec (∑ j, φ (c j) * b.vec j) = ∑ j, hB.dec (φ (c j) * b.vec j) from
      map_sum hB.decHom _ _, Finsupp.finset_sum_apply]
    exact Finset.sum_congr rfl fun j _ => dec_map_mul hA hB hφ (hvec j) (c j) t
  -- off degree `d`, all components vanish
  have hzero : ∀ e, e ≠ d - s i → hA.dec (c i) e = 0 := by
    intro e he
    have ht : hB.dec y (e + s i) = 0 := by
      rw [hB.dec_of_mem hy, Finsupp.single_eq_of_ne (by omega)]
    rw [hcomp] at ht
    have h0 := b.coeff_eq (c := fun j => hA.dec (c j) (e + s i - s j)) (fun j => hcE j _) ht
    have := congrFun h0 i
    rw [b.coeff_zero, Pi.zero_apply, show e + s i - s i = e by ring] at this
    exact this.symm
  have hsum := hA.dec_sum (c i)
  rw [Finsupp.sum, Finset.sum_eq_single (d - s i) (fun e _ he => hzero e he)
    (fun h => Finsupp.not_mem_support_iff.1 h)] at hsum
  rw [← hsum]
  exact hA.dec_mem _ _

/-- `ρ` is graded for the matrix grading with shifts `-sᵢ`. -/
theorem rho_mem [DecidableEq ι] (hA : UniqueDecomposition A) (hB : UniqueDecomposition B)
    (hφ : ∀ {d : ℤ} {x : R}, x ∈ A d → φ x ∈ B d) (hE : E ∈ A 0) (s : ι → ℤ)
    (hvec : ∀ i, b.vec i ∈ B (s i)) {d : ℤ} {y : S} (hy : y ∈ B d) :
    b.rho y ∈ matGrading A (fun i => -s i) d := fun i j =>
  mem_of_deg_eq (b.coeff_mem hA hB hφ hE s hvec (SetLike.GradedMul.mul_mem (hvec i) hy) j)
    (by ring)

/-- **Restriction** `K₀(S) → K₀(R)` along a relative basis: `[P] ↦ [ρ(P)]`, followed by graded
Morita invariance `K₀(Mat_ι(R)) ≅ K₀(R)`. -/
def res [DecidableEq ι] [Nonempty ι] (hA : UniqueDecomposition A) (hB : UniqueDecomposition B)
    (hφ : ∀ {d : ℤ} {x : R}, x ∈ A d → φ x ∈ B d) (hE : E ∈ A 0) (s : ι → ℤ)
    (hvec : ∀ i, b.vec i ∈ B (s i)) : K0 B →ₗ[L] K0 A :=
  (K0.morita (d := fun i => -s i)).toLinearMap.comp
    (k0MapNU b.rho (b.rho_mem hA hB hφ hE s hvec))

/-- `[S{k}] ↦ ∑ᵢ [RE{k + sᵢ}]`. -/
theorem res_single [DecidableEq ι] [Nonempty ι] (hA : UniqueDecomposition A)
    (hB : UniqueDecomposition B) (hφ : ∀ {d : ℤ} {x : R}, x ∈ A d → φ x ∈ B d) (hE : E ∈ A 0)
    (s : ι → ℤ)
    (hvec : ∀ i, b.vec i ∈ B (s i)) (k : ℤ) :
    b.res hA hB hφ hE s hvec (K0.of (GIdem.single k : GIdem B)) =
      ∑ i, (T (k + s i) : L) • K0.of (gelem hE b.idem 0) := by
  rw [res, LinearMap.comp_apply, k0MapNU_of, LinearEquiv.coe_coe, K0.morita_of]
  let σ := Fintype.equivFin (Fin 1 × ι)
  set P := GIdem.mapNU b.rho (b.rho_mem hA hB hφ hE s hvec) (GIdem.single k : GIdem B)
  have hPe : ∀ x y : Fin P.n × ι, flat P.e x y = if x.2 = y.2 then E else 0 := by
    rintro ⟨⟨a, ha⟩, i⟩ ⟨⟨a', ha'⟩, j⟩
    change a < 1 at ha
    change a' < 1 at ha'
    obtain rfl : a = 0 := by omega
    obtain rfl : a' = 0 := by omega
    show b.rho ((1 : Matrix (Fin 1) (Fin 1) S) 0 0) i j = _
    rw [Matrix.one_apply_eq, b.rho_one, diagonal_apply]
  have h1 : P.flatten ≈ gdiag hE b.idem fun m => k + s (σ.symm m).2 := by
    refine MvN.trans P.flatten.idem (GIdem.flat_idem P) (gdiag hE b.idem _).idem
      (GIdem.mvn_flatten P).symm ?_
    refine MvN.of_equiv σ (isHom_flat_iff.1 P.hom) (GIdem.flat_idem P) (fun x => ?_)
      (fun x y => ?_)
    · show k + s (σ.symm (σ x)).2 = k - -s x.2
      rw [Equiv.symm_apply_apply]; ring
    · show (diagonal fun _ => E) (σ x) (σ y) = flat P.e x y
      rw [hPe, diagonal_apply]
      obtain ⟨⟨a, ha⟩, i⟩ := x
      obtain ⟨⟨a', ha'⟩, j⟩ := y
      change a < 1 at ha
      change a' < 1 at ha'
      obtain rfl : a = 0 := by omega
      obtain rfl : a' = 0 := by omega
      by_cases h : i = j
      · subst h; simp
      · rw [if_neg h, if_neg]
        intro e
        exact h (congrArg Prod.snd (σ.injective e))
  rw [K0.of_eq h1, of_diag]
  simp_rw [of_elem hE b.idem (k + _)]
  exact Equiv.sum_comp σ.symm (fun x : Fin 1 × ι => (T (k + s x.2) : L) •
    K0.of (gelem hE b.idem 0)) |>.trans (by rw [Fintype.sum_prod_type]; simp)

end RelBasis

end RelBasis

end OddMath.Frontier.OddCyclotomicAction
