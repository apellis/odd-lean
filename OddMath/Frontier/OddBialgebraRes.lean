import OddMath.Frontier.OddBialgebraFree
import OddMath.Frontier.OddBialgebraInd

/-!
# Restriction `K₀(ONH_{a+b}) → K₀(ONH_a ⊗ ONH_b)`

EKL arXiv:1111.1320v1, §6, pp. 46–47: the inclusions `ONH_a ⊗ ONH_b ⊂ ONH_{a+b}` give rise to
restriction functors. Here `a = m+2`, `b = m'+2`, `n = a + b`, `B = ONH_a ⊗ ONH_b ⊂ ONH_n`
(`OnhStructure.tensorImage`) with the grading `gradB` restricted from `ONH_n`.

Since `ONH_n = ⊕_u B ∂_u` is free over `B` (`OddBialgebraFree`), restricting `ONH_n^k{s} e` to `B`
gives the graded idempotent `(ρ(e_{ij}))` on `B^{k × Shuffle}` with shifts `s_i - 2ℓ(u)`, where
`ρ(x)_{uv}` is the `∂_v`-coordinate of `∂_u x` (`rho`, a graded ring map
`ONH_n → Mat_{Shuffle}(B)`); on `K₀` this is `K₀(ρ)` followed by graded Morita invariance.

* `GIdem.mapHom`, `k0Map`: `K₀` of a graded ring map (extension of scalars).
* `resIdem`, `res : K₀(ONH_n) →ₗ K₀(B)`.
* `res_one`: `Res [ONH_n] = ∑_u q^{-2ℓ(u)} [B] = q^{-ab} [n, a] [B]`, with
  `∑_{u} q^{-2ℓ(u)} = q^{-ab} [a+b, a]` over the shuffles (`sum_shuffle_length`).
* `pairB`, `boxE`: `E^{(a)} ⊠ E^{(b)} = B(e_a ⊗ e_b){C(a,2) + C(b,2)}`, and
  `[B] = [a]! [b]! [E^{(a)} ⊠ E^{(b)}]` (`class_B`).
* `res_divE`: `[n]! (Res [E^{(n)}] - q^{-ab} [E^{(a)} ⊠ E^{(b)}]) = 0` in `K₀(B)`. So
  `Res [E^{(n)}] = q^{-ab} [E^{(a)} ⊠ E^{(b)}]` as soon as `K₀(B)` has no `[n]!`-torsion (e.g.
  `K₀(B) ≅ ℤ[q,q⁻¹]`, which is not proved here): the shift is `c(a,b) = -ab`, matching
  `Δ(ϑ^{(n)}) = ∑ q^{-ab} ϑ^{(a)} ⊗ ϑ^{(b)}` of `OddBialgebraCoproduct`.
-/

noncomputable section
open Matrix LaurentPolynomial

namespace OddMath.Frontier.OddBialgebra
open GradedK0 NilCoxeterWords NilHeckeAction OnhStructure OnhWindow OddCategorification
  QuantumSl2Plus

local notation "L" => LaurentPolynomial ℤ

/-! ### Extension of scalars along a graded ring map -/

section MapHom

variable {R S : Type*} [Ring R] [Ring S] {A : ℤ → AddSubgroup R} {B : ℤ → AddSubgroup S}
  [SetLike.GradedMonoid A] [SetLike.GradedMonoid B] (φ : R →+* S)
  (hφ : ∀ {d : ℤ} {x : R}, x ∈ A d → φ x ∈ B d)

omit [SetLike.GradedMonoid A] [SetLike.GradedMonoid B] in
include hφ in
theorem isHom_mapHom {ι κ : Type*} {s : ι → ℤ} {t : κ → ℤ} {u : Matrix ι κ R}
    (hu : IsHom A s t u) : IsHom B s t (u.map φ) := fun i j => hφ (hu i j)

omit [SetLike.GradedMonoid A] [SetLike.GradedMonoid B] in
include hφ in
theorem mvn_mapHom {ι κ : Type*} [Fintype ι] [Fintype κ] {s : ι → ℤ} {e : Matrix ι ι R}
    {t : κ → ℤ} {f : Matrix κ κ R} (h : MvN A s e t f) : MvN B s (e.map φ) t (f.map φ) := by
  obtain ⟨u, v, hu, hv, h1, h2, h3, h4⟩ := h
  exact ⟨u.map φ, v.map φ, isHom_mapHom φ hφ hu, isHom_mapHom φ hφ hv,
    by rw [← Matrix.map_mul, h1], by rw [← Matrix.map_mul, h2],
    by rw [← Matrix.map_mul, ← Matrix.map_mul, h3], by rw [← Matrix.map_mul, ← Matrix.map_mul, h4]⟩

/-- Extension of scalars `S ⊗_R -` on graded idempotents: `(n, s, e) ↦ (n, s, φ(e))`. -/
def GIdem.mapHom (P : GIdem A) : GIdem B where
  n := P.n
  s := P.s
  e := P.e.map φ
  hom := isHom_mapHom φ hφ P.hom
  idem := by rw [← Matrix.map_mul, P.idem]

omit [SetLike.GradedMonoid A] in
theorem GIdem.mapHom_sum (P Q : GIdem A) :
    GIdem.mapHom φ hφ (P.sum Q) ≈ (GIdem.mapHom φ hφ P).sum (GIdem.mapHom φ hφ Q) := by
  refine MvN.of_equiv (Equiv.refl _) (GIdem.mapHom φ hφ (P.sum Q)).hom
    (GIdem.mapHom φ hφ (P.sum Q)).idem (fun i => ?_) (fun i j => ?_)
  · rfl
  · show fromBlocks (P.e.map φ) 0 0 (Q.e.map φ) (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) =
      φ (fromBlocks P.e 0 0 Q.e (finSumFinEquiv.symm i) (finSumFinEquiv.symm j))
    generalize finSumFinEquiv.symm i = x
    generalize finSumFinEquiv.symm j = y
    cases x <;> cases y <;> simp

/-- `K₀` of a graded ring map, on isomorphism classes. -/
def gprojMapHom : GProj A →+ GProj B where
  toFun := Quotient.map (GIdem.mapHom φ hφ) fun _ _ h => mvn_mapHom φ hφ h
  map_zero' := GProj.mk_eq_mk.2 (MvN.of_equiv (Equiv.refl _)
    (GIdem.mapHom φ hφ GIdem.zero).hom (GIdem.mapHom φ hφ GIdem.zero).idem
    (fun i => i.elim0) (fun i => i.elim0))
  map_add' := by
    refine GProj.ind fun P => GProj.ind fun Q => ?_
    exact GProj.mk_eq_mk.2 (GIdem.mapHom_sum φ hφ P Q)

/-- `K₀` of a graded ring map: `[P] ↦ [S ⊗_R P]`, `ℤ[q,q⁻¹]`-linear. -/
def k0Map : K0 A →ₗ[L] K0 B :=
  let F : K0 A →+ K0 B := GrothendieckGroup.map (gprojMapHom φ hφ)
  { F with
    map_smul' := K0.map_smul_of_shift F fun k x => by
      rw [K0.T_smul]
      have : F.comp (K0.shift k) = (K0.shift k).comp F := K0.hom_ext fun P => by
        rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, K0.shift_of,
          show F (K0.of (P.shift k)) = K0.of (GIdem.mapHom φ hφ (P.shift k)) from
            GrothendieckGroup.map_of _ _,
          show F (K0.of P) = K0.of (GIdem.mapHom φ hφ P) from GrothendieckGroup.map_of _ _,
          K0.shift_of]
        rfl
      exact DFunLike.congr_fun this x }

theorem k0Map_of (P : GIdem A) : k0Map φ hφ (K0.of P) = K0.of (GIdem.mapHom φ hφ P) :=
  GrothendieckGroup.map_of _ _

end MapHom

/-! ### Restriction -/

variable {m m' : ℕ}

theorem isShuffle_one : IsShuffle (1 : Perm (m+2+m')) :=
  ⟨fun k k' h => by
    show (Fin.castAdd (m'+2) k : Fin (m+2+m'+2)) < Fin.castAdd (m'+2) k'
    exact Fin.lt_def.2 (by simp only [Fin.coe_castAdd]; exact Fin.lt_def.1 h),
   fun k k' h => by
    show (Fin.natAdd (m+2) k : Fin (m+2+m'+2)) < Fin.natAdd (m+2) k'
    exact Fin.lt_def.2 (by simp only [Fin.coe_natAdd]; have := Fin.lt_def.1 h; omega)⟩

instance : Nonempty (Shuffle m m') := ⟨⟨1, isShuffle_one⟩⟩

/-- The shifts `2ℓ(u)` of the free basis `∂_u`. -/
abbrev shufShift (m m' : ℕ) (u : Shuffle m m') : ℤ := 2 * (length u.1 : ℤ)

/-- **Restriction** of a graded idempotent of `ONH_{a+b}` to `B = ONH_a ⊗ ONH_b`:
`(k, s, e) ↦ (k · C(a+b, a), s_i - 2ℓ(u), ρ(e_{ij})_{uv})`. -/
def resIdem (P : GIdem (onhGrading (m+2+m'))) : GIdem (gradB m m') :=
  (GIdem.mapHom (B := matGrading (gradB m m') (shufShift m m')) (rho m m') rho_mem P).flatten

/-- **Restriction** `K₀(ONH_{a+b}) → K₀(ONH_a ⊗ ONH_b)`. -/
def res (m m' : ℕ) : K0 (onhGrading (m+2+m')) →ₗ[L] K0 (gradB m m') :=
  K0.morita.toLinearMap ∘ₗ k0Map (B := matGrading (gradB m m') (shufShift m m')) (rho m m') rho_mem

theorem res_of (P : GIdem (onhGrading (m+2+m'))) : res m m' (K0.of P) = K0.of (resIdem P) := by
  rw [res, LinearMap.comp_apply, k0Map_of, LinearEquiv.coe_coe, K0.morita_of]
  rfl

/-- `Res [ONH_{a+b}] = ∑_u q^{-2ℓ(u)} [B]`: `ONH_{a+b} = ⊕_u B ∂_u ≅ ⊕_u B{-2ℓ(u)}`. -/
theorem res_one : res m m' (K0.of (GIdem.single 0)) =
    ∑ u : Shuffle m m', (T (-(2 * (length u.1 : ℤ))) : L) •
      K0.of (GIdem.single 0 : GIdem (gradB m m')) := by
  rw [res_of]
  set Q := GIdem.mapHom (B := matGrading (gradB m m') (shufShift m m')) (rho m m') rho_mem
    (GIdem.single 0 : GIdem (onhGrading (m+2+m')))
  have hQ : Q.e = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h1 : flat Q.e = 1 := by
    rw [hQ]
    exact (Matrix.compRingEquiv (Fin 1) (Shuffle m m') (tensorImage m m')).map_one
  let σ := Fintype.equivFin (Fin Q.n × Shuffle m m')
  let t : Fin (Fintype.card (Fin Q.n × Shuffle m m')) → ℤ :=
    fun i => Q.s (σ.symm i).1 - shufShift m m' (σ.symm i).2
  have h2 : MvN (gradB m m') (fun x : Fin Q.n × Shuffle m m' => Q.s x.1 - shufShift m m' x.2)
      (flat Q.e) (GIdem.free (A := gradB m m') t).s (GIdem.free (A := gradB m m') t).e := by
    rw [h1]
    refine MvN.of_equiv σ (IsHom.one (A := gradB m m')) (mul_one 1)
      (fun x => by simp [t, GIdem.free]) ?_
    intro x y
    simp only [GIdem.free, Matrix.one_apply, σ.injective.eq_iff]
  have h3 : resIdem (GIdem.single 0) ≈ GIdem.free (A := gradB m m') t :=
    MvN.trans (resIdem _).idem (GIdem.flat_idem Q) (GIdem.free t).idem (GIdem.mvn_flatten Q).symm
      h2
  rw [K0.of_eq h3, K0.of_free,
    ← Equiv.sum_comp σ (fun a => K0.of (GIdem.single (A := gradB m m') (t a))),
    Fintype.sum_prod_type]
  simp only [t, Equiv.symm_apply_apply]
  change ∑ _x : Fin 1, ∑ u : Shuffle m m',
    K0.of (GIdem.single (A := gradB m m') (0 - shufShift m m' u)) = _
  rw [Fin.sum_univ_one]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [K0.T_smul_single, zero_sub]

/-- `∑_{w ∈ S_{n+2}} q^{-2ℓ(w)} = q^{-C(n+2, 2)} [n+2]!`. -/
theorem sum_perm_length (n : ℕ) :
    ∑ w : Perm n, (T (-(2 * (length w : ℤ))) : L) =
      T (-(((n+2).choose 2 : ℕ) : ℤ)) * qFact (n+2) := by
  rw [sum_T_length_eq, ← sum_Sq_eq_qFact, Finset.mul_sum,
    ← Finset.sum_coe_sort (BoxPartitionCount.Sq (n+2))]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [← T_add]
  congr 1
  ring

/-- **Shuffles and the Gaussian binomial**: `∑_{u} q^{-2ℓ(u)} = q^{-ab} [a+b, a]`, `u` running
over the minimal coset representatives of `S_a × S_b ⊂ S_{a+b}`. -/
theorem sum_shuffle_length :
    ∑ u : Shuffle m m', (T (-(2 * (length u.1 : ℤ))) : L) =
      T (-(((m+2) * (m'+2) : ℕ) : ℤ)) * qBinom (m+2) (m'+2) := by
  set S := ∑ u : Shuffle m m', (T (-(2 * (length u.1 : ℤ))) : L)
  have hsplit : ∑ w : Perm (m+2+m'), (T (-(2 * (length w : ℤ))) : L) =
      (∑ y : Perm m, (T (-(2 * (length y : ℤ))) : L)) *
        (∑ y : Perm m', (T (-(2 * (length y : ℤ))) : L)) * S := by
    calc ∑ w : Perm (m+2+m'), (T (-(2 * (length w : ℤ))) : L)
        = ∑ p : (Perm m × Perm m') × Shuffle m m',
            (T (-(2 * (length (factorEquiv p) : ℤ))) : L) :=
          (Equiv.sum_comp factorEquiv (fun w => (T (-(2 * (length w : ℤ))) : L))).symm
      _ = ∑ p : (Perm m × Perm m') × Shuffle m m',
            (T (-(2 * (length p.1.1 : ℤ))) * T (-(2 * (length p.1.2 : ℤ))) : L) *
              T (-(2 * (length p.2.1 : ℤ))) := by
          refine Fintype.sum_congr _ _ fun p => ?_
          rw [factorEquiv_apply, length_blockPerm_mul _ _ p.2.2, length_blockPerm, ← T_add,
            ← T_add]
          congr 1
          push_cast
          ring
      _ = (∑ y : Perm m × Perm m', (T (-(2 * (length y.1 : ℤ))) *
            T (-(2 * (length y.2 : ℤ))) : L)) * S := by
          rw [Fintype.sum_prod_type, Finset.sum_mul]
          simp only [Finset.mul_sum, S]
      _ = _ := by
          congr 1
          rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  rw [sum_perm_length, sum_perm_length, sum_perm_length] at hsplit
  have hc : (((m+2+m'+2).choose 2 : ℕ) : ℤ) =
      (((m+2).choose 2 : ℕ) : ℤ) + (((m'+2).choose 2 : ℕ) : ℤ) + (((m+2) * (m'+2) : ℕ) : ℤ) := by
    rw [show m+2+m'+2 = (m+2) + (m'+2) by omega, BoxComplement.choose_two_add]
    push_cast
    ring
  have hq := qBinom_mul_qFact (m+2) (m'+2)
  rw [show m+2+(m'+2) = m+2+m'+2 by omega] at hq
  refine mul_right_cancel₀ (mul_ne_zero (mul_ne_zero (qFact_ne_zero (m+2))
    (qFact_ne_zero (m'+2))) (isUnit_T (-((((m+2).choose 2 : ℕ) : ℤ) +
      (((m'+2).choose 2 : ℕ) : ℤ)))).ne_zero) ?_
  calc S * (qFact (m+2) * qFact (m'+2) * T (-((((m+2).choose 2 : ℕ) : ℤ) +
        (((m'+2).choose 2 : ℕ) : ℤ))))
      = T (-(((m+2).choose 2 : ℕ) : ℤ)) * qFact (m+2) * (T (-(((m'+2).choose 2 : ℕ) : ℤ)) *
          qFact (m'+2)) * S := by
        rw [neg_add, T_add]
        ring
    _ = T (-(((m+2+m'+2).choose 2 : ℕ) : ℤ)) * qFact (m+2+m'+2) := hsplit.symm
    _ = _ := by
        rw [← hq, hc, neg_add, neg_add, T_add, T_add]
        ring

/-! ### `E^{(a)} ⊠ E^{(b)}` -/

/-- `ONH_a → B ← ONH_b`, as a super pair. -/
def pairB (m m' : ℕ) : SuperPair (onhGrading m) (onhGrading m') (gradB m m') where
  ι₁ := (incL m m').codRestrict (tensorImage m m') incL_mem_tensorImage
  ι₂ := (incR m m').codRestrict (tensorImage m m') incR_mem_tensorImage
  map₁ hx := winPiece_le _ _ _ (windowHom_mem (window_left_le m m') hx)
  map₂ hy := winPiece_le _ _ _ (windowHom_mem (window_right_le m m') hy)
  even₁ := onh_even
  even₂ := onh_even
  comm hx hy := Subtype.ext <| by
    have := winPiece_supercomm (windowHom_mem (window_left_le m m') hx)
      (windowHom_mem (window_right_le m m') hy) (by omega)
    rw [Units.smul_def] at this ⊢
    exact this

/-- `E^{(a)} ⊠ E^{(b)} = B (e_a ⊗ e_b) {C(a,2) + C(b,2)}`. -/
def boxE (m m' : ℕ) : GIdem (gradB m m') := (pairB m m').ind (divE m) (divE m')

/-- `[B] = [a]! [b]! [E^{(a)} ⊠ E^{(b)}]` in `K₀(B)`. -/
theorem class_B : K0.of (GIdem.single 0 : GIdem (gradB m m')) =
    (qFact (m+2) * qFact (m'+2)) • K0.of (boxE m m') := by
  have h : K0.of (GIdem.single 0 : GIdem (gradB m m')) =
      (pairB m m').indK0 (K0.of (GIdem.single 0)) (K0.of (GIdem.single 0)) :=
    ((pairB m m').indK0_of_of _ _).trans (K0.of_eq ((pairB m m').ind_gelem
      SetLike.GradedOne.one_mem (one_mul 1) SetLike.GradedOne.one_mem (one_mul 1)
      SetLike.GradedOne.one_mem (one_mul 1) (by rw [map_one, map_one, one_mul]) (add_zero 0)))
      |>.symm
  rw [h, eq_6_1_qFact, eq_6_1_qFact, map_smul, LinearMap.map_smul₂, smul_smul,
    SuperPair.indK0_of_of, boxE, mul_comm]

/-- **Restriction of `E^{(a+b)}`**: `[a+b]! (Res [E^{(a+b)}] - q^{-ab} [E^{(a)} ⊠ E^{(b)}]) = 0`
in `K₀(ONH_a ⊗ ONH_b)`. -/
theorem res_divE : qFact (m+2+m'+2) •
    (res m m' (K0.of (divE (m+2+m'))) - (T (-(((m+2) * (m'+2) : ℕ) : ℤ)) : L) •
      K0.of (boxE m m')) = 0 := by
  rw [smul_sub, ← map_smul, ← eq_6_1_qFact, res_one, ← Finset.sum_smul, sum_shuffle_length,
    class_B, smul_smul, smul_smul, sub_eq_zero]
  congr 1
  have hq := qBinom_mul_qFact (m+2) (m'+2)
  rw [show m+2+(m'+2) = m+2+m'+2 by omega] at hq
  rw [← hq]
  ring

end OddMath.Frontier.OddBialgebra
