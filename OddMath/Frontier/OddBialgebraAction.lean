import OddMath.Frontier.OddBialgebraRestrict
import OddMath.Frontier.CyclotomicGraded

/-!
# Induction on `K₀(ONH^N)`

EKL arXiv:1111.1320v1, §6, last paragraph (p. 47): `ONH^N = ⊕_{a=0}^{N} ONH_a^N`, and the
functors between the cyclotomic quotients along `ONH_a^N → ONH_{a+1}^N`, `x ↦ x ⊗ 1`, give the
action of `E` on `K₀(ONH^N)`.

* `cycInc N a : ONH_a^N → ONH_{a+1}^N`, induced by `ONH_a → ONH_{a+1}` on the first `a` strands
  (it maps `x̃_1^N` to `x̃_1^N`), graded (`cycInc_mem`).
* `cycE N a : K₀(ONH_a^N) → K₀(ONH_{a+1}^N)`, induction `ONH_{a+1}^N ⊗_{ONH_a^N} -`.
* `vCyc N a`: the class of `E^{(a)} = ONH_a^N e_a {C(a,2)}`; for `a ≤ N` it is a basis of
  `K₀(ONH_a^N) ≅ ℤ[q,q⁻¹]` (`cycRankEquiv_vCyc`), so the `vCyc N a` form a basis `cycBasis N`
  of `K₀(ONH^N)`.
* `cycE_vCyc`: `E [E^{(a)}] = [a+1] [E^{(a+1)}]`, from (6.2) through the cyclotomic quotients;
  `EN_cycBasis`: the induced operator on `K₀(ONH^N)` is `E w_a = [a+1] w_{a+1}` (`w_{N+1} = 0`),
  the action of `E` on the integral form `V(N)_A` of the irreducible module of highest weight `N`
  in its basis `w_a = E^{(a)} w_0` from the lowest weight vector.
-/

noncomputable section
open LaurentPolynomial

namespace OddMath.Frontier.OddBialgebra
open GradedK0 NilHeckeAction OnhWindow OddCategorification QuantumSl2Plus Cyclotomic
open OddMath.SkewPolynomial (SkewPolynomial)

local notation "L" => LaurentPolynomial ℤ

/-! ### Functoriality of extension of scalars -/

section Natural

variable {R S T : Type*} [Ring R] [Ring S] [Ring T] {A : ℤ → AddSubgroup R}
  {B : ℤ → AddSubgroup S} {C : ℤ → AddSubgroup T}

theorem GIdem.mapHom_mapHom (f : R →+* S) (hf : ∀ {d : ℤ} {x : R}, x ∈ A d → f x ∈ B d)
    (g : S →+* T) (hg : ∀ {d : ℤ} {x : S}, x ∈ B d → g x ∈ C d) (h : R →+* T)
    (hh : ∀ {d : ℤ} {x : R}, x ∈ A d → h x ∈ C d) (hgf : ∀ x, g (f x) = h x) (P : GIdem A) :
    GIdem.mapHom g hg (GIdem.mapHom f hf P) = GIdem.mapHom h hh P := by
  have : (P.e.map f).map g = P.e.map h := by
    ext i j
    simp [hgf]
  simp only [GIdem.mapHom, this]

theorem GIdem.mapHom_single [SetLike.GradedMonoid A] [SetLike.GradedMonoid B] (f : R →+* S)
    (hf : ∀ {d : ℤ} {x : R}, x ∈ A d → f x ∈ B d) (k : ℤ) :
    GIdem.mapHom (B := B) f hf (GIdem.single k) ≈ GIdem.single k :=
  MvN.of_equiv (Equiv.refl _) (GIdem.mapHom (B := B) f hf (GIdem.single k)).hom
    (GIdem.mapHom (B := B) f hf (GIdem.single k)).idem (fun _ => rfl) (fun i j => by
      simp only [GIdem.mapHom, GIdem.single, GIdem.free, Equiv.refl_apply]
      rw [Matrix.map_one _ (map_zero f) (map_one f)])

end Natural

/-! ### The inclusions `ONH_a^N → ONH_{a+1}^N` -/

section Inclusions

/-- The ring structure of `OPol`, preferred over the pointwise `Finsupp` structure. -/
local instance (priority := high) opolRing' (m : ℕ) :
    NonUnitalNonAssocRing (SkewPolynomial m) :=
  @NonAssocRing.toNonUnitalNonAssocRing _ (@Ring.toNonAssocRing _ (OddMath.PbwL3.instRing m))

/-- A ring map out of a quotient by a two-sided ideal contained in the kernel. -/
def liftTwoSided {R S : Type*} [Ring R] [Ring S] (I : TwoSidedIdeal R) (f : R →+* S)
    (h : I ≤ TwoSidedIdeal.ker f) : R ⧸ I.asIdeal →+* S :=
  Ideal.Quotient.lift I.asIdeal f fun _ ha =>
    (TwoSidedIdeal.mem_ker f).1 (h (TwoSidedIdeal.mem_asIdeal.1 ha))

theorem liftTwoSided_mk {R S : Type*} [Ring R] [Ring S] (I : TwoSidedIdeal R) (f : R →+* S)
    (h : I ≤ TwoSidedIdeal.ker f) (x : R) :
    liftTwoSided I f h (Ideal.Quotient.mk I.asIdeal x) = f x :=
  Ideal.Quotient.lift_mk _ _ _

theorem window_le_succ (n : ℕ) : 0 + (n+2) ≤ (n+1)+2 := by omega

/-- `ONH_{n+2}^N → ONH_{n+3}^N`, on the first `n+2` strands. -/
def incCyc (n N : ℕ) : ONH n N →+* ONH (n+1) N :=
  liftTwoSided (cyclotomicIdeal n N) ((toONH (n+1) N).comp (windowHom n (n+1) 0
    (window_le_succ n))) <| by
    rw [cyclotomicIdeal, TwoSidedIdeal.span_le]
    rintro _ rfl
    rw [SetLike.mem_coe, TwoSidedIdeal.mem_ker, RingHom.comp_apply, map_pow, firstDot,
      windowHom_dot]
    exact toONH_firstDot_pow (n+1) N

theorem incCyc_toONH (n N : ℕ) (x : Presented n) :
    incCyc n N (toONH n N x) = toONH (n+1) N (windowHom n (n+1) 0 (window_le_succ n) x) :=
  liftTwoSided_mk _ _ _ x

theorem dotHom_generator (n : ℕ) (j : Fin (n+2)) :
    dotHom n j (OddMath.SkewPolynomial.generator 0 : SkewPolynomial 1) = dot n j := by
  show dotHom n j (Finsupp.single _ 1) = _
  rw [dotHom_single, one_smul]
  simp [OddMath.SkewPolynomial.expSingle]

/-- `ONH_1^N → ONH_2^N`, `x ↦ x_1`. -/
def incCyc1 (N : ℕ) : ONH1 N →+* ONH 0 N :=
  liftTwoSided (cyc1Ideal N) ((toONH 0 N).comp (dotHom 0 0)) <| by
    rw [cyc1Ideal, TwoSidedIdeal.span_le]
    rintro _ rfl
    rw [SetLike.mem_coe, TwoSidedIdeal.mem_ker, RingHom.comp_apply, map_pow, dotHom_generator]
    exact toONH_firstDot_pow 0 N

theorem incCyc1_toONH1 (N : ℕ) (x : SkewPolynomial 1) :
    incCyc1 N (toONH1 N x) = toONH 0 N (dotHom 0 0 x) :=
  liftTwoSided_mk _ _ _ x

theorem incCyc_mem {n N : ℕ} {d : ℤ} {x : ONH n N} (hx : x ∈ onhCycGrading n N d) :
    incCyc n N x ∈ onhCycGrading (n+1) N d := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [show (toONH n N).toAddMonoidHom y = toONH n N y from rfl, incCyc_toONH]
  exact map_mem_imageGrading _ (winPiece_le _ _ _ (windowHom_mem _ hy))

theorem incCyc1_mem {N : ℕ} {d : ℤ} {x : ONH1 N} (hx : x ∈ onh1Grading N d) :
    incCyc1 N x ∈ onhCycGrading 0 N d := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [show (toONH1 N).toAddMonoidHom y = toONH1 N y from rfl, incCyc1_toONH1]
  exact map_mem_imageGrading _ (winPiece_le _ _ _ (dotHom_mem 0 hy))

theorem intCast_onh1_mem {N : ℕ} {d : ℤ} {x : ℤ} (hx : x ∈ intGrading d) :
    Int.castRingHom (ONH1 N) x ∈ onh1Grading N d := by
  rcases (hx : x = 0 ∨ d = 0) with h | h
  · rw [h, map_zero]; exact zero_mem _
  · rw [h]; exact GradedK0.intCast_mem x

end Inclusions

theorem toONH_mem {n N : ℕ} {d : ℤ} {x : Presented n} (hx : x ∈ onhGrading n d) :
    toONH n N x ∈ onhCycGrading n N d :=
  map_mem_imageGrading _ hx

theorem toONH1_mem {N : ℕ} {d : ℤ} {x : SkewPolynomial 1} (hx : x ∈ opolGrading d) :
    toONH1 N x ∈ onh1Grading N d :=
  map_mem_imageGrading _ hx

/-! ### Induction on `K₀(ONH^N)` -/

/-- Induction `K₀(ONH_a^N) → K₀(ONH_{a+1}^N)` along `ONH_a^N → ONH_{a+1}^N`. -/
def cycE (N : ℕ) : (a : ℕ) → KCyc N a →ₗ[L] KCyc N (a + 1)
  | 0 => k0Map (Int.castRingHom (ONH1 N)) intCast_onh1_mem
  | 1 => k0Map (incCyc1 N) incCyc1_mem
  | n+2 => k0Map (incCyc n N) incCyc_mem

/-- The quotient `K₀(ONH_a) → K₀(ONH_a^N)`. -/
def toKCyc (N : ℕ) : (a : ℕ) → KONH a →ₗ[L] KCyc N a
  | 0 => LinearMap.id
  | 1 => k0Map (toONH1 N) toONH1_mem
  | n+2 => k0Map (toONH n N) toONH_mem

/-- The class `[E^{(a)}] ∈ K₀(ONH_a^N)`. -/
def vCyc (N a : ℕ) : KCyc N a := toKCyc N a (Eclass a)

theorem qInt_one : qInt 1 = 1 := by simp [qInt]

theorem toKCyc_single_one (N : ℕ) :
    toKCyc N 1 (K0.of (GIdem.single 0 : GIdem opolGrading)) =
      K0.of (GIdem.single 0 : GIdem (onh1Grading N)) := by
  show k0Map (toONH1 N) _ (K0.of _) = _
  rw [k0Map_of]
  exact K0.of_eq (GIdem.mapHom_single (toONH1 N) toONH1_mem 0)

theorem toKCyc_divE (N n : ℕ) :
    toKCyc N (n+2) (Eclass (n+2)) =
      K0.of (GIdem.mapHom (toONH n N) toONH_mem (divE n)) :=
  k0Map_of _ _ _

/-- `[ONH_a^N] = [a]! [E^{(a)}]` in `K₀(ONH_a^N)`. -/
theorem cyc_single_eq (N n : ℕ) :
    K0.of (GIdem.single 0 : GIdem (onhCycGrading n N)) = qFact (n+2) • vCyc N (n+2) := by
  have h := congrArg (k0Map (A := onhGrading n) (B := onhCycGrading n N) (toONH n N) toONH_mem)
    (eq_6_1_qFact n)
  rw [map_smul, k0Map_of, K0.of_eq (GIdem.mapHom_single (A := onhGrading n)
    (B := onhCycGrading n N) (toONH n N) toONH_mem 0)] at h
  rw [h]
  rfl

/-- `[E^{(a)}] ∈ K₀(ONH_a^N) ≅ ℤ[q,q⁻¹]` is the unit `q^{-C(a,2)}`. -/
theorem cycRankEquiv_vCyc (N : ℕ) : ∀ a (h : a ≤ N),
    cycRankEquiv N a h (vCyc N a) = T (-((a.choose 2 : ℕ) : ℤ))
  | 0, _ => K0.classify_single intConnected 0
  | 1, h => by
    show K0.classify (onh1Connected h) (toKCyc N 1 (K0.of (GIdem.single 0))) = _
    rw [toKCyc_single_one, K0.classify_single]
    simp
  | n+2, h => by
    show onhCycK0Equiv n N h (vCyc N (n+2)) = _
    have h1 := congrArg (onhCycK0Equiv n N h) (cyc_single_eq N n)
    rw [onhCycK0Equiv_one_qFact, map_smul, smul_eq_mul, mul_comm] at h1
    exact (mul_left_cancel₀ (qFact_ne_zero (n+2)) h1).symm

/-- **Induction on the cyclotomic quotients**: `E [E^{(a)}] = [a+1] [E^{(a+1)}]` in
`K₀(ONH_{a+1}^N)`. -/
theorem cycE_vCyc (N : ℕ) : ∀ a, cycE N a (vCyc N a) = qInt (a+1) • vCyc N (a+1)
  | 0 => by
    show k0Map (Int.castRingHom (ONH1 N)) _ (K0.of (GIdem.single 0)) =
      qInt 1 • toKCyc N 1 (K0.of (GIdem.single 0))
    rw [k0Map_of, toKCyc_single_one, qInt_one, one_smul]
    exact K0.of_eq (GIdem.mapHom_single (Int.castRingHom (ONH1 N)) intCast_onh1_mem 0)
  | 1 => by
    show k0Map (incCyc1 N) _ (toKCyc N 1 (K0.of (GIdem.single 0))) = _
    rw [toKCyc_single_one, k0Map_of, K0.of_eq (GIdem.mapHom_single (A := onh1Grading N)
      (B := onhCycGrading 0 N) (incCyc1 N) incCyc1_mem 0),
      cyc_single_eq, qFact_two]
  | n+2 => by
    show k0Map (incCyc n N) _ (toKCyc N (n+2) (Eclass (n+2))) = _
    rw [toKCyc_divE, k0Map_of]
    have hw : ∀ {d : ℤ} {x : Presented n}, x ∈ onhGrading n d →
        windowHom n (n+1) 0 (window_le_succ n) x ∈ onhGrading (n+1) d :=
      fun hx => winPiece_le _ _ _ (windowHom_mem _ hx)
    rw [GIdem.mapHom_mapHom (toONH n N) _ (incCyc n N) incCyc_mem
      ((toONH (n+1) N).comp (windowHom n (n+1) 0 (window_le_succ n)))
      (fun hx => toONH_mem (hw hx)) (incCyc_toONH n N),
      ← GIdem.mapHom_mapHom (windowHom n (n+1) 0 (window_le_succ n)) hw (toONH (n+1) N)
        toONH_mem _ _ (fun _ => rfl)]
    have hab : (n+2) + 1 = (n+1) + 2 := by omega
    have hE : GIdem.mapHom (windowHom n (n+1) 0 (window_le_succ n)) hw (divE n) ≈ indE hab := by
      refine MvN.of_equiv (Equiv.refl _) (GIdem.mapHom _ hw (divE n)).hom
        (GIdem.mapHom _ hw (divE n)).idem (fun _ => ?_) (fun i j => ?_)
      · simp [indE, divE, projE, gelem, gdiag, GIdem.mapHom]
      · simp only [indE, divE, projE, gelem, gdiag, GIdem.mapHom, Equiv.refl_apply,
          Matrix.map_apply, Matrix.diagonal_apply]
        rw [ThickBubble.blockE_one, mul_one, ThickBubble.blockE_eq (window_le_succ n)]
        split_ifs <;> simp
    have h2 := congrArg (k0Map (A := onhGrading (n+1)) (B := onhCycGrading (n+1) N)
      (toONH (n+1) N) toONH_mem) (eq_6_2_K0 hab)
    rw [map_smul, k0Map_of, k0Map_of] at h2
    rw [← k0Map_of, K0.of_eq hE, k0Map_of, h2, TwTensor.qBinom_one]
    rfl

/-- `K₀(ONH_{N+1}^N) = 0`, so `E [E^{(N)}] = 0`. -/
theorem cycE_vCyc_top (N : ℕ) : cycE N N (vCyc N N) = 0 :=
  haveI := KCyc_subsingleton N (N+1) (Nat.lt_succ_self N)
  Subsingleton.elim _ _

/-! ### The action of `E` on `K₀(ONH^N)` -/

theorem Fin.le_of_lt_succ' {N : ℕ} (a : Fin (N+1)) : (a : ℕ) ≤ N := Nat.lt_succ_iff.mp a.isLt

/-- The basis `{[E^{(a)}]}` of `K₀(ONH_a^N)`, `a ≤ N`. -/
def cycBasisComp (N : ℕ) (a : Fin (N+1)) : Basis (Fin 1) L (KCyc N a) :=
  ((Basis.singleton (Fin 1) L).map (cycRankEquiv N a (Fin.le_of_lt_succ' a)).symm).unitsSMul
    fun _ => (isUnit_T (-((((a : ℕ)).choose 2 : ℕ) : ℤ))).unit

theorem cycBasisComp_apply (N : ℕ) (a : Fin (N+1)) (i : Fin 1) :
    cycBasisComp N a i = vCyc N a := by
  rw [cycBasisComp, Basis.unitsSMul_apply, Basis.map_apply, Basis.singleton_apply, Units.smul_def,
    IsUnit.unit_spec, ← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_eq,
    cycRankEquiv_vCyc]

/-- The basis `{[E^{(a)}] : 0 ≤ a ≤ N}` of `K₀(ONH^N) = ⊕_{a ≤ N} K₀(ONH_a^N)`. -/
def cycBasis (N : ℕ) : Basis (Fin (N+1)) L (K0Cyc N) :=
  (DFinsupp.basis (cycBasisComp N)).reindex (Equiv.sigmaUnique (Fin (N+1)) fun _ => Fin 1)

theorem cycBasis_apply (N : ℕ) (a : Fin (N+1)) :
    cycBasis N a = DFinsupp.single a (vCyc N a) := by
  rw [cycBasis, Basis.reindex_apply]
  simp [DFinsupp.basis, sigmaFinsuppLequivDFinsupp, cycBasisComp_apply]

/-- `E` on `K₀(ONH^N)`: induction `K₀(ONH_a^N) → K₀(ONH_{a+1}^N)` in each weight. -/
def EN (N : ℕ) : K0Cyc N →ₗ[L] K0Cyc N :=
  DFinsupp.lsum L fun a : Fin (N+1) =>
    if h : (a : ℕ) < N then (DFinsupp.lsingle (⟨a + 1, by omega⟩ : Fin (N+1))).comp (cycE N a)
    else 0

/-- **`E` on `K₀(ONH^N)`**: `E [E^{(a)}] = [a+1] [E^{(a+1)}]` for `a < N`. -/
theorem EN_cycBasis (N : ℕ) (a : Fin (N+1)) (ha : (a : ℕ) < N) :
    EN N (cycBasis N a) = qInt (a + 1) • cycBasis N ⟨a + 1, by omega⟩ := by
  rw [cycBasis_apply, cycBasis_apply, EN, DFinsupp.lsum_single, dif_pos ha, LinearMap.comp_apply,
    cycE_vCyc, DFinsupp.lsingle_apply, DFinsupp.single_smul]

/-- `E [E^{(N)}] = 0`. -/
theorem EN_cycBasis_last (N : ℕ) : EN N (cycBasis N (Fin.last N)) = 0 := by
  rw [cycBasis_apply, EN, DFinsupp.lsum_single, dif_neg (by simp), LinearMap.zero_apply]

end OddMath.Frontier.OddBialgebra
