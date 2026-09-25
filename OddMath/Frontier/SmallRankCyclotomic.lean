import OddMath.Frontier.SmallRank
import OddMath.Frontier.CyclotomicGraded

/-!
# Ranks `0` and `1`: odd Grassmannians and cyclotomic quotients

EKL arXiv:1111.1320v1, §5, pp. 44–46, for every rank `a`. The odd Grassmannian ring
`OH_{a,N} = OΛ_a/⟨h_m : m > N − a⟩` is defined here for every `a` (`OH`); for `a = n+2` it is
`Cyclotomic.OH n N` (`OH_add_two`). In rank `0`, `OΛ_0 = ℤ` and every `h_m`, `m > 0`, vanishes;
in rank `1`, `OΛ_1 = ℤ[x]` and `h_m = x^m`. The cyclotomic quotients are `ONH_0^N = ℤ` and
`ONH_1^N = ℤ[x]/(x^N)` (`Cyclotomic.ONH1`).

* `OH_{a,N} = 0` for `N < a`, every `a` (`OH_subsingleton_all`).
* `OH_{0,N} ≅ ℤ` (`OH_zero_equiv`), `OH_{1,N} ≅ ONH_1^N = ℤ[x]/(x^N)` (`OH_one_equiv`), and
  `OH_{a,a} ≅ ℤ` for `a ≤ 1` (`OH_self_equiv_small`).
* **Prop 5.2**, `a ≤ 1`: `ONH_a^N ≅ Mat_{a!}(OH_{a,N})` with `a! = 1` (`prop_5_2_zero`,
  `prop_5_2_one`).
* **Prop 5.4**, `a ≤ 1`: `OH_{a,N}` is free of rank `C(N, a)`, with basis `1` for `a = 0` and
  `1, x, …, x^{N-1}` for `a = 1` (`basis_OH_zero`, `basis_OH_one`, `finrank_OH_zero`,
  `finrank_OH_one`).

Lemma 5.1 and (5.5)–(5.9) concern the `a × a` matrix of `x̃_1` over `OΛ_a`; for `a = 1` the matrix
is `(x)` and Lemma 5.1 reads `x · 1 = 1 · x`, for `a = 0` there is no `x̃_1`.
-/

namespace OddMath.Frontier.SmallRank
open OddMath.SkewPolynomial (SkewPolynomial generator monomial)
open FiniteCompleteElementary
open scoped BigOperators

noncomputable section

/-- The ring structure of `OPol`, preferred over the pointwise `Finsupp` structure. -/
local instance (priority := high) opolNonUnitalNonAssocRing' (m : ℕ) :
    NonUnitalNonAssocRing (SkewPolynomial m) :=
  @NonAssocRing.toNonUnitalNonAssocRing _ (@Ring.toNonAssocRing _ (OddMath.PbwL3.instRing m))

/-! ## `h_m` in every rank -/

theorem complete_mem_OLam (N m : ℕ) : completePoly N m ∈ OLam N := by
  match N with
  | 0 => exact mem_OLam_small (by omega) _
  | 1 => exact mem_OLam_small le_rfl _
  | n+2 => exact OddSymmetricKernel.complete_mem n m

/-- `h_m ∈ OΛ_N` (EKL (2.30)). -/
def hAll (N m : ℕ) : OLam N := ⟨completePoly N m, complete_mem_OLam N m⟩

@[simp] theorem hAll_zero (N : ℕ) : hAll N 0 = 1 := Subtype.ext (completePoly_zero N)

/-! ## `OH_{a,N}` in every rank -/

/-- The generators `h_m`, `m > N − a`, of the odd Grassmannian ideal. -/
def grassGen (a N : ℕ) : Set (OLam a) := {x | ∃ m, N < m + a ∧ hAll a m = x}

/-- `⟨h_m : m > N − a⟩ ⊂ OΛ_a`, EKL p. 44. -/
def grassIdeal (a N : ℕ) : TwoSidedIdeal (OLam a) := TwoSidedIdeal.span (grassGen a N)

/-- The odd Grassmannian ring `OH_{a,N} = OΛ_a/⟨h_m : m > N − a⟩`, EKL p. 44, every rank. -/
def OH (a N : ℕ) : Type := OLam a ⧸ (grassIdeal a N).asIdeal

instance (a N : ℕ) : Ring (OH a N) := Ideal.Quotient.ring _

/-- The quotient map `OΛ_a → OH_{a,N}`. -/
def toOH (a N : ℕ) : OLam a →+* OH a N := Ideal.Quotient.mk _

theorem OH_add_two (n N : ℕ) : OH (n+2) N = Cyclotomic.OH n N := rfl

theorem toOH_hAll {a N m : ℕ} (h : N < m + a) : toOH a N (hAll a m) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr
    (TwoSidedIdeal.mem_asIdeal.mpr (TwoSidedIdeal.subset_span ⟨m, h, rfl⟩))

/-- EKL p. 44, every rank: `OH_{a,N} = 0` for `N < a` (`h_0 = 1` is a generator). For
`a = n+2` this is `Cyclotomic.OH_subsingleton`. -/
theorem OH_subsingleton_all {a N : ℕ} (h : N < a) : Subsingleton (OH a N) := by
  have h1 : toOH a N 1 = 0 := by rw [← hAll_zero]; exact toOH_hAll (by omega)
  rw [map_one] at h1
  exact subsingleton_of_zero_eq_one h1.symm

/-! ## Rank `0`: `OH_{0,N} = ℤ` -/

/-- `OH_{0,N} → ℤ`, the constant term. -/
def OHzeroConst (N : ℕ) : OH 0 N →+* ℤ :=
  Ideal.Quotient.lift _ (zeroEquiv.toRingHom.comp (OLam 0).subtype) fun x hx => by
    have hle : grassIdeal 0 N ≤ TwoSidedIdeal.ker (zeroEquiv.toRingHom.comp (OLam 0).subtype) := by
      rw [grassIdeal, TwoSidedIdeal.span_le]
      rintro _ ⟨m, hm, rfl⟩
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      change zeroEquiv (completePoly 0 (k+1)) = 0
      rw [completePoly_zero_succ, map_zero]
    exact (TwoSidedIdeal.mem_ker _).mp (hle (TwoSidedIdeal.mem_asIdeal.mp hx))

/-- **EKL p. 44** at `a = 0`: `OH_{0,N} ≅ ℤ` for every `N`. -/
def OH_zero_equiv (N : ℕ) : OH 0 N ≃+* ℤ :=
  RingEquiv.ofRingHom (OHzeroConst N) (Int.castRingHom _) (RingHom.ext_int _ _)
    (Ideal.Quotient.ringHom_ext (RingHom.ext fun x => by
      change ((zeroEquiv (x : SkewPolynomial 0) : ℤ) : OH 0 N) = toOH 0 N x
      have hx : x = ((x : SkewPolynomial 0) 0 : OLam 0) :=
        Subtype.ext ((eq_intCast_zero _).trans (by simp))
      conv_rhs => rw [hx]
      rw [map_intCast]
      rfl))

/-- **EKL Prop 5.4**, `a = 0`: `OH_{0,N}` is free on `1`. -/
def basis_OH_zero (N : ℕ) : Basis (Fin 1) ℤ (OH 0 N) :=
  (Basis.singleton (Fin 1) ℤ).map (OH_zero_equiv N).symm.toAddEquiv.toIntLinearEquiv

theorem finrank_OH_zero (N : ℕ) : Module.finrank ℤ (OH 0 N) = N.choose 0 := by
  rw [Module.finrank_eq_card_basis (basis_OH_zero N), Fintype.card_fin, Nat.choose_zero_right]

/-- **EKL Prop 5.2**, `a = 0`: `ONH_0^N = ℤ ≅ Mat_1(OH_{0,N})`. -/
def prop_5_2_zero (N : ℕ) : ℤ ≃+* Matrix (Fin 1) (Fin 1) (OH 0 N) :=
  (OH_zero_equiv N).symm.trans Matrix.uniqueRingEquiv.symm

/-! ## Rank `1`: `OH_{1,N} = ℤ[x]/(x^N) = ONH_1^N` -/

/-- `OPol_1 → OΛ_1 = OPol_1`. -/
def toOLamOne : SkewPolynomial 1 →+* OLam 1 :=
  (RingHom.id (SkewPolynomial 1)).codRestrict (OLam 1) fun f => mem_OLam_small le_rfl f

theorem hAll_one (m : ℕ) : hAll 1 m = toOLamOne (generator 0 ^ m) :=
  Subtype.ext (completePoly_one m)

/-- `OH_{1,N} → ONH_1^N`. -/
def OHoneTo (N : ℕ) : OH 1 N →+* Cyclotomic.ONH1 N :=
  Ideal.Quotient.lift _ ((Cyclotomic.toONH1 N).comp (OLam 1).subtype) fun x hx => by
    have hle : grassIdeal 1 N ≤
        TwoSidedIdeal.ker ((Cyclotomic.toONH1 N).comp (OLam 1).subtype) := by
      rw [grassIdeal, TwoSidedIdeal.span_le]
      rintro _ ⟨m, hm, rfl⟩
      rw [SetLike.mem_coe, TwoSidedIdeal.mem_ker, RingHom.comp_apply, Subring.coe_subtype, hAll,
        completePoly_one, show m = N + (m - N) by omega, pow_add, map_mul]
      have h0 : Cyclotomic.toONH1 N (generator 0 ^ N) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
        (TwoSidedIdeal.mem_asIdeal.mpr (TwoSidedIdeal.subset_span rfl))
      rw [h0, zero_mul]
    exact (TwoSidedIdeal.mem_ker _).mp (hle (TwoSidedIdeal.mem_asIdeal.mp hx))

/-- `ONH_1^N → OH_{1,N}`. -/
def OHoneFrom (N : ℕ) : Cyclotomic.ONH1 N →+* OH 1 N :=
  Ideal.Quotient.lift _ ((toOH 1 N).comp toOLamOne) fun _ hx => by
    have hle : Cyclotomic.cyc1Ideal N ≤ TwoSidedIdeal.ker ((toOH 1 N).comp toOLamOne) := by
      rw [Cyclotomic.cyc1Ideal, TwoSidedIdeal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
        TwoSidedIdeal.mem_ker, RingHom.comp_apply, ← hAll_one]
      exact toOH_hAll (by omega)
    exact (TwoSidedIdeal.mem_ker _).mp (hle (TwoSidedIdeal.mem_asIdeal.mp hx))

/-- **EKL p. 44** at `a = 1`: `OH_{1,N} = OΛ_1/⟨h_m : m ≥ N⟩ ≅ ℤ[x]/(x^N) = ONH_1^N`. -/
def OH_one_equiv (N : ℕ) : OH 1 N ≃+* Cyclotomic.ONH1 N :=
  RingEquiv.ofRingHom (OHoneTo N) (OHoneFrom N)
    (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl))
    (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => congrArg (toOH 1 N) (Subtype.ext rfl)))

/-- **EKL Prop 5.2**, `a = 1`: `ONH_1^N ≅ Mat_1(OH_{1,N})`. -/
def prop_5_2_one (N : ℕ) : Cyclotomic.ONH1 N ≃+* Matrix (Fin 1) (Fin 1) (OH 1 N) :=
  (OH_one_equiv N).symm.trans Matrix.uniqueRingEquiv.symm

/-- `ONH_1^N ≅ ℤ[X]/(X^N)`. -/
def ONH1To (N : ℕ) : Cyclotomic.ONH1 N →+* AdjoinRoot (Polynomial.X ^ N : Polynomial ℤ) :=
  Ideal.Quotient.lift _ ((AdjoinRoot.mk _).comp rankOneEquiv.toRingHom) fun x hx => by
    have hle : Cyclotomic.cyc1Ideal N ≤
        TwoSidedIdeal.ker ((AdjoinRoot.mk (Polynomial.X ^ N)).comp rankOneEquiv.toRingHom) := by
      rw [Cyclotomic.cyc1Ideal, TwoSidedIdeal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
        TwoSidedIdeal.mem_ker, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, map_pow, rankOneEquiv_generator]
      exact AdjoinRoot.mk_self
    exact (TwoSidedIdeal.mem_ker _).mp (hle (TwoSidedIdeal.mem_asIdeal.mp hx))

def ONH1From (N : ℕ) : AdjoinRoot (Polynomial.X ^ N : Polynomial ℤ) →+* Cyclotomic.ONH1 N :=
  Ideal.Quotient.lift _ ((Cyclotomic.toONH1 N).comp rankOneEquiv.symm.toRingHom) fun p hp => by
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hp
    rw [RingHom.comp_apply, map_mul, map_mul, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      map_pow, ← rankOneEquiv_generator, RingEquiv.symm_apply_apply]
    have h0 : Cyclotomic.toONH1 N (generator 0 ^ N) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (TwoSidedIdeal.mem_asIdeal.mpr (TwoSidedIdeal.subset_span rfl))
    rw [h0, mul_zero]

def ONH1Equiv (N : ℕ) : Cyclotomic.ONH1 N ≃+* AdjoinRoot (Polynomial.X ^ N : Polynomial ℤ) :=
  RingEquiv.ofRingHom (ONH1To N) (ONH1From N)
    (Ideal.Quotient.ringHom_ext (RingHom.ext fun p => by
      change AdjoinRoot.mk _ (rankOneEquiv (rankOneEquiv.symm p)) = AdjoinRoot.mk _ p
      rw [RingEquiv.apply_symm_apply]))
    (Ideal.Quotient.ringHom_ext (RingHom.ext fun f => by
      change Cyclotomic.toONH1 N (rankOneEquiv.symm (rankOneEquiv f)) = Cyclotomic.toONH1 N f
      rw [RingEquiv.symm_apply_apply]))

/-- **EKL Prop 5.4**, `a = 1`: `OH_{1,N} ≅ ℤ[x]/(x^N)` is free on `1, x, …, x^{N-1}`. -/
def basis_OH_one (N : ℕ) : Basis (Fin N) ℤ (OH 1 N) :=
  let pb := AdjoinRoot.powerBasis' (Polynomial.monic_X_pow (R := ℤ) N)
  (pb.basis.map ((OH_one_equiv N).trans (ONH1Equiv N)).symm.toAddEquiv.toIntLinearEquiv).reindex
    (finCongr (by simp [pb, AdjoinRoot.powerBasis']))

theorem OH_one_equiv_trans_apply (N : ℕ) (i : ℕ) :
    ((OH_one_equiv N).trans (ONH1Equiv N)) (toOH 1 N (toOLamOne (generator 0 ^ i))) =
      AdjoinRoot.root _ ^ i := by
  change AdjoinRoot.mk _ (rankOneEquiv (generator 0 ^ i)) = _
  rw [map_pow, rankOneEquiv_generator, map_pow, AdjoinRoot.mk_X]

theorem basis_OH_one_apply (N : ℕ) (i : Fin N) :
    basis_OH_one N i = toOH 1 N (toOLamOne (generator 0 ^ i.val)) := by
  simp only [basis_OH_one, Basis.reindex_apply, Basis.map_apply, PowerBasis.coe_basis,
    AdjoinRoot.powerBasis'_gen]
  change ((OH_one_equiv N).trans (ONH1Equiv N)).symm _ = _
  rw [finCongr_symm_apply, Fin.coe_cast, ← OH_one_equiv_trans_apply, RingEquiv.symm_apply_apply]

theorem finrank_OH_one (N : ℕ) : Module.finrank ℤ (OH 1 N) = N.choose 1 := by
  rw [Module.finrank_eq_card_basis (basis_OH_one N), Fintype.card_fin, Nat.choose_one_right]

/-- `OH_{a,a} ≅ ℤ` for `a ≤ 1` (EKL p. 44; `Cyclotomic.OH_self_equiv` for `a ≥ 2`). -/
def OH_self_equiv_small : (a : ℕ) → a ≤ 1 → (OH a a ≃+* ℤ)
  | 0, _ => OH_zero_equiv 0
  | 1, _ => ((OH_one_equiv 1).trans (ONH1Equiv 1)).trans
      ((Ideal.quotEquivOfEq (by rw [pow_one, map_zero, sub_zero] :
        Ideal.span {(Polynomial.X ^ 1 : Polynomial ℤ)} =
          Ideal.span {Polynomial.X - Polynomial.C 0})).trans
        (Polynomial.quotientSpanXSubCAlgEquiv (0 : ℤ)).toRingEquiv)
  | _+2, h => absurd h (by omega)

end

end OddMath.Frontier.SmallRank
