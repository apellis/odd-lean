import OddMath.Frontier.EQLimaPartitions
import OddMath.Frontier.EQSkewDifferential

/-!
# Ellis–Qi, Proposition A.2: the cohomology of `OΛ` and `OΛ_n`

A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
Appendix A.1.3, Proposition A.2:

1. `H(OΛ)` is a free abelian group with basis `{s_λ : λ a Lima partition}`;
2. `H(OΛ_n)` is a free abelian group with basis `{s_λ : λ a Lima partition, ℓ(λ) ≤ n}`.

The input from the body of the paper is Proposition 3.11, `d(s_λ) = Σ_{μ = λ + □_i}
(-1)^{|λ/i| + i - 1} {ct(□_i)} s_μ`, where `{m}` is `1` for odd `m` and `0` for even `m`: the
differential of an untwisted odd Schur function adds one white box, with sign `schurSign`.

This file proves Proposition A.2 for any module with a basis indexed by partitions on which a
differential acts by such a formula (`schurHomologyBasis`, `prop_A_2_one`), and for the dg
algebra `OΛ_n = osym n` itself (`OddSchurData.prop_A_2_two`), assuming as explicit hypotheses
(`OddSchurData`) that the untwisted odd Schur polynomials of length `≤ n` form a `ℤ`-basis of
`OΛ_n` and satisfy Proposition 3.11.  These hypotheses are discharged for `n ≥ 2` in
`EQLimaOsym` (`oddSchurData`, `prop_A_2_two'`).

The proof follows the paper's urns-and-balls argument, with the hypercube decomposition replaced
by an explicit contracting homotopy (`BoxSystem.retraction`); the combinatorial identification
of the partitions without addable or removable white boxes with the Lima partitions is
`whiteSystem_crit_iff` / `whiteSystemLen_crit_iff`.  In addition to the basis statement we give
the concrete consequences: every cocycle is a coboundary plus a unique combination of Lima Schur
functions.

The paper works over a field `k`; the statements here are over an arbitrary commutative ring for
the abstract version and over `ℤ` for `OΛ_n`, as in the printed statement ("free abelian group").
Note that the paper's `OΛ` is the inverse limit of the `OΛ_n`; part (1) is stated for any module
with a partition-indexed basis and a differential given by Proposition 3.11.
-/

namespace OddMath.Frontier.EQLima

open Finset

/-! ### Transport of retractions -/

namespace Retraction

variable {k : Type*} [CommRing k] {M M' N : Type*} [AddCommGroup M] [Module k M]
  [AddCommGroup M'] [Module k M'] [AddCommGroup N] [Module k N]
  {D : M →ₗ[k] M}

/-- Transport a deformation retraction along a linear equivalence intertwining the
differentials. -/
def conj (r : Retraction D N) (e : M ≃ₗ[k] M') (D' : M' →ₗ[k] M')
    (hD : ∀ x, D' (e x) = e (D x)) : Retraction D' N where
  ι := e.toLinearMap ∘ₗ r.ι
  ρ := r.ρ ∘ₗ e.symm.toLinearMap
  h := e.toLinearMap ∘ₗ r.h ∘ₗ e.symm.toLinearMap
  ρ_comp_ι := LinearMap.ext fun n => by simp [r.ρ_ι]
  D_comp_ι := LinearMap.ext fun n => by simp [hD, r.D_ι]
  ρ_comp_D := LinearMap.ext fun x => by
    have := hD (e.symm x)
    simp only [LinearEquiv.apply_symm_apply] at this
    simp [this, r.ρ_D]
  homotopy := LinearMap.ext fun x => by
    have h1 := hD (r.h (e.symm x))
    have h2 := hD (e.symm x)
    simp only [LinearEquiv.apply_symm_apply] at h2
    have h3 := r.homotopy_apply (e.symm x)
    simp only [LinearMap.add_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, LinearMap.sub_apply, LinearMap.id_coe, id_eq]
    rw [h1, h2, LinearEquiv.symm_apply_apply, ← map_add, h3, map_sub,
      LinearEquiv.apply_symm_apply]

end Retraction

/-! ### Complexes with a basis indexed by shapes -/

section SchurType

variable {k : Type*} [CommRing k] {P B : Type*} [DecidableEq B] (S : BoxSystem P B)
  {M : Type*} [AddCommGroup M] [Module k M] (s : Module.Basis P k M) (c : P → B → kˣ)
  (D : M →ₗ[k] M)

/-- The differential acts on the basis by adding boxes (the shape of Proposition 3.11). -/
def ActsByBoxes : Prop :=
  ∀ p, D (s p) = ∑ b ∈ S.A p, ((c p b : kˣ) : k) • s (S.add p b)

variable {S s c D}

theorem actsByBoxes_intertwine (hD : ActsByBoxes S s c D) (x : P →₀ k) :
    D (s.repr.symm x) = s.repr.symm (S.delta c x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single p a =>
    rw [← mul_one a, ← smul_eq_mul, ← Finsupp.smul_single, map_smul, map_smul, map_smul,
      map_smul, Module.Basis.repr_symm_single_one, hD, BoxSystem.delta_single, map_sum]
    simp only [map_smul, Module.Basis.repr_symm_single_one]

theorem squareCond_of_actsByBoxes (hD : ActsByBoxes S s c D) (hDD : ∀ x, D (D x) = 0) :
    S.SquareCond c := by
  refine S.squareCond_of_delta_sq fun x => ?_
  apply s.repr.symm.injective
  rw [← actsByBoxes_intertwine hD, ← actsByBoxes_intertwine hD, hDD, map_zero]

/-- The deformation retraction of `(M, D)` onto the span of the critical shapes. -/
noncomputable def schurRetraction (hD : ActsByBoxes S s c D) (hc : S.SquareCond c) :
    Retraction D (S.critSet →₀ k) :=
  (S.retraction hc).conj s.repr.symm D (actsByBoxes_intertwine hD)

theorem schurRetraction_ι (hD : ActsByBoxes S s c D) (hc : S.SquareCond c) (p : S.critSet) :
    (schurRetraction hD hc).ι (Finsupp.single p 1) = s p := by
  simp [schurRetraction, Retraction.conj, BoxSystem.retraction, BoxSystem.critι_single]

theorem schur_crit_cocycle (hD : ActsByBoxes S s c D) {p : P} (hp : S.Crit p) : D (s p) = 0 := by
  rw [hD, ((S.crit_iff p).mp hp).1, Finset.sum_empty]

/-- **Cohomology with a Schur-type basis.** If `D` acts on the basis `s` by adding boxes with
unit coefficients and `D² = 0`, then `H(M, D)` is free with basis the classes of `s p` for the
critical shapes `p`. -/
noncomputable def schurHomologyBasis (hD : ActsByBoxes S s c D) (hc : S.SquareCond c) :
    Module.Basis S.critSet k (Homology D) :=
  Module.Basis.ofRepr (schurRetraction hD hc).homologyEquiv

theorem schurHomologyBasis_apply (hD : ActsByBoxes S s c D) (hc : S.SquareCond c)
    (p : S.critSet) :
    schurHomologyBasis hD hc p =
      Submodule.Quotient.mk ⟨s p, LinearMap.mem_ker.mpr (schur_crit_cocycle hD p.2)⟩ := by
  rw [schurHomologyBasis, Module.Basis.coe_ofRepr]
  change (schurRetraction hD hc).homologyEquiv.symm _ = _
  rw [Retraction.homologyEquiv_symm_apply]
  congr 1
  exact Subtype.ext (schurRetraction_ι hD hc p)

theorem schurRetraction_ι_eq (hD : ActsByBoxes S s c D) (hc : S.SquareCond c)
    (f : S.critSet →₀ k) :
    (schurRetraction hD hc).ι f = Finsupp.linearCombination k (fun p : S.critSet => s p) f := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single p a =>
    rw [← mul_one a, ← smul_eq_mul, ← Finsupp.smul_single, map_smul, map_smul,
      schurRetraction_ι, Finsupp.linearCombination_single, one_smul]

/-- Every cocycle is a coboundary plus a combination of the basis vectors of critical shape. -/
theorem schur_cocycle_eq (hD : ActsByBoxes S s c D) (hc : S.SquareCond c) {z : M}
    (hz : D z = 0) :
    ∃ y : M, ∃ f : S.critSet →₀ k,
      z = D y + Finsupp.linearCombination k (fun p : S.critSet => s p) f := by
  refine ⟨(schurRetraction hD hc).h z, (schurRetraction hD hc).ρ z, ?_⟩
  rw [← schurRetraction_ι_eq]
  exact (schurRetraction hD hc).cocycle_eq hz

/-- A combination of basis vectors of critical shape which is a coboundary is zero. -/
theorem schur_independent (hD : ActsByBoxes S s c D) (hc : S.SquareCond c)
    {f : S.critSet →₀ k} {y : M}
    (h : Finsupp.linearCombination k (fun p : S.critSet => s p) f = D y) : f = 0 :=
  (schurRetraction hD hc).eq_zero_of_ι_eq_D ((schurRetraction_ι_eq hD hc f).trans h)

end SchurType

/-! ### Proposition A.2 (1): `OΛ` -/

section PropA2One

variable {k : Type*} [CommRing k] {M : Type*} [AddCommGroup M] [Module k M]

/-- The critical shapes of the white-box system are the Lima partitions. -/
def whiteCritEquiv : whiteSystem.critSet ≃ {μ : YoungDiagram // IsLima μ} :=
  Equiv.subtypeEquivRight fun μ => whiteSystem_crit_iff μ

/-- **Proposition A.2 (1)** (Ellis–Qi).  Let `M` have a basis `s_λ` indexed by all partitions,
and let `D` act by Proposition 3.11:
`D(s_λ) = Σ_{μ = λ + □, □ white} (-1)^{|λ/i| + i - 1} s_μ`.  Then the cohomology `H(M, D)` is
free with basis `{[s_λ] : λ a Lima partition}`.  (The square-zero property is automatic for
these signs, `squareCond_schurSign`.) -/
noncomputable def prop_A_2_one (s : Module.Basis YoungDiagram k M) (D : M →ₗ[k] M)
    (hD : ∀ μ, D (s μ) =
      ∑ b ∈ addableCells IsWhite μ, ((schurSign μ b : kˣ) : k) • s (addCell μ b)) :
    Module.Basis {μ : YoungDiagram // IsLima μ} k (Homology D) :=
  (schurHomologyBasis (S := whiteSystem) (c := fun μ b => schurSign μ b) hD
    (squareCond_schurSign checker_white)).reindex whiteCritEquiv

theorem prop_A_2_one_apply (s : Module.Basis YoungDiagram k M) (D : M →ₗ[k] M)
    (hD : ∀ μ, D (s μ) =
      ∑ b ∈ addableCells IsWhite μ, ((schurSign μ b : kˣ) : k) • s (addCell μ b))
    (μ : {μ : YoungDiagram // IsLima μ}) :
    prop_A_2_one s D hD μ = Submodule.Quotient.mk ⟨s μ.1, LinearMap.mem_ker.mpr
      (schur_crit_cocycle (S := whiteSystem) (c := fun μ b => schurSign μ b) hD
        ((whiteSystem_crit_iff _).mpr μ.2))⟩ := by
  rw [prop_A_2_one, Module.Basis.reindex_apply, schurHomologyBasis_apply]
  rfl

/-- Proposition A.2 (1) for arbitrary unit coefficients: if `D` adds one white box with unit
coefficients and `D² = 0`, the cohomology is free on the classes of the Lima Schur functions. -/
noncomputable def prop_A_2_one_of_sq (s : Module.Basis YoungDiagram k M) (D : M →ₗ[k] M)
    (c : YoungDiagram → ℕ × ℕ → kˣ)
    (hD : ∀ μ, D (s μ) = ∑ b ∈ addableCells IsWhite μ, ((c μ b : kˣ) : k) • s (addCell μ b))
    (hDD : ∀ x, D (D x) = 0) :
    Module.Basis {μ : YoungDiagram // IsLima μ} k (Homology D) :=
  (schurHomologyBasis (S := whiteSystem) hD
    (squareCond_of_actsByBoxes (S := whiteSystem) hD hDD)).reindex whiteCritEquiv

end PropA2One

/-! ### Proposition A.2 (2): `OΛ_n` -/

section PropA2Two

open OddMath.SkewPolynomial (SkewPolynomial)
open OddMath.Frontier.EQSkewDifferential (osym d d_mem_osym)

/-- The differential of Ellis–Qi §3.1 restricted to `OΛ_n = osym n`, as a `ℤ`-linear map. -/
noncomputable def dOsym (n : ℕ) : osym n →ₗ[ℤ] osym n :=
  (AddMonoidHom.codRestrict ((d n).comp (osym n).subtype.toAddMonoidHom) (osym n)
    (fun x => d_mem_osym x.2)).toIntLinearMap

@[simp] theorem dOsym_coe (n : ℕ) (x : osym n) : (dOsym n x : SkewPolynomial n) = d n x := rfl

/-- The hypotheses under which Proposition A.2 (2) is derived: a family `s_λ` of untwisted odd
Schur polynomials whose members with `ℓ(λ) ≤ n` form a `ℤ`-basis of `OΛ_n`, and which satisfies
Proposition 3.11 (`s_μ` with `ℓ(μ) > n` does not occur, since it vanishes in `OΛ_n`). -/
structure OddSchurData (n : ℕ) where
  /-- the untwisted odd Schur polynomials -/
  s : YoungDiagram → SkewPolynomial n
  /-- the Schur polynomials of length `≤ n` form a `ℤ`-basis of `OΛ_n` -/
  basis : Module.Basis {μ : YoungDiagram // LengthLE n μ} ℤ (osym n)
  basis_apply : ∀ μ, (basis μ : SkewPolynomial n) = s μ.1
  /-- Proposition 3.11 in `OΛ_n` -/
  prop_3_11 : ∀ μ, LengthLE n μ →
    d n (s μ) = ∑ b ∈ addableCells (fun c => IsWhite c ∧ c.1 < n) μ,
      ((schurSign μ b : ℤˣ) : ℤ) • s (addCell μ b)

namespace OddSchurData

variable {n : ℕ} (H : OddSchurData n)

theorem whiteSystemLen_add_val {μ : {μ : YoungDiagram // LengthLE n μ}} {b : ℕ × ℕ}
    (hb : b ∈ (whiteSystemLen n).A μ) : ((whiteSystemLen n).add μ b).1 = addCell μ.1 b :=
  BoxSystem.restrict_add_val _ _ _ _ hb

theorem actsByBoxes :
    ActsByBoxes (whiteSystemLen n) H.basis (fun μ b => schurSign μ.1 b) (dOsym n) := by
  intro μ
  apply Subtype.ext
  rw [dOsym_coe, H.basis_apply, H.prop_3_11 μ.1 μ.2]
  simp only [AddSubmonoidClass.coe_finsetSum, AddSubgroupClass.coe_zsmul]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [H.basis_apply, whiteSystemLen_add_val hb]

omit H in
theorem squareCond :
    (whiteSystemLen n).SquareCond (k := ℤ) (fun μ b => schurSign μ.1 b) := by
  intro μ b b' hb hb' hne
  have := squareCond_schurSign (k := ℤ) (checker_white.and (fun c : ℕ × ℕ => c.1 < n))
    μ.1 b b' hb hb' hne
  simp only at this ⊢
  rw [whiteSystemLen_add_val hb, whiteSystemLen_add_val hb']
  exact this

/-- The critical shapes of `whiteSystemLen n` are the Lima partitions of length `≤ n`. -/
def critEquiv : (whiteSystemLen n).critSet ≃ {μ : YoungDiagram // IsLima μ ∧ LengthLE n μ} where
  toFun p := ⟨p.1.1, (whiteSystemLen_crit_iff p.1).mp p.2, p.1.2⟩
  invFun μ := ⟨⟨μ.1, μ.2.2⟩, (whiteSystemLen_crit_iff ⟨μ.1, μ.2.2⟩).mpr μ.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The Lima Schur polynomials are cocycles. -/
theorem lima_cocycle {μ : YoungDiagram} (hμ : IsLima μ) (hn : LengthLE n μ) : d n (H.s μ) = 0 := by
  have := schur_crit_cocycle H.actsByBoxes
    (p := ⟨μ, hn⟩) ((whiteSystemLen_crit_iff ⟨μ, hn⟩).mpr hμ)
  rw [← H.basis_apply ⟨μ, hn⟩, ← dOsym_coe, this]
  rfl

/-- **Proposition A.2 (2)** (Ellis–Qi).  The cohomology `H(OΛ_n)` is a free abelian group with
basis the classes of the Lima Schur polynomials `s_λ`, `λ` a Lima partition with `ℓ(λ) ≤ n`. -/
noncomputable def prop_A_2_two :
    Module.Basis {μ : YoungDiagram // IsLima μ ∧ LengthLE n μ} ℤ (Homology (dOsym n)) :=
  (schurHomologyBasis H.actsByBoxes (squareCond (n := n))).reindex critEquiv

theorem prop_A_2_two_apply (μ : {μ : YoungDiagram // IsLima μ ∧ LengthLE n μ}) :
    H.prop_A_2_two μ = Submodule.Quotient.mk ⟨H.basis ⟨μ.1, μ.2.2⟩, LinearMap.mem_ker.mpr
      (Subtype.ext (by rw [dOsym_coe, H.basis_apply]; exact H.lima_cocycle μ.2.1 μ.2.2))⟩ := by
  rw [prop_A_2_two, Module.Basis.reindex_apply, schurHomologyBasis_apply]
  rfl

theorem coe_linearCombination (a : (whiteSystemLen n).critSet →₀ ℤ) :
    ((Finsupp.linearCombination ℤ (fun p : (whiteSystemLen n).critSet => H.basis p) a : osym n) :
      SkewPolynomial n) = (a.mapDomain critEquiv).sum (fun μ z => z • H.s μ.1) := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [map_add, AddMemClass.coe_add, hf, hg, Finsupp.mapDomain_add,
      Finsupp.sum_add_index' (h := fun (μ : {μ : YoungDiagram // IsLima μ ∧ LengthLE n μ})
        (z : ℤ) => z • H.s μ.1) (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  | single p a =>
    rw [Finsupp.linearCombination_single, Finsupp.mapDomain_single,
      Finsupp.sum_single_index (h := fun (μ : {μ : YoungDiagram // IsLima μ ∧ LengthLE n μ})
        (z : ℤ) => z • H.s μ.1) (zero_smul _ _), AddSubgroupClass.coe_zsmul, H.basis_apply]
    rfl

/-- Proposition A.2 (2), concretely: every cocycle of `OΛ_n` is a coboundary plus a
`ℤ`-combination of Lima Schur polynomials. -/
theorem cocycle_eq {f : SkewPolynomial n} (hf : f ∈ osym n) (hdf : d n f = 0) :
    ∃ g ∈ osym n, ∃ a : {μ : YoungDiagram // IsLima μ ∧ LengthLE n μ} →₀ ℤ,
      f = d n g + a.sum (fun μ z => z • H.s μ.1) := by
  obtain ⟨y, a, hy⟩ := schur_cocycle_eq H.actsByBoxes (squareCond (n := n)) (z := ⟨f, hf⟩)
    (Subtype.ext (by rw [dOsym_coe]; exact hdf))
  refine ⟨y, y.2, a.mapDomain critEquiv, ?_⟩
  have := congrArg Subtype.val hy
  change f = _ at this
  rw [this, AddMemClass.coe_add, dOsym_coe, H.coe_linearCombination]

/-- Proposition A.2 (2), concretely: a `ℤ`-combination of Lima Schur polynomials which is a
coboundary in `OΛ_n` is zero, i.e. the Lima Schur polynomials are linearly independent in
cohomology. -/
theorem lima_independent (a : {μ : YoungDiagram // IsLima μ ∧ LengthLE n μ} →₀ ℤ)
    {g : SkewPolynomial n} (hg : g ∈ osym n) (h : a.sum (fun μ z => z • H.s μ.1) = d n g) :
    a = 0 := by
  have key := schur_independent H.actsByBoxes (squareCond (n := n))
    (f := a.mapDomain critEquiv.symm) (y := ⟨g, hg⟩) (Subtype.ext (by
      rw [dOsym_coe, ← h, H.coe_linearCombination, ← Finsupp.mapDomain_comp,
        Equiv.self_comp_symm, Finsupp.mapDomain_id]))
  have := congrArg (Finsupp.mapDomain critEquiv) key
  rwa [Finsupp.mapDomain_zero, ← Finsupp.mapDomain_comp, Equiv.self_comp_symm,
    Finsupp.mapDomain_id] at this

end OddSchurData

end PropA2Two

end OddMath.Frontier.EQLima
