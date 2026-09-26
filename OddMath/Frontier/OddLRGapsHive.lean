import OddMath.Frontier.OddLRHiveTableau
import OddMath.Frontier.OddLRMisc
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Littlewood–Richardson triangles and hives: cones, polytopes and the form `N(μ) + N(λ)`

Ellis, "The odd Littlewood–Richardson rule", arXiv:1111.3932v1 ("E"), §4.3, pp. 16–19, on the
library's `OddLRHive.IsLRTriangle`, `OddLRHive.triangles`, `OddLRHive.IsHive`, `OddLRHive.hives`
(Definition 4.11 with the corrected condition (3), and Definition 4.14).

* Definition 4.11, p. 16: "Note that `a_{0,j} < 0` and `a_{j,j} < 0` are both possible"
  (`lrTriangle_neg_int`, `lrTriangle_neg_real`: an LR triangle with `a_{0,1} = a_{1,1} = -1`).
* p. 16: "Let `△_LR` denote the set of all Littlewood–Richardson triangles, a cone in `V`"
  (`lrCone`); p. 18: "Let `H` be the set of all hives; this is a cone in `V`" (`hiveCone`).
* p. 16: "Each set `△_LR(λ, μ, ν)` is a convex polytope in `V`" (`triangles_isPolytope`);
  p. 18: "Each `H(λ, μ, ν)` is a convex polytope in `V`" (`hives_isPolytope`). A polytope is a
  bounded intersection of finitely many closed half-spaces `{x : f x ≤ c}` (`IsPolytope`); it is
  convex (`IsPolyhedron.convex`) and closed (`IsPolyhedron.isClosed`). Here `V = ℝ^{C(n+2,2)}`
  and `λ, μ, ν` are arbitrary real sequences.
* p. 19: "The quantity `N(μ) + N(λ)` can also be expressed as a quadratic form in either the
  variables `(a_{i,j})` or the variables `(h_{i,j})`": the quadratic forms `NFormT`, `NFormH`
  (`N(κ) = Σ_i κ_i Σ_{k<i} κ_k`, `OddLRMisc.north_eq_rows`, with `μ_j, λ_j` the linear
  coordinates `muT, lamT`, resp. `muH, lamH`) satisfy `NFormT A = N(μ) + N(λ)` on
  `△_LR(λ, μ, ν)` (`NFormT_eq`) and `NFormH H = N(μ) + N(λ)` on `H(λ, μ, ν)` (`NFormH_eq`), for
  partitions with at most `n` parts; and `NFormH ∘ Φ = NFormT` (`NFormH_phi`).
-/

noncomputable section
open scoped BigOperators
open Finset

namespace OddMath.Frontier.OddLRGaps

open OddLRHive

/-! ## Negative entries (Definition 4.11) -/

/-- The triangle `a_{0,0} = 0`, `a_{0,1} = a_{1,1} = -1` (`n = 1`). -/
def negTri (R : Type*) [CommRing R] : V R 1 := fun x => if x.j = 0 then 0 else -1

theorem coord_negTri (R : Type*) [CommRing R] (i j : ℕ) (hij : i ≤ j) (hj : j ≤ 1) :
    coord (negTri R) i j = if j = 0 then 0 else -1 := by
  rw [coord_mk _ hij hj]
  rfl

theorem negTri_isLR (R : Type*) [CommRing R] [PartialOrder R] : IsLRTriangle (negTri R) where
  zero := by rw [coord_negTri R 0 0 le_rfl zero_le_one, if_pos rfl]
  nonneg := fun i j h1 h2 h3 => by omega
  column := fun i j h1 h2 h3 => by omega
  lattice := fun i j h1 h2 h3 => by omega

theorem coord_negTri_01 (R : Type*) [CommRing R] : coord (negTri R) 0 1 = -1 := by
  rw [coord_negTri R 0 1 zero_le_one le_rfl, if_neg one_ne_zero]

theorem coord_negTri_11 (R : Type*) [CommRing R] : coord (negTri R) 1 1 = -1 := by
  rw [coord_negTri R 1 1 le_rfl le_rfl, if_neg one_ne_zero]

/-- E Definition 4.11: an integral LR triangle with `a_{0,j} < 0` and `a_{j,j} < 0`. -/
theorem lrTriangle_neg_int :
    ∃ A : V ℤ 1, IsLRTriangle A ∧ coord A 0 1 < 0 ∧ coord A 1 1 < 0 :=
  ⟨negTri ℤ, negTri_isLR ℤ, by rw [coord_negTri_01]; norm_num,
    by rw [coord_negTri_11]; norm_num⟩

/-- E Definition 4.11: a real LR triangle with `a_{0,j} < 0` and `a_{j,j} < 0`. -/
theorem lrTriangle_neg_real :
    ∃ A : V ℝ 1, IsLRTriangle A ∧ coord A 0 1 < 0 ∧ coord A 1 1 < 0 :=
  ⟨negTri ℝ, negTri_isLR ℝ, by rw [coord_negTri_01]; norm_num,
    by rw [coord_negTri_11]; norm_num⟩

/-! ## Finite intersections of half-spaces -/

section cut
open scoped Classical
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The intersection of the half-spaces `{x : f x ≤ c}`, `(f, c) ∈ K`. -/
def cut (K : Finset ((E →ₗ[ℝ] ℝ) × ℝ)) : Set E := {x | ∀ p ∈ K, p.1 x ≤ p.2}

/-- A finite intersection of closed half-spaces. -/
def IsPolyhedron (s : Set E) : Prop := ∃ K : Finset ((E →ₗ[ℝ] ℝ) × ℝ), s = cut K

/-- A convex polytope: a bounded finite intersection of closed half-spaces. -/
def IsPolytope [PseudoMetricSpace E] (s : Set E) : Prop := IsPolyhedron s ∧ Bornology.IsBounded s

theorem mem_cut {K : Finset ((E →ₗ[ℝ] ℝ) × ℝ)} {x : E} : x ∈ cut K ↔ ∀ p ∈ K, p.1 x ≤ p.2 :=
  Iff.rfl

theorem mem_cut_union {K K' : Finset ((E →ₗ[ℝ] ℝ) × ℝ)} {x : E} :
    x ∈ cut (K ∪ K') ↔ x ∈ cut K ∧ x ∈ cut K' := by
  simp only [mem_cut, Finset.mem_union]
  constructor
  · intro h; exact ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩
  · rintro ⟨h1, h2⟩ p (hp | hp)
    · exact h1 p hp
    · exact h2 p hp

theorem mem_cut_biUnion {ι : Type*} (I : Finset ι) (K : ι → Finset ((E →ₗ[ℝ] ℝ) × ℝ)) {x : E} :
    x ∈ cut (I.biUnion K) ↔ ∀ i ∈ I, x ∈ cut (K i) := by
  simp only [mem_cut, Finset.mem_biUnion]
  constructor
  · intro h i hi p hp; exact h p ⟨i, hi, hp⟩
  · rintro h p ⟨i, hi, hp⟩; exact h i hi p hp

theorem mem_cut_single {f : E →ₗ[ℝ] ℝ} {c : ℝ} {x : E} : x ∈ cut {(f, c)} ↔ f x ≤ c := by
  simp [mem_cut]

/-- The hyperplane `f = c` as two half-spaces. -/
def eqCut (f : E →ₗ[ℝ] ℝ) (c : ℝ) : Finset ((E →ₗ[ℝ] ℝ) × ℝ) := {(f, c), (-f, -c)}

theorem mem_cut_eqCut {f : E →ₗ[ℝ] ℝ} {c : ℝ} {x : E} : x ∈ cut (eqCut f c) ↔ f x = c := by
  simp only [eqCut, mem_cut, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp,
    forall_eq, LinearMap.neg_apply, neg_le_neg_iff]
  exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

theorem preimage_cut {F : Type*} [AddCommGroup F] [Module ℝ F] (g : F →ₗ[ℝ] E)
    (K : Finset ((E →ₗ[ℝ] ℝ) × ℝ)) :
    g ⁻¹' cut K = cut (K.image fun p => (p.1.comp g, p.2)) := by
  ext x
  simp only [Set.mem_preimage, mem_cut, Finset.forall_mem_image, LinearMap.comp_apply]

theorem IsPolyhedron.convex {s : Set E} (hs : IsPolyhedron s) : Convex ℝ s := by
  obtain ⟨K, rfl⟩ := hs
  have : cut K = ⋂ p ∈ K, {x : E | p.1 x ≤ p.2} := by
    ext x; simp [mem_cut]
  rw [this]
  exact convex_iInter₂ fun p _ => convex_halfSpace_le p.1.isLinear p.2

theorem IsPolyhedron.isClosed [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [T2Space E] [FiniteDimensional ℝ E] {s : Set E} (hs : IsPolyhedron s) : IsClosed s := by
  obtain ⟨K, rfl⟩ := hs
  have : cut K = ⋂ p ∈ K, {x : E | p.1 x ≤ p.2} := by
    ext x; simp [mem_cut]
  rw [this]
  exact isClosed_biInter fun p _ =>
    isClosed_le (LinearMap.continuous_of_finiteDimensional p.1) continuous_const

/-- A finite intersection of half-spaces through `0` is a convex cone. -/
def cutCone (K : Finset ((E →ₗ[ℝ] ℝ) × ℝ)) (hK : ∀ p ∈ K, p.2 = 0) : ConvexCone ℝ E where
  carrier := cut K
  smul_mem' c hc x hx p hp := by
    rw [map_smul, smul_eq_mul, hK p hp]
    exact mul_nonpos_of_nonneg_of_nonpos hc.le (hK p hp ▸ hx p hp)
  add_mem' x hx y hy p hp := by
    rw [map_add, hK p hp]
    have := hx p hp; have := hy p hp
    rw [hK p hp] at *
    linarith

end cut

/-! ## The linear conditions of Definitions 4.11 and 4.14 -/

variable {n : ℕ}

/-- The coordinate `a_{i,j}` (zero outside `0 ≤ i ≤ j ≤ n`) as a linear functional. -/
def coordL (R : Type*) [CommRing R] (n : ℕ) (i j : ℕ) : V R n →ₗ[R] R :=
  if h : i ≤ j ∧ j ≤ n then LinearMap.proj (Idx.mk i j h.1 h.2) else 0

theorem coordL_apply {R : Type*} [CommRing R] (i j : ℕ) (A : V R n) :
    coordL R n i j A = coord A i j := by
  unfold coordL coord
  split_ifs <;> rfl

theorem coord_add {R : Type*} [CommRing R] (A B : V R n) (i j : ℕ) :
    coord (A + B) i j = coord A i j + coord B i j := by
  simp only [← coordL_apply, map_add]

section real
open scoped Classical

/-- Indices `(i, j)` with `i, j ≤ n` satisfying `P`. -/
def idxSet (n : ℕ) (P : ℕ → ℕ → Prop) : Finset (ℕ × ℕ) :=
  (range (n+1) ×ˢ range (n+1)).filter fun p => P p.1 p.2

theorem mem_idxSet {P : ℕ → ℕ → Prop} {p : ℕ × ℕ} :
    p ∈ idxSet n P ↔ p.1 ≤ n ∧ p.2 ≤ n ∧ P p.1 p.2 := by
  simp only [idxSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff,
    and_assoc]

/-- Condition (2) of Definition 4.11 as a functional `≤ 0`. -/
def colL (n i j : ℕ) : V ℝ n →ₗ[ℝ] ℝ :=
  ∑ p ∈ range (i+1), coordL ℝ n p (j+1) - ∑ p ∈ range i, coordL ℝ n p j

/-- Condition (3) of Definition 4.11 (corrected range) as a functional `≤ 0`. -/
def latL (n i j : ℕ) : V ℝ n →ₗ[ℝ] ℝ :=
  ∑ q ∈ Icc (i+1) (j+1), coordL ℝ n (i+1) q - ∑ q ∈ Icc i j, coordL ℝ n i q

/-- The half-spaces cutting out `△_LR` (all through `0`). -/
def lrK (n : ℕ) : Finset ((V ℝ n →ₗ[ℝ] ℝ) × ℝ) :=
  eqCut (coordL ℝ n 0 0) 0 ∪
    (idxSet n (fun i j => 1 ≤ i ∧ i < j)).biUnion (fun p => {(-coordL ℝ n p.1 p.2, 0)}) ∪
    (idxSet n (fun i j => 1 ≤ i ∧ i ≤ j ∧ j < n)).biUnion (fun p => {(colL n p.1 p.2, 0)}) ∪
    (idxSet n (fun i j => 1 ≤ i ∧ i ≤ j ∧ j < n)).biUnion (fun p => {(latL n p.1 p.2, 0)})

theorem lrK_zero : ∀ p ∈ lrK n, p.2 = 0 := by
  intro p hp
  simp only [lrK, eqCut, Finset.mem_union, Finset.mem_biUnion, Finset.mem_insert,
    Finset.mem_singleton] at hp
  rcases hp with ((((rfl | rfl) | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) <;> simp

theorem mem_cut_lrK (A : V ℝ n) : A ∈ cut (lrK n) ↔ IsLRTriangle A := by
  simp only [lrK, mem_cut_union, mem_cut_eqCut, mem_cut_biUnion, mem_cut_single, mem_idxSet,
    coordL_apply, LinearMap.neg_apply, neg_nonpos, colL, latL, LinearMap.sub_apply,
    LinearMap.coeFn_sum, Finset.sum_apply, sub_nonpos, and_imp, Prod.forall]
  constructor
  · rintro ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩
    exact ⟨h0, fun i j hi hij hj => h1 i j (by omega) hj hi hij,
      fun i j hi hij hj => h2 i j (by omega) (by omega) hi hij hj,
      fun i j hi hij hj => h3 i j (by omega) (by omega) hi hij hj⟩
  · intro hA
    exact ⟨⟨⟨hA.zero, fun i j _ hj hi hij => hA.nonneg i j hi hij hj⟩,
      fun i j _ _ hi hij hj => hA.column i j hi hij hj⟩,
      fun i j _ _ hi hij hj => hA.lattice i j hi hij hj⟩

/-- `λ_j`, `ν_j` as functionals. -/
def lamL (n j : ℕ) : V ℝ n →ₗ[ℝ] ℝ := ∑ p ∈ range (j+1), coordL ℝ n p j
def nuL (n j : ℕ) : V ℝ n →ₗ[ℝ] ℝ := ∑ q ∈ Icc j n, coordL ℝ n j q

/-- The hyperplanes fixing `λ, μ, ν`. -/
def shapeK (n : ℕ) (lam mu nu : ℕ → ℝ) : Finset ((V ℝ n →ₗ[ℝ] ℝ) × ℝ) :=
  (Icc 1 n).biUnion fun j =>
    eqCut (lamL n j) (lam j) ∪ eqCut (coordL ℝ n 0 j) (mu j) ∪ eqCut (nuL n j) (nu j)

theorem mem_cut_shapeK (lam mu nu : ℕ → ℝ) (A : V ℝ n) :
    A ∈ cut (shapeK n lam mu nu) ↔
      ∀ j, 1 ≤ j → j ≤ n → lamT A j = lam j ∧ muT A j = mu j ∧ nuT A j = nu j := by
  simp only [shapeK, mem_cut_biUnion, mem_cut_union, mem_cut_eqCut, Finset.mem_Icc, lamL, nuL,
    LinearMap.coeFn_sum, Finset.sum_apply, coordL_apply, lamT, muT, nuT, and_imp, and_assoc]

theorem triangles_eq_cut (lam mu nu : ℕ → ℝ) :
    triangles n lam mu nu = cut (lrK n ∪ shapeK n lam mu nu) := by
  ext A
  rw [mem_cut_union, mem_cut_lrK, mem_cut_shapeK]
  rfl

/-! ## Cones -/

/-- E §4.3, p. 16: `△_LR` is a convex cone in `V`. -/
def lrCone (n : ℕ) : ConvexCone ℝ (V ℝ n) := cutCone (lrK n) lrK_zero

theorem mem_lrCone (A : V ℝ n) : A ∈ lrCone n ↔ IsLRTriangle A := mem_cut_lrK A

theorem lrCone_pointed : (0 : V ℝ n) ∈ lrCone n := fun p hp => by
  rw [map_zero, lrK_zero p hp]

theorem isHive_iff (H : V ℝ n) : IsHive H ↔ IsLRTriangle ((phiEquiv ℝ n).symm H) := by
  rw [← isHive_phi_iff, ← phiEquiv_apply, LinearEquiv.apply_symm_apply]

/-- E §4.3, p. 18: the hives form a convex cone in `V`. -/
def hiveCone (n : ℕ) : ConvexCone ℝ (V ℝ n) :=
  (lrCone n).comap (phiEquiv ℝ n).symm.toLinearMap

theorem mem_hiveCone (H : V ℝ n) : H ∈ hiveCone n ↔ IsHive H := by
  rw [isHive_iff, ← mem_lrCone]
  rfl

theorem hiveCone_pointed : (0 : V ℝ n) ∈ hiveCone n := by
  rw [mem_hiveCone, isHive_iff, map_zero, ← mem_lrCone]
  exact lrCone_pointed

/-! ## Boundedness -/

section bounds
variable {lam mu nu : ℕ → ℝ} {A : V ℝ n}

theorem diag_ge (hA : A ∈ triangles n lam mu nu) :
    ∀ d i, n = i + d → 1 ≤ i → nu n ≤ coord A i i
  | 0, i, hd, hi => by
    obtain rfl : i = n := by omega
    have := (hA.2 i hi le_rfl).2.2
    rw [nuT, Finset.Icc_self, Finset.sum_singleton] at this
    rw [this]
  | d+1, i, hd, hi => by
    have h1 := diag_ge hA d (i+1) (by omega) (by omega)
    have h2 := hA.1.lattice i i hi le_rfl (by omega)
    rw [Finset.Icc_self, Finset.sum_singleton, Finset.Icc_self, Finset.sum_singleton] at h2
    linarith

theorem row_split (i : ℕ) (hi : i ≤ n) :
    nuT A i = coord A i i + ∑ q ∈ Ioc i n, coord A i q := by
  rw [nuT, Finset.Icc_eq_cons_Ioc hi, Finset.sum_cons]

theorem off_nonneg (hA : A ∈ triangles n lam mu nu) {i q : ℕ} (hi : 1 ≤ i) (hq : q ∈ Ioc i n) :
    0 ≤ coord A i q := by
  rw [Finset.mem_Ioc] at hq
  exact hA.1.nonneg i q hi hq.1 hq.2

theorem coord_bound (hA : A ∈ triangles n lam mu nu) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) :
    |coord A i j| ≤ |mu j| + |nu i| + |nu n| := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [hA.1.zero, abs_zero]; positivity
    · have := (hA.2 j hj0 hj).2.1
      rw [muT] at this
      rw [this]
      have := abs_nonneg (nu 0); have := abs_nonneg (nu n); linarith
  have hnu := (hA.2 i hi (hij.trans hj)).2.2
  rw [row_split i (hij.trans hj)] at hnu
  have hsum : 0 ≤ ∑ q ∈ Ioc i n, coord A i q :=
    Finset.sum_nonneg fun q hq => off_nonneg hA hi hq
  have hdiag := diag_ge hA (n - i) i (by omega) hi
  have hmu := abs_nonneg (mu j)
  rcases eq_or_lt_of_le hij with rfl | hlt
  · rw [abs_le]
    constructor
    · have := neg_abs_le (nu n); have := abs_nonneg (nu i); linarith
    · have := le_abs_self (nu i); have := abs_nonneg (nu n); linarith
  · have hq : j ∈ Ioc i n := Finset.mem_Ioc.mpr ⟨hlt, hj⟩
    have h0 := off_nonneg hA hi hq
    have hle : coord A i j ≤ ∑ q ∈ Ioc i n, coord A i q :=
      Finset.single_le_sum (fun q hq => off_nonneg hA hi hq) hq
    rw [abs_of_nonneg h0]
    have := le_abs_self (nu i); have := neg_abs_le (nu n)
    linarith

end bounds

/-- The coordinates of every point of `△_LR(λ, μ, ν)` are bounded. -/
theorem triangles_isBounded (lam mu nu : ℕ → ℝ) : Bornology.IsBounded (triangles n lam mu nu) := by
  set M := ∑ k ∈ range (n+1), (|mu k| + |nu k|) + |nu n| with hM
  have hM0 : 0 ≤ M := by positivity
  refine (Metric.isBounded_closedBall (x := (0 : V ℝ n)) (r := M)).subset ?_
  intro A hA
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hM0]
  intro x
  rw [← coord_idx A x, Real.norm_eq_abs]
  refine (coord_bound hA x.i_le_j x.j_le).trans ?_
  have hj : x.j ∈ range (n+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le x.j_le)
  have hi : x.i ∈ range (n+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le (x.i_le_j.trans x.j_le))
  have h1 : |mu x.j| ≤ ∑ k ∈ range (n+1), |mu k| :=
    Finset.single_le_sum (f := fun k => |mu k|) (fun _ _ => abs_nonneg _) hj
  have h2 : |nu x.i| ≤ ∑ k ∈ range (n+1), |nu k| :=
    Finset.single_le_sum (f := fun k => |nu k|) (fun _ _ => abs_nonneg _) hi
  rw [hM, Finset.sum_add_distrib]
  linarith

/-! ## Polytopes -/

/-- E §4.3, p. 16: `△_LR(λ, μ, ν)` is a convex polytope in `V`. -/
theorem triangles_isPolytope (lam mu nu : ℕ → ℝ) : IsPolytope (triangles n lam mu nu) :=
  ⟨⟨_, triangles_eq_cut lam mu nu⟩, triangles_isBounded lam mu nu⟩

theorem hives_eq_preimage (lam mu nu : ℕ → ℝ) :
    hives n lam mu nu = (phiEquiv ℝ n).symm ⁻¹' triangles n lam mu nu := by
  rw [← (phi_bijOn (n := n) lam mu nu).image_eq, ← LinearEquiv.image_eq_preimage]
  rfl

/-- E §4.3, p. 18: `H(λ, μ, ν)` is a convex polytope in `V`. -/
theorem hives_isPolytope (lam mu nu : ℕ → ℝ) : IsPolytope (hives n lam mu nu) := by
  refine ⟨⟨(lrK n ∪ shapeK n lam mu nu).image
      fun p => (p.1.comp (phiEquiv ℝ n).symm.toLinearMap, p.2), ?_⟩, ?_⟩
  · rw [hives_eq_preimage, triangles_eq_cut, ← LinearEquiv.coe_toLinearMap, preimage_cut]
  · rw [← (phi_bijOn (n := n) lam mu nu).image_eq]
    exact (LinearMap.toContinuousLinearMap (phi ℝ n)).lipschitz.isBounded_image
      (triangles_isBounded lam mu nu)

theorem triangles_convex (lam mu nu : ℕ → ℝ) : Convex ℝ (triangles n lam mu nu) :=
  (triangles_isPolytope lam mu nu).1.convex

theorem hives_convex (lam mu nu : ℕ → ℝ) : Convex ℝ (hives n lam mu nu) :=
  (hives_isPolytope lam mu nu).1.convex

end real

/-! ## `N(μ) + N(λ)` as a quadratic form -/

section forms
variable (R : Type*) [CommRing R]

/-- `μ_j = a_{0,j}` as a linear functional. -/
def muTL (n j : ℕ) : V R n →ₗ[R] R := coordL R n 0 j

/-- `λ_j = Σ_{p ≤ j} a_{p,j}` as a linear functional. -/
def lamTL (n j : ℕ) : V R n →ₗ[R] R := ∑ p ∈ range (j+1), coordL R n p j

/-- `μ_j = h_{0,j} - h_{0,j-1}` as a linear functional. -/
def muHL (n j : ℕ) : V R n →ₗ[R] R := coordL R n 0 j - coordL R n 0 (j-1)

/-- `λ_j = h_{j,j} - h_{j-1,j-1}` as a linear functional. -/
def lamHL (n j : ℕ) : V R n →ₗ[R] R := coordL R n j j - coordL R n (j-1) (j-1)

/-- The bilinear form `(X, Y) ↦ Σ_{1 ≤ k < j ≤ n} (m_j(X) m_k(Y) + l_j(X) l_k(Y))`. -/
def NBil (n : ℕ) (m l : ℕ → V R n →ₗ[R] R) : LinearMap.BilinForm R (V R n) :=
  ∑ j ∈ Icc 1 n, ∑ k ∈ Ico 1 j,
    ((LinearMap.mul R R).compl₁₂ (m j) (m k) + (LinearMap.mul R R).compl₁₂ (l j) (l k))

theorem NBil_apply (n : ℕ) (m l : ℕ → V R n →ₗ[R] R) (X : V R n) :
    NBil R n m l X X = ∑ j ∈ Icc 1 n, (m j X * ∑ k ∈ Ico 1 j, m k X + l j X * ∑ k ∈ Ico 1 j, l k X) := by
  simp only [NBil, LinearMap.coeFn_sum, Finset.sum_apply, LinearMap.add_apply,
    LinearMap.compl₁₂_apply, LinearMap.mul_apply', Finset.mul_sum, Finset.sum_add_distrib]

/-- E §4.3, p. 19: `N(μ) + N(λ)` as a quadratic form in the triangle coordinates `a_{i,j}`. -/
def NFormT (n : ℕ) : QuadraticForm R (V R n) :=
  (NBil R n (muTL R n) (lamTL R n)).toQuadraticMap

/-- E §4.3, p. 19: `N(μ) + N(λ)` as a quadratic form in the hive coordinates `h_{i,j}`. -/
def NFormH (n : ℕ) : QuadraticForm R (V R n) :=
  (NBil R n (muHL R n) (lamHL R n)).toQuadraticMap

theorem muTL_apply (j : ℕ) (A : V R n) : muTL R n j A = muT A j := coordL_apply 0 j A

theorem lamTL_apply (j : ℕ) (A : V R n) : lamTL R n j A = lamT A j := by
  simp [lamTL, lamT, coordL_apply]

theorem muHL_apply (j : ℕ) (H : V R n) : muHL R n j H = muH H j := by
  simp [muHL, muH, coordL_apply]

theorem lamHL_apply (j : ℕ) (H : V R n) : lamHL R n j H = lamH H j := by
  simp [lamHL, lamH, coordL_apply]

theorem NFormT_apply (A : V R n) :
    NFormT R n A = ∑ j ∈ Icc 1 n,
      (muT A j * ∑ k ∈ Ico 1 j, muT A k + lamT A j * ∑ k ∈ Ico 1 j, lamT A k) := by
  rw [NFormT, LinearMap.BilinMap.toQuadraticMap_apply, NBil_apply]
  simp only [muTL_apply, lamTL_apply]

theorem NFormH_apply (H : V R n) :
    NFormH R n H = ∑ j ∈ Icc 1 n,
      (muH H j * ∑ k ∈ Ico 1 j, muH H k + lamH H j * ∑ k ∈ Ico 1 j, lamH H k) := by
  rw [NFormH, LinearMap.BilinMap.toQuadraticMap_apply, NBil_apply]
  simp only [muHL_apply, lamHL_apply]

/-- `Q_N^𝔥 ∘ Φ = Q_N^△`. -/
theorem NFormH_phi (A : V R n) : NFormH R n (phi R n A) = NFormT R n A := by
  rw [NFormH_apply, NFormT_apply]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_Icc] at hj
  have hk' : ∀ k ∈ Ico 1 j, muH (phi R n A) k = muT A k ∧ lamH (phi R n A) k = lamT A k := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    exact ⟨muH_phi A hk.1 (by omega), lamH_phi A hk.1 (by omega)⟩
  rw [muH_phi A hj.1 hj.2, lamH_phi A hj.1 hj.2, Finset.sum_congr rfl fun k hk => (hk' k hk).1,
    Finset.sum_congr rfl fun k hk => (hk' k hk).2]

end forms

/-- `Σ_{j=1}^{n} κ_j Σ_{k=1}^{j-1} κ_k = N(κ)` for a partition `κ` with at most `n` parts. -/
theorem north_eq_sum (κ : YoungDiagram) (hκ : κ.colLen 0 ≤ n) :
    (TableauStripSigns.north κ : ℤ) =
      ∑ j ∈ Icc 1 n, OddLRHive.part κ j * ∑ k ∈ Ico 1 j, OddLRHive.part κ k := by
  rw [OddLRMisc.north_eq_rows]
  push_cast
  have hshift : ∀ (g : ℕ → ℤ) (m : ℕ), ∑ j ∈ Icc 1 m, g j = ∑ i ∈ range m, g (i+1) :=
    fun g m => sum_Icc_one g m
  have hshift' : ∀ (g : ℕ → ℤ) (m : ℕ), ∑ j ∈ Ico 1 m, g j = ∑ i ∈ range (m - 1), g (i+1) := by
    intro g m
    rcases m with _ | m
    · simp
    · rw [Nat.add_sub_cancel, ← hshift g m]
      rfl
  rw [hshift]
  simp only [OddLRHive.part, Nat.add_sub_cancel, hshift', Nat.add_sub_cancel]
  apply Finset.sum_subset
  · intro i hi
    rw [Finset.mem_range] at hi ⊢
    omega
  · intro i _ hi
    rw [Finset.mem_range, not_lt] at hi
    rw [OddLRHive.rowLen_eq_zero_of_le (by omega)]
    simp

/-- E §4.3, p. 19: on `△_LR(λ, μ, ν) ∩ V_ℤ`, `N(μ) + N(λ)` is the quadratic form `NFormT`. -/
theorem NFormT_eq {lam mu nu : YoungDiagram} (hl : lam.colLen 0 ≤ n) (hm : mu.colLen 0 ≤ n)
    {A : V ℤ n} (hA : A ∈ triangles n (part lam) (part mu) (part nu)) :
    NFormT ℤ n A = (TableauStripSigns.north mu + TableauStripSigns.north lam : ℤ) := by
  have hj : ∀ j, 1 ≤ j → j ≤ n → muT A j = part mu j ∧ lamT A j = part lam j :=
    fun j h1 h2 => ⟨(hA.2 j h1 h2).2.1, (hA.2 j h1 h2).1⟩
  rw [NFormT_apply, north_eq_sum mu hm, north_eq_sum lam hl, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj' => ?_
  rw [Finset.mem_Icc] at hj'
  rw [(hj j hj'.1 hj'.2).1, (hj j hj'.1 hj'.2).2,
    Finset.sum_congr rfl fun k hk => (hj k (Finset.mem_Ico.mp hk).1
      (by have := Finset.mem_Ico.mp hk; omega)).1,
    Finset.sum_congr rfl fun k hk => (hj k (Finset.mem_Ico.mp hk).1
      (by have := Finset.mem_Ico.mp hk; omega)).2]

/-- E §4.3, p. 19: on `H(λ, μ, ν) ∩ V_ℤ`, `N(μ) + N(λ)` is the quadratic form `NFormH`. -/
theorem NFormH_eq {lam mu nu : YoungDiagram} (hl : lam.colLen 0 ≤ n) (hm : mu.colLen 0 ≤ n)
    {H : V ℤ n} (hH : H ∈ hives n (part lam) (part mu) (part nu)) :
    NFormH ℤ n H = (TableauStripSigns.north mu + TableauStripSigns.north lam : ℤ) := by
  have hj : ∀ j, 1 ≤ j → j ≤ n → muH H j = part mu j ∧ lamH H j = part lam j :=
    fun j h1 h2 => ⟨(hH.2 j h1 h2).2.1, (hH.2 j h1 h2).1⟩
  rw [NFormH_apply, north_eq_sum mu hm, north_eq_sum lam hl, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj' => ?_
  rw [Finset.mem_Icc] at hj'
  rw [(hj j hj'.1 hj'.2).1, (hj j hj'.1 hj'.2).2,
    Finset.sum_congr rfl fun k hk => (hj k (Finset.mem_Ico.mp hk).1
      (by have := Finset.mem_Ico.mp hk; omega)).1,
    Finset.sum_congr rfl fun k hk => (hj k (Finset.mem_Ico.mp hk).1
      (by have := Finset.mem_Ico.mp hk; omega)).2]

end OddMath.Frontier.OddLRGaps
