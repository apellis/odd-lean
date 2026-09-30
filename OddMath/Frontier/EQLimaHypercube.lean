import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination

/-!
# Ellis–Qi, Appendix A.1.1: hypercube complexes and complexes of boxes

A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
Appendix A.1.  The cohomology of `OΛ` and `OΛ_n` (Proposition A.2) is computed there by
decomposing the complex spanned by odd Schur functions into *hypercube complexes*
(Subsection A.1.1): `Y_k` has basis `v_ε`, `ε ∈ {0,1}^k` ("`k` urns, each holding zero or one
ball"), and `d(v_ε) = Σ_{|η| = 1 + |ε|} ± v_η` is a signed sum over the ways of adding one ball.
The paper records that `Y_k` is contractible for `k ≥ 1`.

This file isolates the homological algebra, independently of polynomials.

* `BoxSystem P B`: a set `P` of "shapes", each with a finite set of cells in `B`, a finite set
  `A p` of addable boxes and a finite set `R p` of removable boxes, with the exchange properties
  of Lemma A.1 of the paper (adding an addable box removes it from the addable set and makes it
  removable, and creates no other addable or removable box).
* `BoxSystem.delta S c`: the complex `P →₀ k` with differential
  `δ(p) = Σ_{b ∈ A p} c p b • (p + b)` for arbitrary unit coefficients `c p b ∈ kˣ`.
* `BoxSystem.delta_comp_delta_eq_zero_iff`: `δ² = 0` iff every square anticommutes.
* `BoxSystem.homotopy_spec`: an explicit contracting homotopy ("take the ball out of the chosen
  urn") gives `δ h + h δ = id - π`, where `π` is the projection onto the span of the *critical*
  shapes, those with no addable and no removable box.
* `BoxSystem.homologyBasis`: the cohomology `ker δ / im δ` is free with basis the classes of the
  critical shapes.
* `hypercube`: the hypercube complex `Y_α` (urns indexed by a finite type `α`, arbitrary signs
  with `d² = 0`) as a box system; `hypercube_contractible`: it is contractible when `α` is
  nonempty, i.e. `Y_k` is contractible for `k ≥ 1`, and `hypercube_homology_empty`: `Y_0 ≅ k`.

The paper works over a field `k`; everything here is over an arbitrary commutative ring, since
the coefficients `c p b` are units (they are `±1` for the odd Schur differential).
-/

namespace OddMath.Frontier.EQLima

open Finset

/-! ### Homology of an endomorphism and deformation retractions -/

section Homology

variable {k : Type*} [CommRing k] {M : Type*} [AddCommGroup M] [Module k M]

/-- The (co)homology `ker D / im D` of a `k`-linear endomorphism `D` (with `D ∘ D = 0` in
applications). -/
abbrev Homology (D : M →ₗ[k] M) : Type _ :=
  LinearMap.ker D ⧸ (LinearMap.range D).comap (LinearMap.ker D).subtype

/-- A deformation retraction of `(M, D)` onto a module `N` with zero differential:
`ρ ∘ ι = id`, `D ∘ ι = 0`, `ρ ∘ D = 0`, and a homotopy `h` with `D h + h D = id - ι ρ`. -/
structure Retraction (D : M →ₗ[k] M) (N : Type*) [AddCommGroup N] [Module k N] where
  /-- inclusion of the zero-differential complex -/
  ι : N →ₗ[k] M
  /-- projection onto the zero-differential complex -/
  ρ : M →ₗ[k] N
  /-- the homotopy -/
  h : M →ₗ[k] M
  ρ_comp_ι : ρ ∘ₗ ι = LinearMap.id
  D_comp_ι : D ∘ₗ ι = 0
  ρ_comp_D : ρ ∘ₗ D = 0
  homotopy : D ∘ₗ h + h ∘ₗ D = LinearMap.id - ι ∘ₗ ρ

namespace Retraction

variable {D : M →ₗ[k] M} {N : Type*} [AddCommGroup N] [Module k N] (r : Retraction D N)

theorem ρ_ι (n : N) : r.ρ (r.ι n) = n := by
  simpa using LinearMap.congr_fun r.ρ_comp_ι n

theorem D_ι (n : N) : D (r.ι n) = 0 := by
  simpa using LinearMap.congr_fun r.D_comp_ι n

theorem ρ_D (x : M) : r.ρ (D x) = 0 := by
  simpa using LinearMap.congr_fun r.ρ_comp_D x

theorem homotopy_apply (x : M) : D (r.h x) + r.h (D x) = x - r.ι (r.ρ x) := by
  simpa using LinearMap.congr_fun r.homotopy x

/-- Every cocycle is a coboundary plus an element of the image of `ι`. -/
theorem cocycle_eq {z : M} (hz : D z = 0) : z = D (r.h z) + r.ι (r.ρ z) := by
  have := r.homotopy_apply z
  rw [hz, map_zero, add_zero] at this
  rw [this, sub_add_cancel]

/-- An element of the image of `ι` which is a coboundary is zero. -/
theorem eq_zero_of_ι_eq_D {n : N} {y : M} (h : r.ι n = D y) : n = 0 := by
  rw [← r.ρ_ι n, h, r.ρ_D]

/-- The map from cohomology to `N` induced by `ρ`. -/
def toN : Homology D →ₗ[k] N :=
  Submodule.liftQ _ (r.ρ ∘ₗ (LinearMap.ker D).subtype) (by
    rintro ⟨x, hx⟩ hx'
    simp only [Submodule.mem_comap, Submodule.coe_subtype, LinearMap.mem_range] at hx'
    obtain ⟨y, rfl⟩ := hx'
    simp [r.ρ_D])

/-- The map from `N` to cohomology induced by `ι`. -/
def ofN : N →ₗ[k] Homology D :=
  Submodule.mkQ _ ∘ₗ LinearMap.codRestrict (LinearMap.ker D) r.ι (fun n => r.D_ι n)

theorem ofN_apply (n : N) :
    r.ofN n = Submodule.Quotient.mk ⟨r.ι n, r.D_ι n⟩ := rfl

/-- The cohomology of `(M, D)` is isomorphic to `N`. -/
def homologyEquiv : Homology D ≃ₗ[k] N :=
  LinearEquiv.ofLinearMap r.toN r.ofN
    (LinearMap.ext fun n => by simp [toN, ofN, r.ρ_ι])
    (Submodule.linearMap_qext _ <| LinearMap.ext fun z => by
      obtain ⟨z, hz⟩ := z
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, toN,
        Submodule.liftQ_apply, Submodule.coe_subtype, LinearMap.id_coe, id_eq, ofN]
      rw [Submodule.Quotient.eq]
      simp only [Submodule.mem_comap, Submodule.coe_subtype, AddSubgroupClass.coe_sub,
        LinearMap.mem_range]
      refine ⟨-r.h z, ?_⟩
      have := r.homotopy_apply z
      rw [LinearMap.mem_ker.mp hz, map_zero, add_zero] at this
      rw [map_neg, this]
      abel)

theorem homologyEquiv_symm_apply (n : N) :
    r.homologyEquiv.symm n = Submodule.Quotient.mk ⟨r.ι n, r.D_ι n⟩ := rfl

end Retraction

end Homology

/-! ### Box systems -/

/-- Abstract combinatorics of adding and removing boxes (the "urns and balls" of Ellis–Qi,
Appendix A.1.1 and A.1.3).  `cells p` determines `p`; `A p` (addable boxes) and `R p`
(removable boxes) are finite; adding an addable box `b` inserts `b` into the cells, removes `b`
from the addable set and adds it to the removable set, and changes nothing else (this is the
content of Lemma A.1 for white boxes). -/
structure BoxSystem (P : Type*) (B : Type*) [DecidableEq B] where
  /-- the cells of a shape -/
  cells : P → Finset B
  cells_injective : Function.Injective cells
  /-- the addable boxes -/
  A : P → Finset B
  /-- the removable boxes -/
  R : P → Finset B
  /-- add a box -/
  add : P → B → P
  /-- remove a box -/
  rem : P → B → P
  notMem_cells_of_mem_A : ∀ {p b}, b ∈ A p → b ∉ cells p
  cells_add : ∀ {p b}, b ∈ A p → cells (add p b) = insert b (cells p)
  mem_cells_of_mem_R : ∀ {p b}, b ∈ R p → b ∈ cells p
  cells_rem : ∀ {p b}, b ∈ R p → cells (rem p b) = (cells p).erase b
  A_add : ∀ {p b}, b ∈ A p → A (add p b) = (A p).erase b
  R_add : ∀ {p b}, b ∈ A p → R (add p b) = insert b (R p)
  mem_A_rem : ∀ {p b}, b ∈ R p → b ∈ A (rem p b)

namespace BoxSystem

variable {P B : Type*} [DecidableEq B] (S : BoxSystem P B)

theorem notMem_R_of_mem_A {p : P} {b : B} (h : b ∈ S.A p) : b ∉ S.R p :=
  fun h' => S.notMem_cells_of_mem_A h (S.mem_cells_of_mem_R h')

theorem add_rem {p : P} {b : B} (h : b ∈ S.R p) : S.add (S.rem p b) b = p := by
  apply S.cells_injective
  rw [S.cells_add (S.mem_A_rem h), S.cells_rem h, Finset.insert_erase (S.mem_cells_of_mem_R h)]

theorem mem_R_add {p : P} {b : B} (h : b ∈ S.A p) : b ∈ S.R (S.add p b) := by
  rw [S.R_add h]; exact Finset.mem_insert_self _ _

theorem rem_add {p : P} {b : B} (h : b ∈ S.A p) : S.rem (S.add p b) b = p := by
  apply S.cells_injective
  rw [S.cells_rem (S.mem_R_add h), S.cells_add h,
    Finset.erase_insert (S.notMem_cells_of_mem_A h)]

theorem A_rem {p : P} {b : B} (h : b ∈ S.R p) : S.A (S.rem p b) = insert b (S.A p) := by
  have h1 := S.A_add (S.mem_A_rem h)
  rw [S.add_rem h] at h1
  rw [h1, Finset.insert_erase (S.mem_A_rem h)]

theorem R_rem {p : P} {b : B} (h : b ∈ S.R p) : S.R (S.rem p b) = (S.R p).erase b := by
  have h1 := S.R_add (S.mem_A_rem h)
  rw [S.add_rem h] at h1
  rw [h1, Finset.erase_insert (S.notMem_R_of_mem_A (S.mem_A_rem h))]

/-- The set of all addable and removable boxes ("urns"). -/
def U (p : P) : Finset B := S.A p ∪ S.R p

theorem U_add {p : P} {b : B} (h : b ∈ S.A p) : S.U (S.add p b) = S.U p := by
  unfold U
  rw [S.A_add h, S.R_add h]
  ext x
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert]
  constructor
  · rintro (⟨-, hx⟩ | rfl | hx)
    · exact Or.inl hx
    · exact Or.inl h
    · exact Or.inr hx
  · rintro (hx | hx)
    · by_cases hxb : x = b
      · exact Or.inr (Or.inl hxb)
      · exact Or.inl ⟨hxb, hx⟩
    · exact Or.inr (Or.inr hx)

theorem add_add_comm {p : P} {b b' : B} (hb : b ∈ S.A p) (hb' : b' ∈ S.A p) (hne : b ≠ b') :
    S.add (S.add p b) b' = S.add (S.add p b') b := by
  have h1 : b' ∈ S.A (S.add p b) := by rw [S.A_add hb]; exact Finset.mem_erase.mpr ⟨hne.symm, hb'⟩
  have h2 : b ∈ S.A (S.add p b') := by rw [S.A_add hb']; exact Finset.mem_erase.mpr ⟨hne, hb⟩
  apply S.cells_injective
  rw [S.cells_add h1, S.cells_add hb, S.cells_add h2, S.cells_add hb', Finset.insert_comm]

theorem add_injOn {p : P} {b b' : B} (hb : b ∈ S.A p) (hb' : b' ∈ S.A p)
    (h : S.add p b = S.add p b') : b = b' := by
  have h1 := congrArg S.cells h
  rw [S.cells_add hb, S.cells_add hb'] at h1
  have : b ∈ insert b' (S.cells p) := h1 ▸ Finset.mem_insert_self _ _
  rcases Finset.mem_insert.mp this with h2 | h2
  · exact h2
  · exact absurd h2 (S.notMem_cells_of_mem_A hb)

theorem add_add_eq_iff {p : P} {x y b b' : B} (hx : x ∈ S.A p) (hy : y ∈ S.A p) (hxy : x ≠ y)
    (hb : b ∈ S.A p) (hb' : b' ∈ S.A p) (hbb' : b ≠ b') :
    S.add (S.add p x) y = S.add (S.add p b) b' ↔ (x = b ∧ y = b') ∨ (x = b' ∧ y = b) := by
  have hy' : y ∈ S.A (S.add p x) := by rw [S.A_add hx]; exact Finset.mem_erase.mpr ⟨hxy.symm, hy⟩
  have hb'' : b' ∈ S.A (S.add p b) := by
    rw [S.A_add hb]; exact Finset.mem_erase.mpr ⟨hbb'.symm, hb'⟩
  constructor
  · intro h
    have h1 := congrArg S.cells h
    rw [S.cells_add hy', S.cells_add hx, S.cells_add hb'', S.cells_add hb] at h1
    have mx : x ∈ insert b' (insert b (S.cells p)) := h1 ▸ by simp
    have my : y ∈ insert b' (insert b (S.cells p)) := h1 ▸ by simp
    have mb : b ∈ insert y (insert x (S.cells p)) := h1.symm ▸ by simp
    simp only [Finset.mem_insert] at mx my mb
    have nx := S.notMem_cells_of_mem_A hx
    have ny := S.notMem_cells_of_mem_A hy
    have nb := S.notMem_cells_of_mem_A hb
    rcases mx with rfl | rfl | hx'
    · rcases my with rfl | rfl | hy'
      · exact absurd rfl hxy
      · exact Or.inr ⟨rfl, rfl⟩
      · exact absurd hy' ny
    · rcases my with rfl | rfl | hy'
      · exact Or.inl ⟨rfl, rfl⟩
      · exact absurd rfl hxy
      · exact absurd hy' ny
    · exact absurd hx' nx
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact S.add_add_comm hx hy hxy

/-! ### The complex -/

section Complex

variable {k : Type*} [CommRing k]

/-- The differential `δ(p) = Σ_{b ∈ A p} c p b • (p + b)` on the free module `P →₀ k`. -/
noncomputable def delta (c : P → B → kˣ) : (P →₀ k) →ₗ[k] (P →₀ k) :=
  Finsupp.linearCombination k
    (fun p => ∑ b ∈ S.A p, ((c p b : kˣ) : k) • Finsupp.single (S.add p b) (1 : k))

theorem delta_single (c : P → B → kˣ) (p : P) :
    S.delta c (Finsupp.single p 1) =
      ∑ b ∈ S.A p, ((c p b : kˣ) : k) • Finsupp.single (S.add p b) (1 : k) := by
  simp [delta]

/-- The square condition: the two paths `p → p + b → p + b + b'` and `p → p + b' → p + b' + b`
carry opposite coefficients. -/
def SquareCond (c : P → B → kˣ) : Prop :=
  ∀ p b b', b ∈ S.A p → b' ∈ S.A p → b ≠ b' →
    ((c p b : kˣ) : k) * c (S.add p b) b' + (c p b' : k) * c (S.add p b') b = 0

theorem sum_erase_eq_sum_offDiag {M : Type*} [AddCommMonoid M] (s : Finset B) (f : B → B → M) :
    ∑ x ∈ s, ∑ y ∈ s.erase x, f x y = ∑ z ∈ s.offDiag, f z.1 z.2 := by
  refine (Finset.sum_finset_product (f := fun z : B × B => f z.1 z.2) (s.offDiag) s
    (fun x => s.erase x) ?_).symm
  intro z
  simp only [Finset.mem_offDiag, Finset.mem_erase]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, Ne.symm h3, h2⟩
  · rintro ⟨h1, h3, h2⟩; exact ⟨h1, h2, Ne.symm h3⟩

theorem delta_delta_single (c : P → B → kˣ) (p : P) :
    S.delta c (S.delta c (Finsupp.single p 1)) =
      ∑ z ∈ (S.A p).offDiag, (((c p z.1 : kˣ) : k) * c (S.add p z.1) z.2) •
        Finsupp.single (S.add (S.add p z.1) z.2) (1 : k) := by
  rw [delta_single, map_sum]
  refine Eq.trans ?_ (sum_erase_eq_sum_offDiag (S.A p) (fun x y =>
    (((c p x : kˣ) : k) * c (S.add p x) y) • Finsupp.single (S.add (S.add p x) y) (1 : k)))
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [map_smul, delta_single, S.A_add hx, Finset.smul_sum]
  simp only [smul_smul]

theorem delta_sq_eq_zero_of_squareCond {c : P → B → kˣ} (hc : S.SquareCond c) (x : P →₀ k) :
    S.delta c (S.delta c x) = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single p a =>
    rw [← mul_one a, ← smul_eq_mul, ← Finsupp.smul_single, map_smul, map_smul,
      delta_delta_single]
    rw [Finset.sum_involution (fun z _ => z.swap)]
    · simp
    · intro z hz
      obtain ⟨h1, h2, h3⟩ := Finset.mem_offDiag.mp hz
      simp only [Prod.fst_swap, Prod.snd_swap]
      rw [S.add_add_comm h2 h1 (Ne.symm h3), ← add_smul, hc p z.1 z.2 h1 h2 h3, zero_smul]
    · intro z hz _
      obtain ⟨-, -, h3⟩ := Finset.mem_offDiag.mp hz
      intro h
      exact h3 (congrArg Prod.fst h).symm
    · intro z hz
      obtain ⟨h1, h2, h3⟩ := Finset.mem_offDiag.mp hz
      exact Finset.mem_offDiag.mpr ⟨h2, h1, Ne.symm h3⟩
    · intro z _; rfl

theorem squareCond_of_delta_sq {c : P → B → kˣ} (h : ∀ x, S.delta c (S.delta c x) = 0) :
    S.SquareCond c := by
  classical
  intro p b b' hb hb' hbb'
  have h0 := congrArg (fun f : P →₀ k => f (S.add (S.add p b) b')) (h (Finsupp.single p 1))
  simp only [delta_delta_single, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finsupp.coe_zero,
    Pi.zero_apply] at h0
  rw [Finset.sum_eq_add (b, b') (b', b) (by simp [hbb'])] at h0
  · simpa [S.add_add_comm hb' hb (Ne.symm hbb')] using h0
  · intro z hz hne
    obtain ⟨h1, h2, h3⟩ := Finset.mem_offDiag.mp hz
    rw [ite_eq_right_iff.mpr]
    intro hh
    exfalso
    rw [S.add_add_eq_iff h1 h2 h3 hb hb' hbb'] at hh
    rcases hh with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact hne.1 (Prod.ext e1 e2)
    · exact hne.2 (Prod.ext e1 e2)
  · intro hn; exact absurd (Finset.mem_offDiag.mpr ⟨hb, hb', hbb'⟩) hn
  · intro hn; exact absurd (Finset.mem_offDiag.mpr ⟨hb', hb, Ne.symm hbb'⟩) hn

/-- `δ² = 0` if and only if every square anticommutes. -/
theorem delta_comp_delta_eq_zero_iff (c : P → B → kˣ) :
    S.delta c ∘ₗ S.delta c = 0 ↔ S.SquareCond c := by
  constructor
  · intro h
    exact S.squareCond_of_delta_sq fun x => by simpa using LinearMap.congr_fun h x
  · intro h
    exact LinearMap.ext fun x => by simpa using S.delta_sq_eq_zero_of_squareCond h x

/-! ### The contracting homotopy -/

/-- A choice of an element of a nonempty finite set. -/
noncomputable def pick (s : Finset B) : Option B :=
  if h : s.Nonempty then some h.choose else none

omit [DecidableEq B] in
theorem pick_eq_none {s : Finset B} : pick s = none ↔ s = ∅ := by
  unfold pick
  split_ifs with h
  · simp only [false_iff]
    exact h.ne_empty
  · simpa [Finset.not_nonempty_iff_eq_empty] using h

omit [DecidableEq B] in
theorem mem_of_pick_eq_some {s : Finset B} {b : B} (h : pick s = some b) : b ∈ s := by
  unfold pick at h
  split_ifs at h with hs
  · cases h; exact hs.choose_spec

/-- The chosen urn of a shape: an element of `U p`, depending only on `U p`. -/
noncomputable def urn (p : P) : Option B := pick (S.U p)

theorem urn_add {p : P} {b : B} (h : b ∈ S.A p) : S.urn (S.add p b) = S.urn p := by
  unfold urn; rw [S.U_add h]

/-- A shape is *critical* if it has no addable and no removable boxes. -/
def Crit (p : P) : Prop := S.U p = ∅

instance (p : P) : Decidable (S.Crit p) := inferInstanceAs (Decidable (S.U p = ∅))

theorem crit_iff (p : P) : S.Crit p ↔ S.A p = ∅ ∧ S.R p = ∅ := by
  simp [Crit, U, Finset.union_eq_empty]

/-- The homotopy on a basis vector: if the chosen urn of `p` holds a ball `u`, remove it
(with the inverse coefficient); otherwise `0`. -/
noncomputable def hvec (c : P → B → kˣ) (p : P) : P →₀ k :=
  match S.urn p with
  | none => 0
  | some u =>
    if u ∈ S.R p then
      ((((c (S.rem p u) u)⁻¹ : kˣ)) : k) • Finsupp.single (S.rem p u) (1 : k)
    else 0

/-- The contracting homotopy. -/
noncomputable def homotopy (c : P → B → kˣ) : (P →₀ k) →ₗ[k] (P →₀ k) :=
  Finsupp.linearCombination k (S.hvec c)

theorem hvec_none (c : P → B → kˣ) {p : P} (h : S.urn p = none) : S.hvec c p = 0 := by
  simp [hvec, h]

theorem hvec_of_mem_R (c : P → B → kˣ) {p : P} {u : B} (h : S.urn p = some u) (hu : u ∈ S.R p) :
    S.hvec c p = ((((c (S.rem p u) u)⁻¹ : kˣ)) : k) • Finsupp.single (S.rem p u) (1 : k) := by
  simp [hvec, h, hu]

theorem hvec_of_notMem_R (c : P → B → kˣ) {p : P} {u : B} (h : S.urn p = some u)
    (hu : u ∉ S.R p) : S.hvec c p = 0 := by
  simp [hvec, h, hu]

theorem homotopy_single (c : P → B → kˣ) (p : P) :
    S.homotopy c (Finsupp.single p 1) = S.hvec c p := by
  simp [homotopy]

/-- The set of critical shapes. -/
def critSet : Set P := {p | S.Crit p}

instance : DecidablePred (· ∈ S.critSet) := fun p => inferInstanceAs (Decidable (S.Crit p))

/-- Inclusion of the span of the critical shapes. -/
noncomputable def critι : (S.critSet →₀ k) →ₗ[k] (P →₀ k) :=
  (Finsupp.supported k k S.critSet).subtype ∘ₗ
    (Finsupp.supportedEquivFinsupp (R := k) S.critSet).symm.toLinearMap

/-- Projection onto the span of the critical shapes. -/
noncomputable def critρ : (P →₀ k) →ₗ[k] (S.critSet →₀ k) :=
  (Finsupp.supportedEquivFinsupp (R := k) S.critSet).toLinearMap ∘ₗ
    Finsupp.restrictDom k k S.critSet

theorem critι_single (p : S.critSet) :
    S.critι (Finsupp.single p (1 : k)) = Finsupp.single (p : P) 1 := by
  simp [critι]

theorem critι_critρ (x : P →₀ k) :
    S.critι (S.critρ x) = Finsupp.filter (fun p => p ∈ S.critSet) x := by
  simp only [critι, critρ, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.symm_apply_apply, Submodule.coe_subtype]
  rw [Finsupp.restrictDom_apply]

theorem critρ_critι : S.critρ (k := k) ∘ₗ S.critι = LinearMap.id := by
  ext p : 2
  simp only [critρ, critι, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  have := LinearMap.congr_fun (Finsupp.restrictDom_comp_subtype (M := k) (R := k) S.critSet)
    ((Finsupp.supportedEquivFinsupp (R := k) S.critSet).symm (Finsupp.lsingle (R := k) p (1 : k)))
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at this
  rw [this]
  simp

theorem delta_single_of_crit (c : P → B → kˣ) {p : P} (hp : S.Crit p) :
    S.delta c (Finsupp.single p 1) = 0 := by
  rw [delta_single, ((S.crit_iff p).mp hp).1, Finset.sum_empty]

theorem delta_apply_of_crit (c : P → B → kˣ) (x : P →₀ k) {t : P} (ht : S.Crit t) :
    S.delta c x t = 0 := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single p a =>
    rw [← mul_one a, ← smul_eq_mul, ← Finsupp.smul_single, map_smul, Finsupp.smul_apply,
      delta_single, Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_zero, smul_zero]
    intro b hb
    rw [Finsupp.smul_apply, Finsupp.single_apply, ite_eq_right_iff.mpr, smul_zero]
    rintro rfl
    have := S.mem_R_add hb
    rw [((S.crit_iff _).mp ht).2] at this
    simp at this

theorem units_aux (a b c d : kˣ) (h : (a : k) * b + (c : k) * d = 0) :
    ((a⁻¹ : kˣ) : k) * c + (b : k) * ((d⁻¹ : kˣ) : k) = 0 := by
  have e : ((a⁻¹ : kˣ) : k) * c + (b : k) * ((d⁻¹ : kˣ) : k) =
      ((a⁻¹ : kˣ) : k) * ((d⁻¹ : kˣ) : k) * ((a : k) * b + (c : k) * d) := by
    have ha : ((a⁻¹ : kˣ) : k) * a = 1 := by simp
    have hd : (d : k) * ((d⁻¹ : kˣ) : k) = 1 := by simp
    linear_combination (-(b : k) * ((d⁻¹ : kˣ) : k)) * ha - ((a⁻¹ : kˣ) : k) * (c : k) * hd
  rw [e, h, mul_zero]

/-- The homotopy identity `δ h + h δ = id - π` on basis vectors. -/
theorem homotopy_single_spec {c : P → B → kˣ} (hc : S.SquareCond c) (p : P) :
    S.delta c (S.homotopy c (Finsupp.single p 1)) + S.homotopy c (S.delta c (Finsupp.single p 1))
      = Finsupp.single p 1 - Finsupp.filter (fun q => q ∈ S.critSet) (Finsupp.single p 1) := by
  rw [homotopy_single]
  rcases hu : S.urn p with _ | u
  · -- no urns: `p` is critical
    have hp : S.Crit p := pick_eq_none.mp hu
    rw [S.hvec_none c hu, S.delta_single_of_crit c hp, map_zero, map_zero, add_zero,
      Finsupp.filter_single_of_pos _ (show p ∈ S.critSet from hp), sub_self]
  · have huU : u ∈ S.U p := mem_of_pick_eq_some hu
    have hnc : ¬ S.Crit p := fun h => by rw [Crit] at h; rw [h] at huU; simp at huU
    rw [Finsupp.filter_single_of_neg _ (show p ∉ S.critSet from hnc), sub_zero]
    by_cases huR : u ∈ S.R p
    · -- the urn holds a ball
      set q := S.rem p u with hq
      have huAq : u ∈ S.A q := S.mem_A_rem huR
      have hAq : S.A q = insert u (S.A p) := S.A_rem huR
      have huAp : u ∉ S.A p := fun h => S.notMem_R_of_mem_A h huR
      have hqu : S.add q u = p := S.add_rem huR
      rw [S.hvec_of_mem_R c hu huR, map_smul, delta_single, hAq, Finset.sum_insert huAp, hqu,
        smul_add, smul_smul, Units.inv_mul, one_smul, delta_single, map_sum]
      rw [add_assoc, add_eq_left, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun b hb => ?_
      have hbu : b ≠ u := fun h => huAp (h ▸ hb)
      have hbAq : b ∈ S.A q := by rw [hAq]; exact Finset.mem_insert_of_mem hb
      have hurn : S.urn (S.add p b) = some u := by rw [S.urn_add hb, hu]
      have huR' : u ∈ S.R (S.add p b) := by
        rw [S.R_add hb]; exact Finset.mem_insert_of_mem huR
      have hrem : S.rem (S.add p b) u = S.add q b := by
        apply S.cells_injective
        rw [S.cells_rem huR', S.cells_add hb, S.cells_add hbAq, S.cells_rem huR,
          Finset.erase_insert_of_ne hbu]
      rw [map_smul, homotopy_single, S.hvec_of_mem_R c hurn huR', hrem, smul_smul, smul_smul,
        ← add_smul]
      have hsq := hc q u b huAq hbAq hbu.symm
      rw [hqu] at hsq
      rw [units_aux _ _ _ _ hsq, zero_smul]
    · -- the urn is empty
      have huA : u ∈ S.A p := by
        rcases Finset.mem_union.mp huU with h | h
        · exact h
        · exact absurd h huR
      rw [S.hvec_of_notMem_R c hu huR, map_zero, zero_add, delta_single, map_sum]
      rw [Finset.sum_eq_single u]
      · have hurn : S.urn (S.add p u) = some u := by rw [S.urn_add huA, hu]
        rw [map_smul, homotopy_single, S.hvec_of_mem_R c hurn (S.mem_R_add huA),
          S.rem_add huA, smul_smul, Units.mul_inv, one_smul]
      · intro b hb hbu
        have hurn : S.urn (S.add p b) = some u := by rw [S.urn_add hb, hu]
        rw [map_smul, homotopy_single, S.hvec_of_notMem_R c hurn, smul_zero]
        rw [S.R_add hb, Finset.mem_insert]
        rintro (h | h)
        · exact hbu h.symm
        · exact huR h
      · intro h; exact absurd huA h

/-- The deformation retraction of the box complex onto the span of the critical shapes. -/
noncomputable def retraction {c : P → B → kˣ} (hc : S.SquareCond c) :
    Retraction (S.delta c) (S.critSet →₀ k) where
  ι := S.critι
  ρ := S.critρ
  h := S.homotopy c
  ρ_comp_ι := S.critρ_critι
  D_comp_ι := by
    ext p : 2
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.zero_apply]
    rw [Finsupp.lsingle_apply, critι_single, S.delta_single_of_crit c p.2]
  ρ_comp_D := by
    ext p q
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.zero_apply,
      Finsupp.coe_zero, Pi.zero_apply, critρ, LinearEquiv.coe_coe,
      Finsupp.supportedEquivFinsupp_apply_apply, Finsupp.restrictDom_apply,
      Finsupp.filter_apply_pos _ _ q.2]
    exact S.delta_apply_of_crit c _ q.2
  homotopy := by
    ext p : 2
    simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.sub_apply, LinearMap.id_coe, id_eq, Finsupp.lsingle_apply]
    rw [S.critι_critρ, S.homotopy_single_spec hc p]

theorem homotopy_spec {c : P → B → kˣ} (hc : S.SquareCond c) (x : P →₀ k) :
    S.delta c (S.homotopy c x) + S.homotopy c (S.delta c x) =
      x - Finsupp.filter (fun q => q ∈ S.critSet) x := by
  rw [← S.critι_critρ]
  exact (S.retraction hc).homotopy_apply x

/-- **Cohomology of a box complex.** `H(P →₀ k, δ)` is isomorphic to the free module on the
critical shapes. -/
noncomputable def homologyEquiv {c : P → B → kˣ} (hc : S.SquareCond c) :
    Homology (S.delta c) ≃ₗ[k] (S.critSet →₀ k) :=
  (S.retraction hc).homologyEquiv

/-- **Cohomology of a box complex.** `H(P →₀ k, δ)` is free, with basis the classes of the
critical shapes (which are cocycles). -/
noncomputable def homologyBasis {c : P → B → kˣ} (hc : S.SquareCond c) :
    Module.Basis S.critSet k (Homology (S.delta c)) :=
  Module.Basis.ofRepr (S.homologyEquiv hc)

theorem homologyBasis_apply {c : P → B → kˣ} (hc : S.SquareCond c) (p : S.critSet) :
    S.homologyBasis hc p =
      Submodule.Quotient.mk ⟨Finsupp.single (p : P) 1, by
        rw [LinearMap.mem_ker]; exact S.delta_single_of_crit c p.2⟩ := by
  rw [homologyBasis, Module.Basis.coe_ofRepr]
  change (S.retraction hc).homologyEquiv.symm _ = _
  rw [Retraction.homologyEquiv_symm_apply]
  congr 1
  exact Subtype.ext (S.critι_single p)

end Complex

end BoxSystem

/-! ### Hypercube complexes (Appendix A.1.1) -/

section Hypercube

variable (α : Type*) [Fintype α] [DecidableEq α]

/-- The hypercube `Y_α` of Ellis–Qi, Appendix A.1.1, as a box system: the urns are indexed by
`α`, a shape is the finite set of filled urns, the addable boxes are the empty urns and the
removable boxes are the filled urns.  With coefficients `c` satisfying `δ² = 0` (equivalently
`SquareCond`), `delta` is the hypercube complex `Y_k`, `k = |α|`, with arbitrary signs. -/
def hypercube : BoxSystem (Finset α) α where
  cells := id
  cells_injective := Function.injective_id
  A s := Finset.univ \ s
  R s := s
  add s b := insert b s
  rem s b := s.erase b
  notMem_cells_of_mem_A := by
    intro p b h
    exact (Finset.mem_sdiff.mp h).2
  cells_add := fun _ => rfl
  mem_cells_of_mem_R := fun h => h
  cells_rem := fun _ => rfl
  A_add := by
    intro p b _
    exact Finset.sdiff_insert _ _ _
  R_add := fun _ => rfl
  mem_A_rem := by
    intro p b _
    simp

variable {α}

theorem hypercube_crit_iff (s : Finset α) : (hypercube α).Crit s ↔ IsEmpty α := by
  rw [BoxSystem.crit_iff]
  change (Finset.univ \ s = ∅ ∧ s = ∅) ↔ _
  constructor
  · rintro ⟨h1, rfl⟩
    rwa [Finset.sdiff_empty, Finset.univ_eq_empty_iff] at h1
  · intro h
    exact ⟨by simp [Finset.univ_eq_empty], Finset.eq_empty_of_isEmpty s⟩

variable {k : Type*} [CommRing k]

/-- **`Y_k` is contractible for `k ≥ 1`** (Ellis–Qi, Appendix A.1.1): for any coefficients with
`δ² = 0`, the homotopy `h` satisfies `δ h + h δ = id`. -/
theorem hypercube_contractible [Nonempty α] {c : Finset α → α → kˣ}
    (hc : (hypercube α).delta c ∘ₗ (hypercube α).delta c = 0) (x : Finset α →₀ k) :
    (hypercube α).delta c ((hypercube α).homotopy c x) +
      (hypercube α).homotopy c ((hypercube α).delta c x) = x := by
  have hc' := ((hypercube α).delta_comp_delta_eq_zero_iff c).mp hc
  rw [(hypercube α).homotopy_spec hc', sub_eq_self, Finsupp.filter_eq_zero_iff]
  intro s hs
  exact absurd ((hypercube_crit_iff s).mp hs) (not_isEmpty_of_nonempty α)

/-- For `k ≥ 1` every cocycle of `Y_k` is a coboundary. -/
theorem hypercube_exact [Nonempty α] {c : Finset α → α → kˣ}
    (hc : (hypercube α).delta c ∘ₗ (hypercube α).delta c = 0) {z : Finset α →₀ k}
    (hz : (hypercube α).delta c z = 0) :
    z = (hypercube α).delta c ((hypercube α).homotopy c z) := by
  have := hypercube_contractible hc z
  rwa [hz, map_zero, add_zero, eq_comm] at this

/-- `Y_0` is a single copy of `k`: its cohomology is free of rank one on the class of the
initial vector `v_∅`. -/
noncomputable def hypercube_homology_isEmpty [IsEmpty α] {c : Finset α → α → kˣ}
    (hc : (hypercube α).delta c ∘ₗ (hypercube α).delta c = 0) :
    Homology ((hypercube α).delta c) ≃ₗ[k] k :=
  haveI : Subsingleton (hypercube α).critSet :=
    ⟨fun _ _ => Subtype.ext ((Finset.eq_empty_of_isEmpty _).trans
      (Finset.eq_empty_of_isEmpty _).symm)⟩
  ((hypercube α).homologyEquiv (((hypercube α).delta_comp_delta_eq_zero_iff c).mp hc)).trans
    (Finsupp.uniqueLinearEquiv k k ⟨∅, (hypercube_crit_iff _).mpr inferInstance⟩)

end Hypercube

end OddMath.Frontier.EQLima
