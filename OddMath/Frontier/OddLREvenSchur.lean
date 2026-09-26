import OddMath.Frontier.EKGeneralQCommutative
import OddMath.Frontier.OddLRRule

/-!
# Even Schur functions and the even Pieri rule in `Λ₁`

Ellis, "The odd Littlewood–Richardson rule", arXiv:1111.3932v1 ("E"), §4.1, p.12, works "in the
even setting": `Λ` is the ring of symmetric functions, `s_λ` the Schur functions and `c^λ_{μν}`
the coefficient of `s_λ` in `s_μ s_ν`.

Carrier. `Λ₁ = EKGeneralQ.Lam 1` over `ℤ`: Ellis–Khovanov's `Λ'/I_q` at `q = 1`, the maximal
commutative quotient of the free algebra on `h₁, h₂, …` (`EKGeneralQ.lam_one_universal`), free
with basis `h_λ = h_{λ₁} ⋯ h_{λ_r}` (`EKGeneralQ.hBasisOne`), i.e. the ring of symmetric
functions.

* `sE λ`: the even Schur function, defined by unsigned Kostka inversion,
  `h_μ = Σ_{λ ⊢ |μ|} K_{λμ} s_λ` with `K_{λμ} = #SSYT(λ, μ)` (`hE_expand`), exactly as the odd
  `s^K_λ` is defined from the odd Kostka numbers (E (2.6)–(2.7)) with the signs dropped;
  `sBasisE`: the `s_λ` form a `ℤ`-basis of `Λ₁`.
* `evenLR λ μ ν`: the even Littlewood–Richardson coefficient, the `s_λ`-coordinate of `s_μ s_ν`.
* `kostka0_comp_perm`: the unsigned Kostka number `K_{λ,c}` of a composition `c` is invariant
  under permuting `c` (from `EKRskBijection.ek_eq_4_4`, `N = K⁰ᵀ K⁰`, and `det K⁰ = 1`).
* `sE_mul_hk`: the even Pieri rule `s_α h_k = Σ_{λ/α horizontal strip} s_λ` in `Λ₁`.
-/

namespace OddMath.Frontier.OddLREven

open scoped BigOperators
open DegreeShapes TableauSign TableauContent

noncomputable section

attribute [local instance] degreeFintype Classical.propDecidable

/-! ## The carrier `Λ₁` -/

/-- `Λ₁`, the ring of symmetric functions over `ℤ` (EK's `Λ'/I₁`). -/
abbrev Sym : Type := EKGeneralQ.Lam (1 : ℤ)

/-- `h_k ∈ Λ₁` (`h₀ = 1`). -/
def hk (k : ℕ) : Sym := EKGeneralQ.piQ (1 : ℤ) (EKGeneralQ.h ℤ k)

/-- `h_β = h_{β₁} ⋯ h_{β_r} ∈ Λ₁`. -/
def hE (β : YoungDiagram) : Sym := EKGeneralQ.piQ (1 : ℤ) (EKGeneralQ.hWord ℤ β.rowLens)

theorem hBasisOne_eq (β : YoungDiagram) : EKGeneralQ.hBasisOne (k := ℤ) β = hE β :=
  EKGeneralQ.hBasisOne_apply β

theorem hk_zero : hk 0 = 1 := by simp [hk]

theorem mul_comm' (a b : Sym) : a * b = b * a := EKGeneralQ.lam_one_mul_comm a b

theorem piQ_hWord_perm {l₁ l₂ : List ℕ} (hp : l₁.Perm l₂) :
    EKGeneralQ.piQ (1 : ℤ) (EKGeneralQ.hWord ℤ l₁) = EKGeneralQ.piQ (1 : ℤ) (EKGeneralQ.hWord ℤ l₂) := by
  rw [← sub_eq_zero, ← map_sub, EKGeneralQ.piQ_eq_zero_iff]
  exact EKGeneralQ.commutatorIdeal_le_radical (EKGeneralQ.hWord_perm_sub_mem hp)

theorem piQ_hWord_append (l : List ℕ) (k : ℕ) :
    EKGeneralQ.piQ (1 : ℤ) (EKGeneralQ.hWord ℤ (l ++ [k])) =
      EKGeneralQ.piQ (1 : ℤ) (EKGeneralQ.hWord ℤ l) * hk k := by
  simp [EKGeneralQ.hWord, hk, List.map_append, List.prod_append]

/-! ## Unsigned Kostka numbers and their inverse -/

/-- The unsigned Kostka matrix on partitions of `d`. -/
abbrev K (d : ℕ) : Matrix (DegreeShape d) (DegreeShape d) ℤ := EKGeneralQ.kostkaMat d

theorem K_apply (d : ℕ) (nu mu : DegreeShape d) :
    K d nu mu = ((tableauxOfContent nu.val (TableauDominance.shapeContent mu.val)).card : ℤ) := by
  simp only [K, EKGeneralQ.kostkaMat, EKRskBijection.kostka0, EKGeneralQ.compContent_rowLens]

theorem K_det_isUnit (d : ℕ) : IsUnit (K d).det := by
  rw [EKGeneralQ.kostkaMat_det]; exact isUnit_one

section Inversion

variable {V : Type*} [AddCommGroup V]

theorem inv_action (d : ℕ) (H : DegreeShape d → V) (β : DegreeShape d) :
    ∑ ν, K d ν β • (∑ γ, (K d)⁻¹ γ ν • H γ) = H β := by
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have e : ∀ γ : DegreeShape d, ∑ ν, (K d ν β * (K d)⁻¹ γ ν) • H γ = ((K d)⁻¹ * K d) γ β • H γ := by
    intro γ
    rw [← Finset.sum_smul, Matrix.mul_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro ν _
    ring
  simp_rw [e, Matrix.nonsing_inv_mul _ (K_det_isUnit d), Matrix.one_apply, ite_smul, one_smul,
    zero_smul]
  simp

theorem inv_action' (d : ℕ) (S : DegreeShape d → V) (γ : DegreeShape d) :
    ∑ β, (K d)⁻¹ β γ • (∑ ν, K d ν β • S ν) = S γ := by
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have e : ∀ ν : DegreeShape d, ∑ β, ((K d)⁻¹ β γ * K d ν β) • S ν = (K d * (K d)⁻¹) ν γ • S ν := by
    intro ν
    rw [← Finset.sum_smul, Matrix.mul_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro β _
    ring
  simp_rw [e, Matrix.mul_nonsing_inv _ (K_det_isUnit d), Matrix.one_apply, ite_smul, one_smul,
    zero_smul]
  simp

/-- The unsigned Kostka transform is injective. -/
theorem eq_zero_of_transform (d : ℕ) (S : DegreeShape d → V)
    (h : ∀ β : DegreeShape d, ∑ ν, K d ν β • S ν = 0) : S = 0 := by
  funext γ
  rw [← inv_action' d S γ]
  simp [h]

theorem eq_of_transform (d : ℕ) (S T : DegreeShape d → V)
    (h : ∀ β : DegreeShape d, ∑ ν, K d ν β • S ν = ∑ ν, K d ν β • T ν) : S = T := by
  have := eq_zero_of_transform d (S - T) (fun β => by
    simp only [Pi.sub_apply, smul_sub, Finset.sum_sub_distrib, h, sub_self])
  exact sub_eq_zero.mp this

end Inversion

/-! ## Even Schur functions -/

/-- The even Schur function `s_λ ∈ Λ₁`: `s_λ = Σ_{β ⊢ |λ|} (K⁻¹)_{βλ} h_β`, i.e. the solution of
`h_μ = Σ_λ K_{λμ} s_λ`. -/
def sE (lam : YoungDiagram) : Sym :=
  ∑ β : DegreeShape lam.card, (K lam.card)⁻¹ β ⟨lam, rfl⟩ • hE β.val

theorem sE_eq (d : ℕ) (nu : DegreeShape d) :
    sE nu.val = ∑ β : DegreeShape d, (K d)⁻¹ β nu • hE β.val := by
  obtain ⟨nu, rfl⟩ := nu
  rfl

/-- E (2.7) with the signs dropped: `h_β = Σ_{ν ⊢ |β|} K_{νβ} s_ν` in `Λ₁`. -/
theorem hE_expand (d : ℕ) (β : DegreeShape d) :
    hE β.val = ∑ ν : DegreeShape d, K d ν β • sE ν.val := by
  simp_rw [sE_eq d]
  exact (inv_action d (fun γ => hE γ.val) β).symm

/-- `s_λ` is characterised by `h_μ = Σ_λ K_{λμ} s_λ` in each degree. -/
theorem sE_unique (d : ℕ) (S : DegreeShape d → Sym)
    (hS : ∀ β : DegreeShape d, hE β.val = ∑ ν, K d ν β • S ν) (nu : DegreeShape d) :
    S nu = sE nu.val := by
  have := eq_of_transform d S (fun ν => sE ν.val) (fun β => by rw [← hS, hE_expand])
  exact congrFun this nu

/-! ## The Schur basis of `Λ₁` -/

/-- `h_β ↦ s_β`. -/
def toS : Sym →ₗ[ℤ] Sym := (EKGeneralQ.hBasisOne (k := ℤ)).constr ℤ sE

/-- `h_β ↦ Σ_ν K_{νβ} h_ν`. -/
def toH : Sym →ₗ[ℤ] Sym :=
  (EKGeneralQ.hBasisOne (k := ℤ)).constr ℤ
    (fun β => ∑ ν : DegreeShape β.card, K β.card ν ⟨β, rfl⟩ • hE ν.val)

theorem toS_hE (β : YoungDiagram) : toS (hE β) = sE β := by
  rw [← hBasisOne_eq, toS, Basis.constr_basis]

theorem toH_hE (d : ℕ) (β : DegreeShape d) :
    toH (hE β.val) = ∑ ν : DegreeShape d, K d ν β • hE ν.val := by
  obtain ⟨β, rfl⟩ := β
  rw [← hBasisOne_eq, toH, Basis.constr_basis]

theorem toS_toH (x : Sym) : toS (toH x) = x := by
  have : toS ∘ₗ toH = LinearMap.id := by
    apply (EKGeneralQ.hBasisOne (k := ℤ)).ext
    intro β
    rw [LinearMap.comp_apply, hBasisOne_eq, toH_hE β.card ⟨β, rfl⟩, map_sum]
    simp only [map_zsmul, toS_hE, LinearMap.id_apply]
    exact (hE_expand β.card ⟨β, rfl⟩).symm
  exact congrArg (fun f => f x) this

theorem toH_toS (x : Sym) : toH (toS x) = x := by
  have : toH ∘ₗ toS = LinearMap.id := by
    apply (EKGeneralQ.hBasisOne (k := ℤ)).ext
    intro β
    rw [LinearMap.comp_apply, hBasisOne_eq, toS_hE, sE_eq β.card ⟨β, rfl⟩, map_sum]
    simp only [map_zsmul, LinearMap.id_apply]
    simp_rw [toH_hE β.card]
    exact inv_action' β.card (fun γ => hE γ.val) ⟨β, rfl⟩
  exact congrArg (fun f => f x) this

/-- `h_β ↦ s_β` as a linear automorphism of `Λ₁`. -/
def toSEquiv : Sym ≃ₗ[ℤ] Sym :=
  LinearEquiv.ofLinear toS toH (LinearMap.ext toS_toH) (LinearMap.ext toH_toS)

/-- The even Schur functions form a `ℤ`-basis of `Λ₁`. -/
def sBasisE : Basis YoungDiagram ℤ Sym := (EKGeneralQ.hBasisOne (k := ℤ)).map toSEquiv

@[simp] theorem sBasisE_apply (lam : YoungDiagram) : sBasisE lam = sE lam := by
  rw [sBasisE, Basis.map_apply, hBasisOne_eq]
  exact toS_hE lam

/-- The even Littlewood–Richardson coefficient `c^λ_{μν}` (E §4.1, p.12): the coefficient of
`s_λ` in `s_μ s_ν`. -/
def evenLR (lam mu nu : YoungDiagram) : ℤ := sBasisE.repr (sE mu * sE nu) lam

/-- `c^λ_{μν}` is the unique family of coordinates of `s_μ s_ν`. -/
theorem evenLR_unique (mu nu : YoungDiagram) (c : YoungDiagram →₀ ℤ)
    (h : sE mu * sE nu = c.sum (fun lam a => a • sE lam)) (lam : YoungDiagram) :
    evenLR lam mu nu = c lam := by
  unfold evenLR
  rw [h]
  have : c.sum (fun lam a => a • sE lam) = Finsupp.linearCombination ℤ sBasisE c := by
    simp [Finsupp.linearCombination_apply]
  rw [this, sBasisE.repr_linearCombination]

/-! ## Symmetry of unsigned Kostka numbers -/

open EKRskBijection (kostka0 compContent)

theorem kostka0_eq_zero_of_card {m : ℕ} (la : YoungDiagram) (f : Fin m → ℕ)
    (h : la.card ≠ ∑ i, f i) : kostka0 la f = 0 := by
  unfold kostka0
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_not_mem]
  intro T hT
  rw [mem_tableauxOfContent] at hT
  have := content_total T
  rw [hT, EKRskBijection.compContent_total] at this
  exact h this.symm

/-- Permuting the rows of an `ℕ`-matrix. -/
def matPerm {m n : ℕ} (f : Fin m → ℕ) (ρ : Fin n → ℕ) (σ : Equiv.Perm (Fin m)) :
    EKRskBijection.Mat (f ∘ σ) ρ ≃ EKRskBijection.Mat f ρ where
  toFun A := ⟨fun i => A.1 (σ.symm i), fun i => by simpa using A.2.1 (σ.symm i), fun j => by
      rw [← A.2.2 j]; exact Equiv.sum_comp σ.symm (fun i => A.1 i j)⟩
  invFun A := ⟨fun i => A.1 (σ i), fun i => A.2.1 (σ i), fun j => by
      rw [← A.2.2 j]; exact Equiv.sum_comp σ (fun i => A.1 i j)⟩
  left_inv A := by apply Subtype.ext; funext i; simp
  right_inv A := by apply Subtype.ext; funext i; simp

/-- **Symmetry of Kostka numbers**: `K_{λ, c∘σ} = K_{λ, c}` for every composition `c` and
permutation `σ`. Proof: `#{ℕ-matrices with row sums c, column sums ρ} = Σ_λ K_{λc} K_{λρ}`
(RSK, `EKRskBijection.ek_eq_4_4`) is invariant under permuting `c`, and the matrix
`(K_{λρ})_{λ,ρ ⊢ d}` has determinant `1`. -/
theorem kostka0_comp_perm {m : ℕ} (la : YoungDiagram) (f : Fin m → ℕ) (σ : Equiv.Perm (Fin m)) :
    kostka0 la (f ∘ σ) = kostka0 la f := by
  have hs : ∑ i, (f ∘ σ) i = ∑ i, f i := Equiv.sum_comp σ f
  by_cases hd : la.card = ∑ i, f i
  swap
  · rw [kostka0_eq_zero_of_card la f hd, kostka0_eq_zero_of_card la _ (hs ▸ hd)]
  set d := ∑ i, f i with hd'
  let a : DegreeShape d → ℤ := fun x =>
    (kostka0 x.val (f ∘ σ) : ℤ) - kostka0 x.val f
  have ha : a = 0 := by
    apply EKGeneralQ.vecMul_eq_zero_of_det_one (K d) (EKGeneralQ.kostkaMat_det d) a
    funext ρ
    have e1 := EKRskBijection.ek_eq_4_4 (f ∘ σ) ρ.val.rowLens.get
    have e2 := EKRskBijection.ek_eq_4_4 f ρ.val.rowLens.get
    rw [Nat.card_congr (matPerm f _ σ), e2] at e1
    have e1' := congrArg (fun n : ℕ => (n : ℤ)) e1
    push_cast at e1'
    rw [EKGeneralQ.sum_degreeShape_cast hs (fun x => (kostka0 x (f ∘ σ) : ℤ) *
      kostka0 x ρ.val.rowLens.get)] at e1'
    simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Int.cast_id, Pi.zero_apply, a,
      sub_mul, Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    exact e1'.symm
  have := congrFun ha ⟨la, hd⟩
  simp only [a, Pi.zero_apply, sub_eq_zero] at this
  exact_mod_cast this

theorem kostka0_cast {m m' : ℕ} (la : YoungDiagram) (h : m = m') (f : Fin m' → ℕ) :
    kostka0 la (f ∘ Fin.cast h) = kostka0 la f := by
  subst h; rfl

/-- Two tuples whose value lists are permutations of each other differ by a permutation. -/
theorem exists_perm_of_ofFn_perm {n : ℕ} (f g : Fin n → ℕ)
    (h : (List.ofFn f).Perm (List.ofFn g)) : ∃ σ : Equiv.Perm (Fin n), g = f ∘ σ := by
  have hf := (Tuple.sort f).ofFn_comp_perm f
  have hg := (Tuple.sort g).ofFn_comp_perm g
  have hs : List.ofFn (f ∘ Tuple.sort f) = List.ofFn (g ∘ Tuple.sort g) :=
    List.eq_of_perm_of_sorted (hf.trans (h.trans hg.symm))
      (List.sorted_le_ofFn_iff.mpr (Tuple.monotone_sort f))
      (List.sorted_le_ofFn_iff.mpr (Tuple.monotone_sort g))
  have he := List.ofFn_injective hs
  refine ⟨Tuple.sort f * (Tuple.sort g)⁻¹, ?_⟩
  funext i
  have := congrFun he ((Tuple.sort g)⁻¹ i)
  simp only [Function.comp_apply, Equiv.Perm.apply_inv_self] at this
  simp only [Function.comp_apply, Equiv.Perm.coe_mul]
  exact this.symm

/-- Kostka numbers of compositions with permuted value lists agree. -/
theorem kostka0_of_perm {n : ℕ} (la : YoungDiagram) (f g : Fin n → ℕ)
    (h : (List.ofFn f).Perm (List.ofFn g)) : kostka0 la g = kostka0 la f := by
  obtain ⟨σ, rfl⟩ := exists_perm_of_ofFn_perm f g h
  exact kostka0_comp_perm la f σ

/-! ## Unsigned fibre counts of tableaux restricting to `T_μ` -/

section Fibres

open OddLRRule CompleteTableauExpansion TableauStripCorners

variable {mu : YoungDiagram} {c : ℕ → ℕ}

/-- `#{T of shape λ restricting to T_μ with content μ ∪ (c₁, …, c_t)}`. -/
def W0 (mu : YoungDiagram) (c : ℕ → ℕ) (t : ℕ) (lam : YoungDiagram) : ℕ :=
  Fintype.card (MF mu c t lam)

theorem sum_degreeShape_eq {M : Type*} [AddCommMonoid M] {m m' : ℕ} (h : m = m')
    (F : YoungDiagram → M) : ∑ u : DegreeShape m, F u.val = ∑ u : DegreeShape m', F u.val := by
  subst h; rfl

/-- One Pieri step for the fibre counts. -/
theorem W0_succ (t : ℕ) (v : DegreeShape (mdeg mu c (t + 1))) :
    W0 mu c (t + 1) v.val = ∑ u : DegreeShape (mdeg mu c t),
      if Horizontal u.val v.val then W0 mu c t u.val else 0 := by
  unfold W0
  rw [← Fintype.card_congr (mfStepEquiv t v), Fintype.card_sigma]
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (p := fun u : DegreeShape (mdeg mu c t) => Horizontal u.val v.val)
    (Finset.univ.filter (fun u => Horizontal u.val v.val)) (by simp)
    (fun u => Fintype.card (MF mu c t u.val))).symm

theorem W0_zero (lam : YoungDiagram) : W0 mu c 0 lam = if lam = mu then 1 else 0 := by
  have hc0 : muContent mu c 0 = TableauDominance.shapeContent mu := by simp [muContent]
  have hshape : ∀ T : MF mu c 0 lam, lam = mu := by
    intro T
    apply le_antisymm _ T.2.1.1
    intro p hp
    by_contra hm
    have h1 := T.2.1.2.2 p.1 p.2 hp hm
    have hct : content T.1 = TableauDominance.shapeContent mu := T.2.2.trans hc0
    have h2 := entry_mem_support T.1 (show (p.1, p.2) ∈ lam.cells by simpa using hp)
    rw [hct, Finsupp.mem_support_iff] at h2
    exact h2 (shapeContent_apply_gt mu h1)
  by_cases hl : lam = mu
  · subst hl
    rw [if_pos rfl]
    have hcan : ∀ T : MF lam c 0 lam, T.1 = TableauDominance.canonicalTableau lam := by
      intro T
      apply ext_cells
      intro p hp
      rw [TableauDominance.canonical_entry hp]
      exact T.2.1.2.1 p.1 p.2 (by simpa using hp)
    have hmem : FullCond lam (TableauDominance.canonicalTableau lam) ∧
        content (TableauDominance.canonicalTableau lam) = muContent lam c 0 := by
      refine ⟨⟨le_rfl, fun i j h => ?_, fun i j h h' => absurd h h'⟩, ?_⟩
      · exact TableauDominance.canonical_entry (p := (i, j)) (by simpa using h)
      · rw [TableauDominance.content_canonical, hc0]
    letI : Unique (MF lam c 0 lam) :=
      { default := ⟨_, hmem⟩
        uniq := fun T => Subtype.ext (hcan T) }
    rw [W0, Fintype.card_unique]
  · rw [if_neg hl, W0]
    haveI : IsEmpty (MF mu c 0 lam) := ⟨fun T => hl (hshape T)⟩
    exact Fintype.card_eq_zero

/-- Fibres of `T_S` are skew tableaux (`OddLRRule.mfEquiv`). -/
theorem W0_eq (t : ℕ) (lam : YoungDiagram) :
    W0 mu c t lam = (OddLRTableau.ofContent lam mu (prefixContent c t)).card := by
  rw [W0, Fintype.card_congr (mfEquiv t lam)]
  unfold OddLRTableau.ofContent
  rw [Finset.card_map, Finset.card_univ]

theorem colLen_bot : (⊥ : YoungDiagram).colLen 0 = 0 := by
  by_contra h
  have : ((0, 0) : ℕ × ℕ) ∈ (⊥ : YoungDiagram) :=
    YoungDiagram.mem_iff_lt_colLen.mpr (Nat.pos_of_ne_zero h)
  simp at this

theorem shapeContent_bot : TableauDominance.shapeContent ⊥ = 0 := by
  simp [TableauDominance.shapeContent]

theorem muContent_bot (t : ℕ) : muContent ⊥ c t = prefixContent c t := by
  simp [muContent, colLen_bot, shapeContent_bot, prefixContent]

/-- For `μ = ∅` the fibre count is the Kostka number of the composition `(c₁, …, c_t)`. -/
theorem W0_bot (t : ℕ) (lam : YoungDiagram) :
    W0 ⊥ c t lam = (tableauxOfContent lam (prefixContent c t)).card := by
  rw [W0, ← Fintype.card_coe]
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro T
  rw [mem_tableauxOfContent, muContent_bot]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨bot_le, fun i j hij => absurd hij (by simp), fun i j hij _ => ?_⟩, h⟩
    rw [colLen_bot]
    exact T.positive hij

theorem mdeg_bot (t : ℕ) : mdeg ⊥ c t = prefixDegree c t := by
  simp [mdeg]

end Fibres

/-! ## The even Pieri rule in `Λ₁` -/

section Pieri

open OddLRRule CompleteTableauExpansion TableauStripCorners

/-- The composition `(β₁, …, β_t, k)`, one-based. -/
def snocC (β : YoungDiagram) (k : ℕ) (i : ℕ) : ℕ :=
  if i = β.colLen 0 + 1 then k else rowC β i

theorem prefixContent_snocC (β : YoungDiagram) (k : ℕ) :
    prefixContent (snocC β k) (β.colLen 0) = TableauDominance.shapeContent β := by
  rw [← prefixContent_rowC]
  unfold prefixContent
  apply Finset.sum_congr rfl
  intro i hi
  rw [snocC, if_neg (by have := Finset.mem_range.mp hi; omega)]

theorem prefixDegree_snocC (β : YoungDiagram) (k : ℕ) :
    prefixDegree (snocC β k) (β.colLen 0) = β.card := by
  have h := congrArg (fun f : ℕ →₀ ℕ => f.sum (fun _ n => n)) (prefixContent_snocC β k)
  simp only at h
  rw [← TableauDominance.content_canonical, content_total] at h
  rw [← h]
  unfold prefixContent prefixDegree
  rw [← Finsupp.sum_finset_sum_index (fun _ => rfl) (fun _ _ _ => rfl)]
  simp only [Finsupp.sum_single_index (h := fun _ n : ℕ => n) rfl]

theorem compContent_snocC (β : YoungDiagram) (k : ℕ) :
    compContent (fun i : Fin (β.colLen 0 + 1) => snocC β k (i.val + 1)) =
      prefixContent (snocC β k) (β.colLen 0 + 1) := by
  unfold compContent prefixContent
  exact Fin.sum_univ_eq_sum_range (fun i => Finsupp.single (i + 1) (snocC β k (i + 1))) _

theorem ofFn_snocC (β : YoungDiagram) (k : ℕ) :
    List.ofFn (fun i : Fin (β.colLen 0 + 1) => snocC β k (i.val + 1)) = β.rowLens ++ [k] := by
  rw [List.ofFn_succ', List.concat_eq_append]
  congr 1
  · apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_ofFn, Fin.coe_castSucc, YoungDiagram.get_rowLens]
    simp only [List.length_ofFn] at h1
    rw [snocC, if_neg (by omega), rowC]
    rfl
  · simp [snocC]

/-- The row lengths of `β ∪ (k)`: `k` inserted into the row lengths of `β`. -/
def insRows (β : YoungDiagram) (k : ℕ) : List ℕ := β.rowLens.orderedInsert (· ≥ ·) k

theorem insRows_sorted (β : YoungDiagram) (k : ℕ) : (insRows β k).Sorted (· ≥ ·) :=
  List.Sorted.orderedInsert k _ β.rowLens_sorted

theorem insRows_perm (β : YoungDiagram) (k : ℕ) : (insRows β k).Perm (β.rowLens ++ [k]) :=
  (List.perm_orderedInsert _ k _).trans (List.perm_append_singleton k _).symm

/-- The partition `β ∪ (k)`. -/
def insShape (β : YoungDiagram) (k : ℕ) : YoungDiagram :=
  YoungDiagram.ofRowLens (insRows β k) (insRows_sorted β k)

theorem insShape_rowLens (β : YoungDiagram) {k : ℕ} (hpos : 0 < k) :
    (insShape β k).rowLens = insRows β k := by
  apply YoungDiagram.rowLens_ofRowLens_eq_self
  intro x hx
  rcases List.mem_append.mp ((insRows_perm β k).subset hx) with h | h
  · exact β.pos_of_mem_rowLens x h
  · rw [List.mem_singleton.mp h]; exact hpos

theorem insShape_card (β : YoungDiagram) (k : ℕ) : (insShape β k).card = β.card + k := by
  rw [insShape, EKPartitionSpanning.card_ofRowLens, (insRows_perm β k).sum_eq, List.sum_append,
    EKIntegralBases.rowLens_sum]
  simp

theorem hE_mul_hk (β : YoungDiagram) {k : ℕ} (hpos : 0 < k) :
    hE β * hk k = hE (insShape β k) := by
  rw [hE, ← piQ_hWord_append, hE, insShape_rowLens β hpos]
  exact piQ_hWord_perm (insRows_perm β k).symm

theorem ofFn_get_cast {α : Type*} (l : List α) {n : ℕ} (h : n = l.length) :
    List.ofFn (l.get ∘ Fin.cast h) = l := by
  subst h; exact List.ofFn_get l

/-- `K_{w, β ∪ (k)}` is the number of tableaux of shape `w` and content `(β₁, …, β_t, k)`. -/
theorem card_insShape (w β : YoungDiagram) {k : ℕ} (hpos : 0 < k) :
    (tableauxOfContent w (TableauDominance.shapeContent (insShape β k))).card =
      (tableauxOfContent w (prefixContent (snocC β k) (β.colLen 0 + 1))).card := by
  have hlen : β.colLen 0 + 1 = (insShape β k).rowLens.length := by
    rw [insShape_rowLens β hpos, (insRows_perm β k).length_eq]; simp
  have e1 : kostka0 w (insShape β k).rowLens.get =
      (tableauxOfContent w (TableauDominance.shapeContent (insShape β k))).card := by
    unfold kostka0; rw [EKGeneralQ.compContent_rowLens]
  have e2 : kostka0 w (fun i : Fin (β.colLen 0 + 1) => snocC β k (i.val + 1)) =
      (tableauxOfContent w (prefixContent (snocC β k) (β.colLen 0 + 1))).card := by
    unfold kostka0; rw [compContent_snocC]
  rw [← e1, ← e2, ← kostka0_cast w hlen]
  apply kostka0_of_perm
  rw [ofFn_snocC, ofFn_get_cast, insShape_rowLens β hpos]
  exact (insRows_perm β k).symm

/-- The even Pieri count: `K_{w, β ∪ (k)} = Σ_{α ⊆ w, w/α horizontal} K_{αβ}`. -/
theorem K_insShape (d k : ℕ) (hpos : 0 < k) (β : DegreeShape d) (w : DegreeShape (d + k)) :
    (tableauxOfContent w.val (TableauDominance.shapeContent (insShape β.val k))).card =
      ∑ α : DegreeShape d, if Horizontal α.val w.val then
        (tableauxOfContent α.val (TableauDominance.shapeContent β.val)).card else 0 := by
  rw [card_insShape w.val β.val hpos, ← W0_bot]
  have hm : mdeg ⊥ (snocC β.val k) (β.val.colLen 0) = d := by
    rw [mdeg_bot, prefixDegree_snocC, β.property]
  have hm' : mdeg ⊥ (snocC β.val k) (β.val.colLen 0 + 1) = d + k := by
    rw [mdeg_bot, prefixDegree_succ, prefixDegree_snocC, β.property, snocC, if_pos rfl]
  have := W0_succ (mu := ⊥) (c := snocC β.val k) (β.val.colLen 0) ⟨w.val, w.property.trans hm'.symm⟩
  rw [this]
  rw [sum_degreeShape_eq hm (fun u => if Horizontal u w.val then
    W0 ⊥ (snocC β.val k) (β.val.colLen 0) u else 0)]
  apply Finset.sum_congr rfl
  intro α _
  rw [W0_bot, prefixContent_snocC]

/-- **Even Pieri rule** in `Λ₁`: `s_α h_k = Σ_{λ ⊢ |α|+k, λ/α horizontal strip} s_λ`. -/
theorem sE_mul_hk (d k : ℕ) (α : DegreeShape d) :
    sE α.val * hk k = ∑ w : DegreeShape (d + k), if Horizontal α.val w.val then sE w.val else 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · rw [hk_zero, mul_one]
    rw [Fintype.sum_eq_single (α := DegreeShape (d + 0)) ⟨α.val, α.property⟩]
    · rw [if_pos ⟨subset_refl _, fun p hp => by simp at hp⟩]
    · intro w hw
      rw [if_neg]
      intro hh
      apply hw
      apply Subtype.ext
      symm
      apply YoungDiagram.ext
      apply Finset.eq_of_subset_of_card_le hh.1
      change w.val.card ≤ α.val.card
      rw [w.property, α.property]
      omega
  have := eq_of_transform d (fun α : DegreeShape d => sE α.val * hk k)
    (fun α => ∑ w : DegreeShape (d + k), if Horizontal α.val w.val then sE w.val else 0)
  refine congrFun (this ?_) α
  intro β
  simp only [← smul_mul_assoc, ← Finset.sum_mul, ← hE_expand]
  rw [hE_mul_hk β.val hpos]
  have hγ : (insShape β.val k).card = d + k := by rw [insShape_card, β.property]
  rw [hE_expand (d + k) ⟨insShape β.val k, hγ⟩]
  simp only [Finset.smul_sum, smul_ite, smul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  rw [K_apply, K_insShape d k hpos β w, Nat.cast_sum, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro α _
  rw [K_apply]
  split_ifs <;> simp

end Pieri

end

end OddMath.Frontier.OddLREven
