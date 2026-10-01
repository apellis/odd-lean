import OddMath.Frontier.EQPdgLimit
import OddMath.Frontier.EQPdgTheorem2

/-!
# Ellis–Qi, Theorem A.4 for the limit `Sym`

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
Appendix A.4.2, Theorem A.4, as printed: for the p-dg algebra `Sym` of symmetric functions over a
field `𝕜` of characteristic `p` (`SymLim 𝕜`, the limit of the `Sym_n`, with `d(x_i) = x_i²`),

1. `H_{/k}(Sym) = 0` for `k > 0` (`thmA4_1_pos_lim`), and `H_{/0}(Sym)` has basis the classes of
   the Schur functions `s_λ`, `λ` a `p`-Lima partition (`thmA4_1_zero_lim`);
2. the inclusion `𝕜[e_p^p, e_{2p}^p, e_{3p}^p, …] ↪ Sym` is a quasi-isomorphism of p-dg algebras
   (`thmA4_2_lim`, stated for the algebra map `𝕜[y_1, y_2, …] → Sym`, `y_j ↦ e_{jp}^p`, whose
   image is the subalgebra, `range_evELim`); the differential of the subalgebra is zero, and the
   subalgebra is a polynomial algebra on these generators (`evELim_injective`).

Partitions are Young diagrams; `IsPLimaYD p μ` says that `μ` is built out of `p × p` squares
(`μ_r = p ν_{⌊r/p⌋}`), which for `p = 2` is `EQLima.IsLima` (`isPLimaYD_two_iff`).

The proof deduces the statements from the versions in `n` variables (`EQPdgTheorem`,
`EQPdgTheorem2`): a class in `H_{/k}(Sym)` of degree `≤ D` is computed in `Sym_n` for `n ≥ D + p`,
because `Sym → Sym_n` is bijective in degrees `≤ n` and commutes with `d`
(`exists_eq_dLim_pow_add`).

For `p = 2` slash cohomology is ordinary cohomology (`slashDen_two`), and the theorem gives the
statement recalled in Appendix A.1: over a field of characteristic `2`, the cohomology ring
`H(Sym)` is a polynomial algebra on `e_2², e_4², e_6², …` (`cohomology_char_two`).
-/

namespace OddMath.Frontier.EQPdg

open MvPolynomial Finset
open OddMath.Frontier.EQLima (LengthLE rowExp rowExp_antitone rowExp_injective lengthLE_iff
  sum_rowExp rowLen_eq_of IsLima)

noncomputable section

/-! ## Classes in `H_{/0}` -/

section SlashGeneral

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V] (d : Module.End k V)
  (p : ℕ)

theorem slashClass_eq_iff {v w : V} (hv : (d ^ (0 + 1)) v = 0) (hw : (d ^ (0 + 1)) w = 0) :
    slashClass d p 0 v hv = slashClass d p 0 w hw ↔ v - w ∈ LinearMap.range (d ^ (p - 1)) := by
  rw [slashClass, slashClass, Submodule.Quotient.eq, Submodule.mem_comap, slashDen_zero]
  rfl

variable {ι : Type*} (v : ι → V) (hv : ∀ i, (d ^ (0 + 1)) (v i) = 0)

/-- The family of classes `[v_i] ∈ H_{/0}` is linearly independent iff no nontrivial combination
of the `v_i` lies in `Im(d^{p-1})`. -/
theorem linearIndependent_slashClass_iff :
    LinearIndependent k (fun i => slashClass d p 0 (v i) (hv i)) ↔
      ∀ c : ι →₀ k, Finsupp.linearCombination k v c ∈ LinearMap.range (d ^ (p - 1)) → c = 0 := by
  let w : ι → LinearMap.ker (d ^ (0 + 1)) := fun i => ⟨v i, hv i⟩
  have key : ∀ c : ι →₀ k,
      Finsupp.linearCombination k (fun i => slashClass d p 0 (v i) (hv i)) c = 0 ↔
        Finsupp.linearCombination k v c ∈ LinearMap.range (d ^ (p - 1)) := by
    intro c
    have e1 : (fun i => slashClass d p 0 (v i) (hv i)) =
        ((slashDen d p 0).comap (LinearMap.ker (d ^ (0 + 1))).subtype).mkQ ∘ w := rfl
    rw [e1, ← Finsupp.apply_linearCombination, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, slashDen_zero,
      Finsupp.apply_linearCombination]
    rfl
  rw [linearIndependent_iff]
  exact ⟨fun h c hc => h c ((key c).mpr hc), fun h c hc => h c ((key c).mp hc)⟩

/-- If the classes `[v_i]` span `H_{/0}`, every cocycle is a combination of the `v_i` modulo
`Im(d^{p-1})`. -/
theorem exists_mem_span_of_span_eq_top
    (hspan : Submodule.span k (Set.range fun i => slashClass d p 0 (v i) (hv i)) = ⊤) {f : V}
    (hf : (d ^ (0 + 1)) f = 0) :
    ∃ g : V, ∃ h ∈ Submodule.span k (Set.range v), f = (d ^ (p - 1)) g + h := by
  let w : ι → LinearMap.ker (d ^ (0 + 1)) := fun i => ⟨v i, hv i⟩
  have e1 : (fun i => slashClass d p 0 (v i) (hv i)) =
      ((slashDen d p 0).comap (LinearMap.ker (d ^ (0 + 1))).subtype).mkQ ∘ w := rfl
  have hx : slashClass d p 0 f hf ∈
      Submodule.span k (Set.range fun i => slashClass d p 0 (v i) (hv i)) := by
    rw [hspan]; exact Submodule.mem_top
  rw [e1, Set.range_comp, ← Submodule.map_span] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  rw [slashClass, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_comap,
    slashDen_zero] at hyx
  obtain ⟨g0, hg0⟩ := hyx
  refine ⟨-g0, y.1, ?_, ?_⟩
  · have h1 := Submodule.mem_map_of_mem (f := (LinearMap.ker (d ^ (0 + 1))).subtype) hy
    rw [Submodule.map_span, ← Set.range_comp] at h1
    exact h1
  · have h1 : (d ^ (p - 1)) g0 = y.1 - f := hg0
    rw [map_neg, h1]
    abel

/-- If every cocycle is a combination of the `v_i` modulo `Im(d^{p-1})`, the classes `[v_i]`
span `H_{/0}`. -/
theorem span_slashClass_eq_top
    (h : ∀ f : V, (d ^ (0 + 1)) f = 0 →
      ∃ g : V, ∃ h ∈ Submodule.span k (Set.range v), f = (d ^ (p - 1)) g + h) :
    Submodule.span k (Set.range fun i => slashClass d p 0 (v i) (hv i)) = ⊤ := by
  let w : ι → LinearMap.ker (d ^ (0 + 1)) := fun i => ⟨v i, hv i⟩
  have e1 : (fun i => slashClass d p 0 (v i) (hv i)) =
      ((slashDen d p 0).comap (LinearMap.ker (d ^ (0 + 1))).subtype).mkQ ∘ w := rfl
  rw [eq_top_iff]
  rintro x -
  induction x using Submodule.Quotient.induction_on with
  | H z =>
  obtain ⟨f, hf⟩ := z
  obtain ⟨g, h', hh', hfg⟩ := h f hf
  -- `h'` is a cocycle, and lifts to the span of the `w i`
  have e2 : Set.range v = (LinearMap.ker (d ^ (0 + 1))).subtype '' Set.range w := by
    rw [← Set.range_comp]; rfl
  rw [e2, ← Submodule.map_span] at hh'
  obtain ⟨y, hy, rfl⟩ := hh'
  have hcls : (Submodule.Quotient.mk ⟨f, hf⟩ :
      SlashCohomology d p 0) = Submodule.Quotient.mk y := by
    rw [Submodule.Quotient.eq, Submodule.mem_comap, slashDen_zero]
    refine ⟨g, ?_⟩
    change (d ^ (p - 1)) g = f - y.1
    rw [hfg]
    change (d ^ (p - 1)) g = (d ^ (p - 1)) g + y.1 - y.1
    abel
  rw [hcls, e1, Set.range_comp, ← Submodule.map_span]
  exact Submodule.mem_map_of_mem hy

end SlashGeneral

/-! ## `p`-Lima Young diagrams -/

section PLima

variable {n : ℕ}

/-- A Young diagram is `p`-Lima if it is built out of `p × p` squares:
`μ_r = p ν_{⌊r/p⌋}` for all rows `r`. -/
def IsPLimaYD (p : ℕ) (μ : YoungDiagram) : Prop := ∃ ν : ℕ → ℕ, ∀ r, μ.rowLen r = p * ν (r / p)

theorem lamExt_rowExp {μ : YoungDiagram} (h : LengthLE n μ) (r : ℕ) :
    lamExt (rowExp n μ) r = μ.rowLen r := by
  by_cases hr : r < n
  · rw [lamExt_lt _ hr]
    rfl
  · rw [lamExt_ge _ hr]
    symm
    by_contra hne
    have hmem : (r, 0) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero hne)
    exact hr (h _ hmem)

theorem isPLima_rowExp_iff (p : ℕ) {μ : YoungDiagram} (h : LengthLE n μ) :
    IsPLima p (rowExp n μ) ↔ IsPLimaYD p μ := by
  simp only [IsPLima, IsPLimaYD, lamExt_rowExp h]

/-- For `p = 2` the `p`-Lima partitions are the Lima partitions of Appendix A.1. -/
theorem isPLimaYD_two_iff (μ : YoungDiagram) : IsPLimaYD 2 μ ↔ IsLima μ := by
  constructor
  · rintro ⟨ν, hν⟩ k
    refine ⟨?_, ?_⟩
    · rw [hν]; exact even_two_mul _
    · rw [hν, hν]
      congr 2
      omega
  · intro h
    refine ⟨fun q => μ.rowLen (2 * q) / 2, fun r => ?_⟩
    obtain ⟨m, hm⟩ := (h (r / 2)).1
    have h2 := (h (r / 2)).2
    have hr : μ.rowLen r = μ.rowLen (2 * (r / 2)) := by
      rcases Nat.mod_two_eq_zero_or_one r with h0 | h1
      · exact congrArg μ.rowLen (by omega)
      · exact (congrArg μ.rowLen (by omega : r = 2 * (r / 2) + 1)).trans h2
    change μ.rowLen r = 2 * (μ.rowLen (2 * (r / 2)) / 2)
    rw [hr, hm]
    omega

/-- The cells of the diagram with row lengths `lam`. -/
def diagCells (lam : Fin n → ℕ) : Finset (ℕ × ℕ) :=
  (Finset.univ : Finset (Fin n)).biUnion fun i => (Finset.range (lam i)).image fun j => ((i : ℕ), j)

theorem mem_diagCells (lam : Fin n → ℕ) (c : ℕ × ℕ) :
    c ∈ diagCells lam ↔ ∃ h : c.1 < n, c.2 < lam ⟨c.1, h⟩ := by
  simp only [diagCells, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
    Finset.mem_range]
  constructor
  · rintro ⟨i, j, hj, rfl⟩
    exact ⟨i.2, hj⟩
  · rintro ⟨h, hc⟩
    exact ⟨⟨c.1, h⟩, c.2, hc, rfl⟩

/-- The Young diagram of a partition `λ_0 ≥ λ_1 ≥ ⋯ ≥ λ_{n-1}`. -/
def diagOf (lam : Fin n → ℕ) (h : Antitone lam) : YoungDiagram where
  cells := diagCells lam
  isLowerSet := by
    intro a b hba ha
    rw [Finset.mem_coe, mem_diagCells] at ha ⊢
    obtain ⟨h1, h2⟩ := ha
    have hb1 : b.1 ≤ a.1 := (Prod.le_def.mp hba).1
    have hb2 : b.2 ≤ a.2 := (Prod.le_def.mp hba).2
    refine ⟨lt_of_le_of_lt hb1 h1, lt_of_le_of_lt hb2 (lt_of_lt_of_le h2 (h ?_))⟩
    exact Fin.mk_le_mk.mpr hb1

theorem mem_diagOf (lam : Fin n → ℕ) (h : Antitone lam) (c : ℕ × ℕ) :
    c ∈ diagOf lam h ↔ ∃ h' : c.1 < n, c.2 < lam ⟨c.1, h'⟩ := by
  change c ∈ diagCells lam ↔ _
  exact mem_diagCells lam c

theorem lengthLE_diagOf (lam : Fin n → ℕ) (h : Antitone lam) : LengthLE n (diagOf lam h) :=
  fun c hc => by
    obtain ⟨h', -⟩ := (mem_diagOf lam h c).mp hc
    exact h'

theorem rowExp_diagOf (lam : Fin n → ℕ) (h : Antitone lam) : rowExp n (diagOf lam h) = lam := by
  funext i
  simp only [rowExp]
  apply rowLen_eq_of
  intro j
  rw [mem_diagOf]
  exact ⟨fun ⟨_, hj⟩ => hj, fun hj => ⟨i.2, hj⟩⟩

theorem isPLimaYD_diagOf (p : ℕ) {lam : Fin n → ℕ} (h : Antitone lam) (hl : IsPLima p lam) :
    IsPLimaYD p (diagOf lam h) := by
  rw [← isPLima_rowExp_iff p (lengthLE_diagOf lam h), rowExp_diagOf]
  exact hl

theorem card_diagOf (lam : Fin n → ℕ) (h : Antitone lam) : (diagOf lam h).card = ∑ i, lam i := by
  rw [← sum_rowExp (lengthLE_diagOf lam h), rowExp_diagOf]

/-- The index at level `n` of a `p`-Lima diagram with at most `n` rows (junk otherwise). -/
def rowIdx (p n : ℕ) (μ : {μ : YoungDiagram // IsPLimaYD p μ}) :
    {lam : Fin n → ℕ // Antitone lam ∧ IsPLima p lam} :=
  if h : LengthLE n μ.1 then
    ⟨rowExp n μ.1, rowExp_antitone n μ.1, (isPLima_rowExp_iff p h).mpr μ.2⟩
  else ⟨fun _ => 0, fun _ _ _ => le_rfl, ⟨fun _ => 0, fun r => by simp [lamExt]⟩⟩

theorem rowIdx_val (p : ℕ) {μ : {μ : YoungDiagram // IsPLimaYD p μ}} (h : LengthLE n μ.1) :
    (rowIdx p n μ).1 = rowExp n μ.1 := by
  simp only [rowIdx, h, ↓reduceDIte]

theorem rowIdx_injOn (p n : ℕ) :
    Set.InjOn (rowIdx p n) {μ : {μ : YoungDiagram // IsPLimaYD p μ} | LengthLE n μ.1} := by
  intro μ hμ ν hν h
  have h1 := congrArg Subtype.val h
  rw [rowIdx_val p hμ, rowIdx_val p hν] at h1
  exact Subtype.ext (rowExp_injective hμ hν h1)

end PLima

/-! ## The levels of `Sym` as p-complexes -/

section Levels

variable {k : Type*} [Field k] {n : ℕ}

/-- The projection `Sym → Sym_n` as a linear map. -/
def levelSym (n : ℕ) : SymLim k →ₗ[k] (SymSub : Submodule k (MvPolynomial (Fin n) k)) :=
  (level n).toLinearMap.codRestrict SymSub fun F => mem_SymSub.mpr (F.2.1 n)

theorem levelSym_coe (F : SymLim k) : (levelSym n F).1 = F.1 n := rfl

/-- The projections are morphisms of p-complexes. -/
theorem levelSym_comm (n : ℕ) :
    levelSym n ∘ₗ (dLim : Module.End k (SymLim k)) = dSym ∘ₗ levelSym n :=
  LinearMap.ext fun _ => Subtype.ext rfl

theorem levelSym_dLim_pow (m : ℕ) (F : SymLim k) :
    levelSym n ((dLim ^ m) F) = (dSym ^ m) (levelSym n F) :=
  comp_pow_of_comm dLim dSym (levelSym n) (levelSym_comm n) m F

theorem dSym_pow_coe (m : ℕ) (f : (SymSub : Submodule k (MvPolynomial (Fin n) k))) :
    ((dSym ^ m) f).1 = (pdL (Fin n) k ^ m) f.1 := by
  induction m generalizing f with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
    rfl

end Levels

/-! ## Theorem A.4 (1) -/

section Part1

variable {k : Type*} [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]

/-- **Ellis–Qi, Theorem A.4 (1), `H_{/j}(Sym) = 0` for `j > 0`.** -/
theorem thmA4_1_pos_lim (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ p - 2) :
    Subsingleton (SlashCohomology (dLim : Module.End k (SymLim k)) p j) := by
  have hp2 := hp.out.two_le
  rw [slashCohomology_subsingleton_iff]
  intro F hF
  rw [LinearMap.mem_ker] at hF
  obtain ⟨D, hD⟩ := F.2.2.2
  -- the statement at the level `D + p`
  have hFn : levelSym (D + p) F ∈ LinearMap.ker ((dSym (k := k) (n := D + p)) ^ (j + 1)) := by
    rw [LinearMap.mem_ker, ← levelSym_dLim_pow, hF, map_zero]
  have hsub := (slashCohomology_subsingleton_iff (dSym (k := k) (n := D + p)) p j).mp
    (thmA4_1_pos p j hj1 hj2) hFn
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hsub
  obtain ⟨g, rfl⟩ := hy
  rw [LinearMap.mem_ker] at hz
  -- lift `z`, truncated
  obtain ⟨H0, hH0⟩ := exists_level_eq (R := k) (mem_SymSub.mp z.2)
  have hFn' : F.1 (D + p) = (pdL (Fin (D + p)) k ^ (p - j - 1)) g.1 + z.1 := by
    have h := congrArg Subtype.val hyz
    rw [Submodule.coe_add, dSym_pow_coe] at h
    exact h.symm
  obtain ⟨G, hG⟩ := exists_eq_dLim_pow_add (H := truncLim (D + (p - j - 1)) H0) hD
    (fun i => totalDegree_trunc_le _ _) (by omega) (mem_SymSub.mp g.2) hFn'
    (by change trunc _ _ _ (H0.1 (D + p)) = _; rw [hH0])
  rw [hG]
  refine Submodule.add_mem_sup ⟨G, rfl⟩ ?_
  rw [LinearMap.mem_ker]
  refine eq_zero_of_level_eq_zero (n := D + p) (fun i => ?_) ?_
  · rw [dLim_pow_apply]
    have h1 : ((truncLim (D + (p - j - 1)) H0).1 i).totalDegree ≤ D + (p - j - 1) :=
      totalDegree_trunc_le _ _
    have h2 := totalDegree_pd_pow_le j ((truncLim (D + (p - j - 1)) H0).1 i)
    omega
  · rw [dLim_pow_apply]
    change (pdL (Fin (D + p)) k ^ j) (trunc (Fin (D + p)) k (D + (p - j - 1)) (H0.1 (D + p))) = 0
    rw [hH0, ← trunc_pd_pow, ← dSym_pow_coe, hz]
    simp

variable {p} in
/-- `d(s_μ) = 0` for a `p`-Lima partition `μ`. -/
theorem dLim_sLim_pLima {μ : YoungDiagram} (hμ : IsPLimaYD p μ) : dLim (sLim k μ) = 0 := by
  refine symLim_ext' fun n => ?_
  rw [level_dLim, level_sLim, map_zero]
  by_cases h : LengthLE n μ
  · rw [sFun_of_lengthLE h]
    have h1 := dSym_schurSym_pLima (k := k) p
      ⟨rowExp n μ, rowExp_antitone n μ, (isPLima_rowExp_iff p h).mpr hμ⟩
    have h2 := congrArg Subtype.val h1
    rw [dSym_pow_coe] at h2
    simp only [zero_add, pow_one] at h2
    exact h2
  · rw [sFun_of_not_lengthLE h, map_zero]

theorem sLim_mem_ker (μ : {μ : YoungDiagram // IsPLimaYD p μ}) :
    ((dLim : Module.End k (SymLim k)) ^ (0 + 1)) (sLim k μ.1) = 0 := by
  simpa using dLim_sLim_pLima (k := k) μ.2

/-- The classes of the `p`-Lima Schur polynomials span `H_{/0}(Sym_n)`. -/
theorem span_schurSym_eq_top (n : ℕ) :
    Submodule.span k (Set.range fun lam : {lam : Fin n → ℕ // Antitone lam ∧ IsPLima p lam} =>
      slashClass dSym p 0 (schurSym (k := k) lam.1) (dSym_schurSym_pLima p lam)) = ⊤ := by
  obtain ⟨b, hb⟩ := thmA4_1_zero (k := k) (n := n) p
  have e : (fun lam : {lam : Fin n → ℕ // Antitone lam ∧ IsPLima p lam} =>
      slashClass dSym p 0 (schurSym (k := k) lam.1) (dSym_schurSym_pLima p lam)) = b :=
    funext fun lam => (hb lam).symm
  rw [e, b.span_eq]

theorem linearIndependent_schurSym (n : ℕ) :
    LinearIndependent k (fun lam : {lam : Fin n → ℕ // Antitone lam ∧ IsPLima p lam} =>
      slashClass dSym p 0 (schurSym (k := k) lam.1) (dSym_schurSym_pLima p lam)) := by
  obtain ⟨b, hb⟩ := thmA4_1_zero (k := k) (n := n) p
  have e : (fun lam : {lam : Fin n → ℕ // Antitone lam ∧ IsPLima p lam} =>
      slashClass dSym p 0 (schurSym (k := k) lam.1) (dSym_schurSym_pLima p lam)) = b :=
    funext fun lam => (hb lam).symm
  rw [e]
  exact b.linearIndependent

omit hp [CharP k p] in
theorem levelSym_sLim_eq {n : ℕ} {μ : {μ : YoungDiagram // IsPLimaYD p μ}}
    (h : LengthLE n μ.1) : levelSym n (sLim k μ.1) = schurSym (rowIdx p n μ).1 := by
  apply Subtype.ext
  rw [rowIdx_val p h]
  exact sFun_of_lengthLE h

omit hp [CharP k p] in
/-- Lifting combinations of `p`-Lima Schur polynomials of `Sym_n` to `Sym`, truncated in degree
`≤ E`. -/
theorem exists_lift_trunc (E n : ℕ) {h : (SymSub : Submodule k (MvPolynomial (Fin n) k))}
    (hh : h ∈ Submodule.span k
      (Set.range fun lam : {lam : Fin n → ℕ // Antitone lam ∧ IsPLima p lam} =>
        schurSym (k := k) lam.1)) :
    ∃ H ∈ Submodule.span k (Set.range fun μ : {μ : YoungDiagram // IsPLimaYD p μ} => sLim k μ.1),
      (∀ i, (H.1 i).totalDegree ≤ E) ∧ H.1 n = trunc (Fin n) k E h.1 := by
  induction hh using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨lam, rfl⟩ := hx
    by_cases hE : ∑ i, lam.1 i ≤ E
    · refine ⟨sLim k (diagOf lam.1 lam.2.1), Submodule.subset_span
        ⟨⟨diagOf lam.1 lam.2.1, isPLimaYD_diagOf p lam.2.1 lam.2.2⟩, rfl⟩, fun i => ?_, ?_⟩
      · exact ((sFun_isHomogeneous _ i).totalDegree_le).trans
          ((card_diagOf lam.1 lam.2.1).le.trans hE)
      · change sFun k (diagOf lam.1 lam.2.1) n = trunc (Fin n) k E (schur lam.1)
        rw [sFun_of_lengthLE (lengthLE_diagOf lam.1 lam.2.1), rowExp_diagOf,
          trunc_of_isHomogeneous (schur_isHomogeneous lam.1)]
        simp only [hE, ↓reduceIte]
    · refine ⟨0, Submodule.zero_mem _, fun i => by simp, ?_⟩
      change (0 : MvPolynomial (Fin n) k) = trunc (Fin n) k E (schur lam.1)
      rw [trunc_of_isHomogeneous (schur_isHomogeneous lam.1)]
      simp only [hE, ↓reduceIte]
  | zero => exact ⟨0, Submodule.zero_mem _, fun i => by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨H1, h1, d1, e1⟩ := hx
    obtain ⟨H2, h2, d2, e2⟩ := hy
    refine ⟨H1 + H2, Submodule.add_mem _ h1 h2,
      fun i => (totalDegree_add _ _).trans (max_le (d1 i) (d2 i)), ?_⟩
    change H1.1 n + H2.1 n = trunc (Fin n) k E (x.1 + y.1)
    rw [map_add, e1, e2]
  | smul c x _ hx =>
    obtain ⟨H1, h1, d1, e1⟩ := hx
    refine ⟨c • H1, Submodule.smul_mem _ c h1,
      fun i => (totalDegree_smul_le c _).trans (d1 i), ?_⟩
    change c • H1.1 n = trunc (Fin n) k E (c • x.1)
    rw [map_smul, e1]

/-- Every cocycle of `Sym` is a combination of `p`-Lima Schur functions modulo `Im(d^{p-1})`. -/
theorem exists_sLim_decomp {F : SymLim k} (hF : dLim F = 0) :
    ∃ G : SymLim k, ∃ H ∈ Submodule.span k
      (Set.range fun μ : {μ : YoungDiagram // IsPLimaYD p μ} => sLim k μ.1),
      F = (dLim ^ (p - 1)) G + H := by
  have hp2 := hp.out.two_le
  obtain ⟨D, hD⟩ := F.2.2.2
  have hcoc : ((dSym (k := k) (n := D + p)) ^ (0 + 1)) (levelSym (D + p) F) = 0 := by
    rw [← levelSym_dLim_pow]
    simp [hF]
  obtain ⟨g, h, hh, hfg⟩ := exists_mem_span_of_span_eq_top (dSym (k := k) (n := D + p)) p
    (fun lam : {lam : Fin (D + p) → ℕ // Antitone lam ∧ IsPLima p lam} => schurSym lam.1)
    (dSym_schurSym_pLima p) (span_schurSym_eq_top p (D + p)) hcoc
  obtain ⟨H, hH, hdeg, hHn⟩ := exists_lift_trunc p (D + (p - 1)) (D + p) hh
  have hFn : F.1 (D + p) = (pdL (Fin (D + p)) k ^ (p - 1)) g.1 + h.1 := by
    have h1 := congrArg Subtype.val hfg
    rw [Submodule.coe_add, dSym_pow_coe] at h1
    exact h1
  obtain ⟨G, hG⟩ := exists_eq_dLim_pow_add (H := H) hD hdeg (by omega) (mem_SymSub.mp g.2)
    hFn hHn
  exact ⟨G, H, hH, hG⟩

/-- No nontrivial combination of `p`-Lima Schur functions lies in `Im(d^{p-1})`. -/
theorem sLim_independent (c : {μ : YoungDiagram // IsPLimaYD p μ} →₀ k)
    (hc : Finsupp.linearCombination k (fun μ : {μ : YoungDiagram // IsPLimaYD p μ} => sLim k μ.1) c ∈
      LinearMap.range ((dLim : Module.End k (SymLim k)) ^ (p - 1))) : c = 0 := by
  obtain ⟨G, hG⟩ := hc
  -- a level containing all partitions of the support
  obtain ⟨n, hn⟩ : ∃ n, ∀ μ ∈ c.support, LengthLE n μ.1 :=
    ⟨c.support.sup fun μ => μ.1.colLen 0, fun μ hμ => (lengthLE_iff _ μ.1).mpr
      (Finset.le_sup (f := fun μ : {μ : YoungDiagram // IsPLimaYD p μ} => μ.1.colLen 0) hμ)⟩
  have h1 := congrArg (levelSym n) hG
  rw [levelSym_dLim_pow, Finsupp.apply_linearCombination] at h1
  have h2 : Finsupp.linearCombination k
      (levelSym n ∘ fun μ : {μ : YoungDiagram // IsPLimaYD p μ} => sLim k μ.1) c =
      Finsupp.linearCombination k
        (fun lam : {lam : Fin n → ℕ // Antitone lam ∧ IsPLima p lam} => schurSym (k := k) lam.1)
        (c.mapDomain (rowIdx p n)) := by
    rw [Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply,
      Finsupp.linearCombination_apply]
    refine Finsupp.sum_congr fun μ hμ => ?_
    congr 1
    exact levelSym_sLim_eq p (hn μ hμ)
  have h3 := (linearIndependent_slashClass_iff (dSym (k := k) (n := n)) p _
    (dSym_schurSym_pLima p)).mp (linearIndependent_schurSym p n) (c.mapDomain (rowIdx p n))
    ⟨levelSym n G, h1.trans h2⟩
  have hinj : Set.InjOn (rowIdx p n) (c.support : Set {μ : YoungDiagram // IsPLimaYD p μ}) :=
    (rowIdx_injOn p n).mono fun μ hμ => hn μ (Finset.mem_coe.mp hμ)
  exact Finsupp.mapDomain_injOn _ hinj (Set.Subset.refl _) (by simp)
    (h3.trans Finsupp.mapDomain_zero.symm)

/-- **Ellis–Qi, Theorem A.4 (1), `H_{/0}(Sym)`**: the classes of the Schur functions `s_λ`, `λ` a
`p`-Lima partition, form a basis of `H_{/0}(Sym)`. -/
theorem thmA4_1_zero_lim :
    ∃ b : Module.Basis {μ : YoungDiagram // IsPLimaYD p μ} k
        (SlashCohomology (dLim : Module.End k (SymLim k)) p 0),
      ∀ μ, b μ = slashClass dLim p 0 (sLim k μ.1) (sLim_mem_ker p μ) := by
  have hli := (linearIndependent_slashClass_iff (dLim : Module.End k (SymLim k)) p
    (fun μ : {μ : YoungDiagram // IsPLimaYD p μ} => sLim k μ.1) (sLim_mem_ker p)).mpr
    (sLim_independent p)
  have hsp := span_slashClass_eq_top (dLim : Module.End k (SymLim k)) p
    (fun μ : {μ : YoungDiagram // IsPLimaYD p μ} => sLim k μ.1) (sLim_mem_ker p)
    fun F hF => exists_sLim_decomp p (by simpa using hF)
  exact ⟨Module.Basis.mk hli hsp.ge, fun μ => Module.Basis.mk_apply _ _ μ⟩

end Part1

/-! ## Theorem A.4 (2) -/

section Part2

variable {k : Type*} [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]

/-- The generator `e_{p(j+1)}^p ∈ Sym`, `j ≥ 0`. -/
def gLim (j : ℕ) : SymLim k := eLim k (p * (j + 1)) ^ p

/-- The algebra map `𝕜[y_1, y_2, …] → Sym`, `y_j ↦ e_{jp}^p`. -/
def evELim : MvPolynomial ℕ k →ₐ[k] SymLim k := aeval (gLim (k := k) p)

/-- The subalgebra `𝕜[e_p^p, e_{2p}^p, e_{3p}^p, …]` of `Sym`. -/
def algALim : Subalgebra k (SymLim k) := Algebra.adjoin k (Set.range (gLim (k := k) p))

omit hp [CharP k p] in
theorem mem_algALim_iff {a : SymLim k} : a ∈ algALim (k := k) p ↔ ∃ q, evELim p q = a := by
  rw [algALim, ← MvPolynomial.aeval_range]
  rfl

omit hp [CharP k p] in
theorem level_gLim (n j : ℕ) :
    level n (gLim (k := k) p j) = esymm (Fin n) k (p * (j + 1)) ^ p := by
  rw [gLim, map_pow, level_eLim]

omit hp [CharP k p] in
theorem level_evELim (n : ℕ) (q : MvPolynomial ℕ k) :
    level n (evELim (k := k) p q) =
      aeval (fun j : ℕ => esymm (Fin n) k (p * (j + 1)) ^ p) q := by
  rw [evELim, comp_aeval_apply]
  simp only [level_gLim]

omit hp in
theorem dLim_gLim (j : ℕ) : dLim (gLim (k := k) p j) = 0 := by
  refine symLim_ext' fun n => ?_
  rw [level_dLim, level_gLim, map_zero, Derivation.leibniz_pow,
    ← Nat.cast_smul_eq_nsmul (MvPolynomial (Fin n) k), CharP.cast_eq_zero, zero_smul]

omit hp in
/-- `d = 0` on `𝕜[e_p^p, e_{2p}^p, …]`. -/
theorem dLim_evELim (q : MvPolynomial ℕ k) : dLim (evELim (k := k) p q) = 0 := by
  induction q using MvPolynomial.induction_on with
  | C r =>
    rw [evELim, aeval_C]
    exact dLim_algebraMap r
  | add f g hf hg => rw [map_add, map_add, hf, hg, add_zero]
  | mul_X f i hf =>
    rw [map_mul, dLim_mul, hf, evELim, aeval_X, dLim_gLim, zero_mul, mul_zero, add_zero]

omit hp [CharP k p] in
/-- A monomial in the generators is homogeneous at every level. -/
theorem level_evELim_monomial_isHomogeneous (n : ℕ) (c : ℕ →₀ ℕ) (r : k) :
    (level n (evELim (k := k) p (monomial c r))).IsHomogeneous
      (∑ j ∈ c.support, p * (j + 1) * p * c j) := by
  rw [level_evELim, aeval_monomial, Finsupp.prod]
  rw [← zero_add (∑ j ∈ c.support, p * (j + 1) * p * c j)]
  refine IsHomogeneous.mul (isHomogeneous_C _ r) ?_
  exact IsHomogeneous.prod _ _ _ fun j _ => ((esymm_isHomogeneous (p * (j + 1))).pow p).pow (c j)

omit hp [CharP k p] in
/-- The subalgebra `𝕜[e_p^p, e_{2p}^p, …]` is stable under truncation. -/
theorem exists_evELim_eq_truncLim (E : ℕ) (q : MvPolynomial ℕ k) :
    ∃ q₁, truncLim E (evELim (k := k) p q) = evELim p q₁ := by
  induction q using MvPolynomial.induction_on' with
  | monomial c r =>
    by_cases hE : ∑ j ∈ c.support, p * (j + 1) * p * c j ≤ E
    · refine ⟨monomial c r, symLim_ext' fun n => ?_⟩
      rw [level_truncLim,
        trunc_of_isHomogeneous (level_evELim_monomial_isHomogeneous p n c r)]
      simp only [hE, ↓reduceIte]
    · refine ⟨0, symLim_ext' fun n => ?_⟩
      rw [level_truncLim,
        trunc_of_isHomogeneous (level_evELim_monomial_isHomogeneous p n c r)]
      simp only [hE, ↓reduceIte, map_zero]
  | add q1 q2 h1 h2 =>
    obtain ⟨a, ha⟩ := h1
    obtain ⟨b, hb⟩ := h2
    exact ⟨a + b, by rw [map_add, map_add, ha, hb, map_add]⟩

omit hp [CharP k p] in
/-- At the level `n`, `evELim` restricts to the map `evE` in `n` variables. -/
theorem level_evELim_rename {n N : ℕ} (hN : N ≤ n / p) (q : MvPolynomial (Fin N) k) :
    level n (evELim (k := k) p (rename Fin.val q)) = evE p (rename (Fin.castLE hN) q) := by
  have h : ((fun j : ℕ => esymm (Fin n) k (p * (j + 1)) ^ p) ∘ Fin.val : Fin N → _) =
      ePow p ∘ Fin.castLE hN := by
    funext j
    simp [ePow]
  rw [level_evELim, aeval_rename, evE, aeval_rename, h]

/-- Every cocycle of `Sym` is a polynomial in the `e_{jp}^p` modulo `Im(d^{p-1})`. -/
theorem exists_evELim_decomp {F : SymLim k} (hF : dLim F = 0) :
    ∃ (q : MvPolynomial ℕ k) (G : SymLim k), F = (dLim ^ (p - 1)) G + evELim p q := by
  have hp2 := hp.out.two_le
  obtain ⟨D, hD⟩ := F.2.2.2
  have hcoc : ((dSym (k := k) (n := D + p)) ^ (0 + 1)) (levelSym (D + p) F) = 0 := by
    rw [← levelSym_dLim_pow]
    simp [hF]
  obtain ⟨q', hq'⟩ := psiMap_surjective (k := k) (n := D + p) p
    (slashClass dSym p 0 (levelSym (D + p) F) hcoc)
  rw [psiMap_apply, slashClass_eq_iff] at hq'
  obtain ⟨g0, hg0⟩ := hq'
  have hFn : F.1 (D + p) = (pdL (Fin (D + p)) k ^ (p - 1)) (-g0).1 + evE p q' := by
    have h1 := congrArg Subtype.val hg0
    rw [dSym_pow_coe] at h1
    change (pdL (Fin (D + p)) k ^ (p - 1)) g0.1 = evE p q' - F.1 (D + p) at h1
    change F.1 (D + p) = (pdL (Fin (D + p)) k ^ (p - 1)) (-g0.1) + evE p q'
    rw [map_neg, h1]
    abel
  obtain ⟨q₁, hq₁⟩ := exists_evELim_eq_truncLim (k := k) p (D + (p - 1)) (rename Fin.val q')
  have hHn : (truncLim (D + (p - 1)) (evELim (k := k) p (rename Fin.val q'))).1 (D + p) =
      trunc (Fin (D + p)) k (D + (p - 1)) (evE p q') := by
    have hcast : (Fin.castLE (le_refl ((D + p) / p)) : Fin ((D + p) / p) → Fin ((D + p) / p)) =
        id := funext fun i => Fin.ext rfl
    change trunc (Fin (D + p)) k (D + (p - 1))
      (level (D + p) (evELim (k := k) p (rename Fin.val q'))) = _
    rw [level_evELim_rename p le_rfl, hcast, rename_id_apply]
  obtain ⟨G, hG⟩ := exists_eq_dLim_pow_add
    (H := truncLim (D + (p - 1)) (evELim (k := k) p (rename Fin.val q'))) hD
    (fun i => totalDegree_trunc_le _ _) (by omega) (mem_SymSub.mp (-g0).2) hFn hHn
  exact ⟨q₁, G, by rw [hG, hq₁]⟩

/-- A polynomial in the `e_{jp}^p` which lies in `Im(d^{p-1})` is zero. -/
theorem eq_zero_of_evELim_mem_range {q : MvPolynomial ℕ k}
    (hq : evELim (k := k) p q ∈ LinearMap.range ((dLim : Module.End k (SymLim k)) ^ (p - 1))) :
    q = 0 := by
  have hp0 := hp.out.pos
  obtain ⟨G, hG⟩ := hq
  -- `q` involves the variables `y_j`, `j < N`
  obtain ⟨N, hN⟩ : ∃ N, ∀ i ∈ q.vars, i < N :=
    ⟨q.vars.sup id + 1, fun i hi => Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)⟩
  obtain ⟨q', rfl⟩ := exists_rename_eq_of_vars_subset_range q (Fin.val : Fin N → ℕ)
    Fin.val_injective fun i hi => ⟨⟨i, hN i (Finset.mem_coe.mp hi)⟩, rfl⟩
  have hNle : N ≤ p * N / p := (Nat.mul_div_cancel_left N hp0).ge
  have h0 : psiMap (k := k) (n := p * N) p (rename (Fin.castLE hNle) q') = 0 := by
    rw [psiMap_apply, slashClass, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      slashDen_zero]
    refine ⟨levelSym (p * N) G, Subtype.ext ?_⟩
    rw [dSym_pow_coe]
    change (pdL (Fin (p * N)) k ^ (p - 1)) (G.1 (p * N)) = evE p (rename (Fin.castLE hNle) q')
    rw [← dLim_pow_apply, hG, ← level_evELim_rename p hNle q']
    rfl
  have h1 := psiMap_injective (k := k) (n := p * N) p (h0.trans (map_zero _).symm)
  have h2 := rename_injective _ (Fin.castLE_injective hNle) (h1.trans (map_zero _).symm)
  rw [h2, map_zero]

/-- `𝕜[e_p^p, e_{2p}^p, e_{3p}^p, …] ⊆ Sym` is a polynomial algebra: the generators are
algebraically independent. -/
theorem evELim_injective : Function.Injective (evELim (k := k) p) := by
  intro q q' h
  rw [← sub_eq_zero]
  apply eq_zero_of_evELim_mem_range p
  rw [map_sub, h, sub_self]
  exact Submodule.zero_mem _

omit hp [CharP k p] in
/-- The image of `𝕜[y_1, y_2, …] → Sym` is the subalgebra `𝕜[e_p^p, e_{2p}^p, …]`; since the map
is injective (`evELim_injective`), it identifies the polynomial algebra with this subalgebra. -/
theorem range_evELim : (evELim (k := k) p).range = algALim p := by
  rw [evELim, algALim, MvPolynomial.aeval_range]

omit hp in
/-- `𝕜[y_1, y_2, …] → Sym`, `y_j ↦ e_{jp}^p`, is a morphism of p-complexes when the source has
the zero differential. -/
theorem evELim_comm :
    (evELim (k := k) p).toLinearMap ∘ₗ 0 = dLim ∘ₗ (evELim (k := k) p).toLinearMap := by
  refine LinearMap.ext fun q => ?_
  rw [LinearMap.comp_zero, LinearMap.zero_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    dLim_evELim]

set_option synthInstance.maxHeartbeats 200000 in
/-- **Ellis–Qi, Theorem A.4 (2)**: the inclusion `𝕜[e_p^p, e_{2p}^p, e_{3p}^p, …] ↪ Sym` is a
quasi-isomorphism of p-dg algebras. Stated for the algebra map `𝕜[y_1, y_2, …] → Sym`,
`y_j ↦ e_{jp}^p`, which is an isomorphism onto `𝕜[e_p^p, e_{2p}^p, …]` (`evELim_injective`,
`range_evELim`) and commutes with the differentials (zero on the source, `evELim_comm`): it
induces isomorphisms on all slash cohomology groups `H_{/j}`, `0 ≤ j ≤ p - 2`. -/
theorem thmA4_2_lim :
    IsQuasiIso (0 : Module.End k (MvPolynomial ℕ k)) dLim (evELim (k := k) p).toLinearMap
      (evELim_comm p) p := by
  intro j hj
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · constructor
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro z hz
      induction z using Submodule.Quotient.induction_on with
      | H z =>
      obtain ⟨q, hz'⟩ := z
      rw [slashMap_mk, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, slashDen_zero] at hz
      have hz2 : evELim (k := k) p q ∈
          LinearMap.range ((dLim : Module.End k (SymLim k)) ^ (p - 1)) := hz
      have hq : q = 0 := eq_zero_of_evELim_mem_range p hz2
      subst hq
      have h0 : (⟨0, hz'⟩ : LinearMap.ker ((0 : Module.End k (MvPolynomial ℕ k)) ^ (0 + 1))) =
          0 := rfl
      rw [h0, Submodule.Quotient.mk_zero]
    · intro y
      induction y using Submodule.Quotient.induction_on with
      | H y =>
      obtain ⟨F, hF⟩ := y
      obtain ⟨q, G, hFq⟩ := exists_evELim_decomp p (F := F) (by simpa using hF)
      refine ⟨Submodule.Quotient.mk ⟨q, by simp⟩, ?_⟩
      rw [slashMap_mk, Submodule.Quotient.eq, Submodule.mem_comap, slashDen_zero]
      refine ⟨-G, ?_⟩
      change (dLim ^ (p - 1)) (-G) = evELim p q - F
      rw [map_neg, hFq]
      abel
  · have h1 : Subsingleton (SlashCohomology (0 : Module.End k (MvPolynomial ℕ k)) p j) := by
      rw [slashCohomology_subsingleton_iff]
      intro v _
      refine Submodule.mem_sup_right ?_
      rw [LinearMap.mem_ker, zero_pow (by omega), LinearMap.zero_apply]
    have h2 := thmA4_1_pos_lim (k := k) p j hj0 hj
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

end Part2

/-! ## Characteristic `2`: the cohomology ring of `Sym` -/

section CharTwo

variable {k : Type*} [Field k]

/-- For `p = 2` the only slash cohomology group is ordinary cohomology:
`H_{/0}(V) = Ker(d)/Im(d)`. -/
theorem slashDen_two {V : Type*} [AddCommGroup V] [Module k V] (d : Module.End k V) :
    slashDen d 2 0 = LinearMap.range d ∧
      LinearMap.ker (d ^ (0 + 1)) = LinearMap.ker d := by
  rw [slashDen_zero]
  simp

variable [CharP k 2]

theorem two_smul_symLim (F : SymLim k) : F + F = 0 := by
  rw [← two_smul k F]
  have h : (2 : k) = 0 := by
    have := CharP.cast_eq_zero k 2
    simpa using this
  rw [h, zero_smul]

/-- `Sym` over a field of characteristic `2` as a dg ring (the signs are trivial). -/
def symData : EQLima.SuperDG.Data (SymLim k) where
  D := (dLim : Module.End k (SymLim k)).toAddMonoidHom
  ι := RingHom.id _
  leibniz x y := dLim_mul x y
  sq x := by
    have h := LinearMap.congr_fun (dLim_pow_char (R := k) 2) x
    rw [pow_two, Module.End.mul_apply] at h
    exact h
  anti x := by
    change dLim x = -dLim x
    rw [eq_neg_iff_add_eq_zero]
    exact two_smul_symLim _
  invol _ := rfl

/-- The ring map `𝕜[y_1, y_2, …] → H(Sym)`, `y_j ↦ [e_{2j}²]`. -/
def cohomologyMap : MvPolynomial ℕ k →+* (symData (k := k)).H :=
  (symData (k := k)).cls.comp
    ((evELim (k := k) 2).toRingHom.codRestrict (symData (k := k)).cocycles
      fun q => dLim_evELim 2 q)

/-- **Appendix A.1, the characteristic 2 statement** (Elias–Qi): over a field of characteristic
`2`, the cohomology ring `H(Sym)` is the polynomial algebra on `e_2², e_4², e_6², …`. -/
theorem cohomology_char_two : Function.Bijective (cohomologyMap (k := k)) := by
  constructor
  · intro q q' h
    have h' : (symData (k := k)).cls ⟨evELim 2 q, dLim_evELim 2 q⟩ =
        (symData (k := k)).cls ⟨evELim 2 q', dLim_evELim 2 q'⟩ := h
    obtain ⟨w, hw⟩ := ((symData (k := k)).cls_eq_iff _ _).mp h'
    have hw' : dLim w = evELim (k := k) 2 q - evELim 2 q' := hw
    rw [← sub_eq_zero]
    apply eq_zero_of_evELim_mem_range 2
    refine ⟨w, ?_⟩
    rw [map_sub, ← hw']
    simp
  · intro x
    obtain ⟨z, rfl⟩ := (symData (k := k)).cls_surjective x
    obtain ⟨q, G, hG⟩ := exists_evELim_decomp (k := k) 2 (F := z.1) z.2
    have hG' : z.1 = dLim G + evELim 2 q := by simpa using hG
    refine ⟨q, ?_⟩
    have h' : cohomologyMap q = (symData (k := k)).cls ⟨evELim 2 q, dLim_evELim 2 q⟩ := rfl
    rw [h', (symData (k := k)).cls_eq_iff]
    refine ⟨-G, ?_⟩
    change dLim (-G) = evELim 2 q - z.1
    rw [hG', map_neg]
    abel

end CharTwo

end

end OddMath.Frontier.EQPdg
