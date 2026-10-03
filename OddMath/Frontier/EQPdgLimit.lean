import OddMath.Frontier.EQPdgLimitProj
import OddMath.Frontier.EQLimaAllRanks
import OddMath.Frontier.EQLimaLimit
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

/-!
# The p-dg algebra `Sym` of symmetric functions

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
Appendix A.4.2: "The map `d` is compatible with the inverse system `Sym_{n+1} → Sym_n`
(`x_{n+1} ↦ 0`), so there is an induced p-dg algebra structure on the limit `Sym`. This
differential acts on elementary, complete, and Schur functions as (A.5)–(A.7)."

* `SymLim R`: the ring of symmetric functions as the inverse limit of the graded rings
  `Sym_n = R[x_1, …, x_n]^{S_n}`: families `(F_n)_n` of symmetric polynomials with
  `F_{n+1}(x_1, …, x_n, 0) = F_n` and bounded total degree (a subalgebra of `∏_n R[x_1, …, x_n]`).
  `level n : SymLim R → R[x_1, …, x_n]` are the projections.
* `dLim`: the differential, acting levelwise by `d(x_i) = x_i²`; it is a derivation (`dLim_mul`)
  and `dLim ^ p = 0` in characteristic `p` (`dLim_pow_char`).
* `eLim R j`, `hLim R j`, `sLim R μ` (`μ` a Young diagram, `R` a domain): the elementary, complete
  and Schur functions; `sLim R μ` is `s_μ(x_1, …, x_n)` at the levels `n ≥ ℓ(μ)` and `0` below.
* (A.5) `dLim_eLim`: `d(e_j) = e_1 e_j - (j+1) e_{j+1}`; (A.6) `dLim_hLim`:
  `d(h_j) = (j+1) h_{j+1} - h_1 h_j` (both with the coefficient `j + 1` missing in the printed
  formulas, see `EQPdgPoly`); (A.7) `dLim_sLim`: `d(s_μ) = Σ_B ct(B) s_{μ + B}`, the sum over all
  addable boxes `B` of `μ`, with `ct(B)` the content (column minus row).
* `truncLim D`: the part of degree `≤ D`; `eq_zero_of_level_eq_zero`: an element of degree `≤ n`
  is determined by its level `n`; `exists_level_eq`: every level map is surjective onto `Sym_n`;
  `exists_eq_dLim_pow_add`: an identity `F_n = d^m(g) + h` at a level `n ≥ deg F + m` lifts to
  `Sym`.
-/

namespace OddMath.Frontier.EQPdg

open MvPolynomial Finset
open OddMath.Frontier.EQLima (LengthLE rowExp rowExp_antitone Addable addCell addableCells
  mem_addableCells addable_iff_rowLen addable_iff_antitone rowExp_addCell lengthLE_iff
  lengthLE_addCell lengthLE_of_addCell sum_rowExp)
open OddMath.SkewPolynomial (expSingle)

noncomputable section

/-! ## The limit ring -/

section Ring

variable (R : Type*) [CommRing R]

/-- **The ring `Sym` of symmetric functions**, the limit of the graded rings `Sym_n` along
`x_{n+1} ↦ 0`: compatible families of symmetric polynomials of bounded degree. -/
def SymLim : Subalgebra R (∀ n : ℕ, MvPolynomial (Fin n) R) where
  carrier := {F | (∀ n, (F n).IsSymmetric) ∧ (∀ n, proj R n (F (n + 1)) = F n) ∧
    ∃ D, ∀ n, (F n).totalDegree ≤ D}
  mul_mem' := by
    rintro F G ⟨hF1, hF2, D, hD⟩ ⟨hG1, hG2, E, hE⟩
    refine ⟨fun n => (hF1 n).mul (hG1 n), fun n => ?_, D + E, fun n => ?_⟩
    · rw [Pi.mul_apply, Pi.mul_apply, map_mul, hF2, hG2]
    · exact (totalDegree_mul _ _).trans (Nat.add_le_add (hD n) (hE n))
  one_mem' := ⟨fun _ => IsSymmetric.one, fun _ => map_one _, 0, fun _ => by simp⟩
  add_mem' := by
    rintro F G ⟨hF1, hF2, D, hD⟩ ⟨hG1, hG2, E, hE⟩
    refine ⟨fun n => (hF1 n).add (hG1 n), fun n => ?_, max D E, fun n => ?_⟩
    · rw [Pi.add_apply, Pi.add_apply, map_add, hF2, hG2]
    · exact (totalDegree_add _ _).trans (max_le_max (hD n) (hE n))
  zero_mem' := ⟨fun _ => IsSymmetric.zero, fun _ => map_zero _, 0, fun _ => by simp⟩
  algebraMap_mem' r := ⟨fun _ => IsSymmetric.C r, fun _ => proj_C r, 0, fun n => by
    rw [Pi.algebraMap_apply, MvPolynomial.algebraMap_eq, totalDegree_C]⟩

variable {R}

theorem symLim_ext {F G : SymLim R} (h : ∀ n, F.1 n = G.1 n) : F = G :=
  Subtype.ext (funext h)

/-- The projection `Sym → R[x_1, …, x_n]` (with image `Sym_n`, `exists_level_eq`). -/
def level (n : ℕ) : SymLim R →ₐ[R] MvPolynomial (Fin n) R :=
  (Pi.evalAlgHom R (fun n : ℕ => MvPolynomial (Fin n) R) n).comp (SymLim R).val

@[simp] theorem level_apply (n : ℕ) (F : SymLim R) : level n F = F.1 n := rfl

theorem symLim_ext' {F G : SymLim R} (h : ∀ n, level n F = level n G) : F = G :=
  symLim_ext h

theorem level_isSymmetric (n : ℕ) (F : SymLim R) : (level n F).IsSymmetric := F.2.1 n

theorem proj_level (n : ℕ) (F : SymLim R) : proj R n (level (n + 1) F) = level n F :=
  F.2.2.1 n

/-- The differential of `Sym`: levelwise the derivation `d(x_i) = x_i²`. -/
def dLim : Module.End R (SymLim R) where
  toFun F := ⟨fun n => pd (Fin n) R (F.1 n), fun n => pd_isSymmetric (F.2.1 n),
    fun n => (proj_pd (F.1 (n + 1))).trans (congrArg (pd (Fin n) R) (F.2.2.1 n)), by
      obtain ⟨D, hD⟩ := F.2.2.2
      exact ⟨D + 1, fun n => (totalDegree_pd_le _).trans (Nat.add_le_add_right (hD n) 1)⟩⟩
  map_add' F G := symLim_ext fun n => map_add (pd (Fin n) R) (F.1 n) (G.1 n)
  map_smul' c F := symLim_ext fun n => (pd (Fin n) R).map_smul c (F.1 n)

@[simp] theorem level_dLim (n : ℕ) (F : SymLim R) :
    level n (dLim F) = pd (Fin n) R (level n F) := rfl

theorem dLim_pow_apply (m : ℕ) (F : SymLim R) (n : ℕ) :
    ((dLim ^ m) F).1 n = (pdL (Fin n) R ^ m) (F.1 n) := by
  induction m generalizing F with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
    rfl

/-- `d` is a derivation of `Sym`. -/
theorem dLim_mul (F G : SymLim R) : dLim (F * G) = dLim F * G + F * dLim G := by
  refine symLim_ext' fun n => ?_
  simp only [level_dLim, map_mul, map_add, Derivation.leibniz, smul_eq_mul]
  ring

theorem dLim_algebraMap (r : R) : dLim (algebraMap R (SymLim R) r) = 0 :=
  symLim_ext fun n => (pd (Fin n) R).map_algebraMap r

/-- **`Sym` is a p-dg algebra**: `d^p = 0` in characteristic `p`. -/
theorem dLim_pow_char (p : ℕ) [Fact p.Prime] [CharP R p] :
    (dLim : Module.End R (SymLim R)) ^ p = 0 := by
  refine LinearMap.ext fun F => symLim_ext fun n => ?_
  rw [dLim_pow_apply, pd_pow_char]
  rfl

variable (R)

/-- The elementary symmetric function `e_j ∈ Sym`. -/
def eLim (j : ℕ) : SymLim R :=
  ⟨fun n => esymm (Fin n) R j, fun _ => esymm_isSymmetric _ _ _, fun n => proj_esymm n j, j,
    fun _ => (esymm_isHomogeneous j).totalDegree_le⟩

/-- The complete symmetric function `h_j ∈ Sym`. -/
def hLim (j : ℕ) : SymLim R :=
  ⟨fun n => hsymm (Fin n) R j, fun _ => hsymm_isSymmetric _ _ _, fun n => proj_hsymm n j, j,
    fun _ => (hsymm_isHomogeneous j).totalDegree_le⟩

variable {R}

@[simp] theorem level_eLim (n j : ℕ) : level n (eLim R j) = esymm (Fin n) R j := rfl

@[simp] theorem level_hLim (n j : ℕ) : level n (hLim R j) = hsymm (Fin n) R j := rfl

/-- **(A.5)** in `Sym` (corrected): `d(e_j) = e_1 e_j - (j+1) e_{j+1}`. -/
theorem dLim_eLim (j : ℕ) :
    dLim (eLim R j) = eLim R 1 * eLim R j - (j + 1) • eLim R (j + 1) := by
  refine symLim_ext' fun n => ?_
  simp only [level_dLim, map_sub, map_mul, map_nsmul, level_eLim]
  rw [pd_esymm, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

/-- **(A.6)** in `Sym` (corrected): `d(h_j) = (j+1) h_{j+1} - h_1 h_j`. -/
theorem dLim_hLim (j : ℕ) :
    dLim (hLim R j) = (j + 1) • hLim R (j + 1) - hLim R 1 * hLim R j := by
  refine symLim_ext' fun n => ?_
  simp only [level_dLim, map_sub, map_mul, map_nsmul, level_hLim]
  rw [pd_hsymm, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

end Ring

/-! ## Schur functions -/

section SchurFunctions

variable (R : Type*) [CommRing R] [IsDomain R]

/-- `s_μ(x_1, …, x_n)`: the Schur polynomial if `ℓ(μ) ≤ n`, and `0` otherwise. -/
def sFun (μ : YoungDiagram) (n : ℕ) : MvPolynomial (Fin n) R :=
  if LengthLE n μ then schur (rowExp n μ) else 0

variable {R}

theorem sFun_of_lengthLE {μ : YoungDiagram} {n : ℕ} (h : LengthLE n μ) :
    sFun R μ n = schur (rowExp n μ) := by
  simp only [sFun, h, ↓reduceIte]

theorem sFun_of_not_lengthLE {μ : YoungDiagram} {n : ℕ} (h : ¬ LengthLE n μ) :
    sFun R μ n = 0 := by
  simp only [sFun, h, ↓reduceIte]

theorem rowLen_eq_zero_iff (μ : YoungDiagram) (n : ℕ) : μ.rowLen n = 0 ↔ LengthLE n μ := by
  rw [lengthLE_iff, ← not_iff_not, not_le, ← YoungDiagram.mem_iff_lt_colLen,
    YoungDiagram.mem_iff_lt_rowLen]
  omega

theorem sFun_isSymmetric (μ : YoungDiagram) (n : ℕ) : (sFun R μ n).IsSymmetric := by
  by_cases h : LengthLE n μ
  · rw [sFun_of_lengthLE h]
    exact schurA_isSymmetric _
  · rw [sFun_of_not_lengthLE h]
    exact IsSymmetric.zero

/-- `s_μ` is homogeneous of degree `|μ|` at every level. -/
theorem sFun_isHomogeneous (μ : YoungDiagram) (n : ℕ) : (sFun R μ n).IsHomogeneous μ.card := by
  by_cases h : LengthLE n μ
  · rw [sFun_of_lengthLE h, ← sum_rowExp h]
    exact schur_isHomogeneous _
  · rw [sFun_of_not_lengthLE h]
    exact isHomogeneous_zero _ _ _

theorem proj_sFun (μ : YoungDiagram) (n : ℕ) : proj R n (sFun R μ (n + 1)) = sFun R μ n := by
  by_cases h1 : LengthLE n μ
  · have h2 : LengthLE (n + 1) μ := fun c hc => Nat.lt_succ_of_lt (h1 c hc)
    rw [sFun_of_lengthLE h1, sFun_of_lengthLE h2]
    exact proj_schur_of_last_eq_zero (lam := rowExp (n + 1) μ) ((rowLen_eq_zero_iff μ n).mpr h1)
  · rw [sFun_of_not_lengthLE h1]
    by_cases h2 : LengthLE (n + 1) μ
    · rw [sFun_of_lengthLE h2]
      exact proj_schur_of_last_ne_zero (lam := rowExp (n + 1) μ)
        fun h => h1 ((rowLen_eq_zero_iff μ n).mp h)
    · rw [sFun_of_not_lengthLE h2, map_zero]

variable (R)

/-- The Schur function `s_μ ∈ Sym`. -/
def sLim (μ : YoungDiagram) : SymLim R :=
  ⟨sFun R μ, fun n => sFun_isSymmetric μ n, fun n => proj_sFun μ n, μ.card,
    fun n => (sFun_isHomogeneous μ n).totalDegree_le⟩

variable {R}

@[simp] theorem level_sLim (n : ℕ) (μ : YoungDiagram) : level n (sLim R μ) = sFun R μ n := rfl

theorem expSingle_eq_single {n : ℕ} (i : Fin n) : expSingle i = Pi.single i 1 := by
  funext j
  simp [expSingle, Pi.single_apply, eq_comm]

theorem addableCells_filter_eq (n : ℕ) (μ : YoungDiagram) :
    (addableCells (fun _ => True) μ).filter (fun b => b.1 < n) =
      (univ.filter fun i : Fin n => Addable μ (i.val, μ.rowLen i)).map
        ⟨fun i : Fin n => (i.val, μ.rowLen i), fun _ _ h => Fin.ext (congrArg Prod.fst h)⟩ := by
  ext ⟨a, b⟩
  rw [Finset.mem_filter, mem_addableCells, Finset.mem_map]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk,
    Prod.mk.injEq]
  constructor
  · rintro ⟨hadd, ha⟩
    have hb := ((addable_iff_rowLen μ a b).mp hadd).1
    subst hb
    exact ⟨⟨a, ha⟩, hadd, rfl, rfl⟩
  · rintro ⟨i, hadd, rfl, rfl⟩
    exact ⟨hadd, i.2⟩

/-- **(A.7)** in `Sym`: `d(s_μ) = Σ_{B addable} ct(B) s_{μ + B}`, where `ct(B)` is the content
(column minus row) of the added box. -/
theorem dLim_sLim (μ : YoungDiagram) :
    dLim (sLim R μ) = ∑ b ∈ addableCells (fun _ => True) μ,
      ((b.2 : R) - (b.1 : R)) • sLim R (addCell μ b) := by
  refine symLim_ext' fun n => ?_
  rw [level_dLim, map_sum]
  simp only [map_smul, level_sLim]
  by_cases h : LengthLE n μ
  · rw [sFun_of_lengthLE h, pd_schur (rowExp_antitone n μ),
      ← Finset.sum_filter_add_sum_filter_not (addableCells (fun _ => True) μ) (fun b => b.1 < n),
      Finset.sum_eq_zero (s := (addableCells (fun _ => True) μ).filter fun b => ¬ b.1 < n),
      add_zero, addableCells_filter_eq, Finset.sum_map, Finset.sum_filter]
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Function.Embedding.coeFn_mk]
      by_cases hA : Addable μ (i.val, μ.rowLen i)
      · have hA' := (addable_iff_antitone μ i).mp hA
        rw [expSingle_eq_single] at hA'
        have hlen : LengthLE n (addCell μ (i.val, μ.rowLen i)) := lengthLE_addCell hA h i.2
        have hrow : rowExp n (addCell μ (i.val, μ.rowLen i)) = rowExp n μ + Pi.single i 1 := by
          rw [rowExp_addCell hA, expSingle_eq_single]
        simp only [hA', hA, ↓reduceIte, sFun_of_lengthLE hlen, hrow]
        rfl
      · have hA' : ¬ Antitone (rowExp n μ + Pi.single i 1) := fun h' =>
          hA ((addable_iff_antitone μ i).mpr (by rw [expSingle_eq_single]; exact h'))
        simp only [hA', hA, ↓reduceIte]
    · intro b hb
      obtain ⟨hb1, hb2⟩ := Finset.mem_filter.mp hb
      obtain ⟨-, hab⟩ := mem_addableCells.mp hb1
      rw [sFun_of_not_lengthLE fun h' => hb2 (lengthLE_of_addCell hab h').2, smul_zero]
  · rw [sFun_of_not_lengthLE h, map_zero]
    symm
    refine Finset.sum_eq_zero fun b hb => ?_
    obtain ⟨-, hab⟩ := mem_addableCells.mp hb
    rw [sFun_of_not_lengthLE fun h' => h (lengthLE_of_addCell hab h').1, smul_zero]

end SchurFunctions

/-! ## Truncation, lifting and descent -/

section Descent

variable {R : Type*} [CommRing R]

/-- The part of degree `≤ D` of a symmetric function. -/
def truncLim (D : ℕ) : SymLim R →ₗ[R] SymLim R where
  toFun F := ⟨fun n => trunc (Fin n) R D (F.1 n), fun n => trunc_isSymmetric D (F.2.1 n),
    fun n => (trunc_proj D (F.1 (n + 1))).symm.trans
      (congrArg (trunc (Fin n) R D) (F.2.2.1 n)), D, fun _ => totalDegree_trunc_le D _⟩
  map_add' F G := symLim_ext fun n => map_add (trunc (Fin n) R D) (F.1 n) (G.1 n)
  map_smul' c F := symLim_ext fun n => map_smul (trunc (Fin n) R D) c (F.1 n)

@[simp] theorem level_truncLim (D n : ℕ) (F : SymLim R) :
    level n (truncLim D F) = trunc (Fin n) R D (level n F) := rfl

theorem level_eq_zero_of_le {F : SymLim R} {m n : ℕ} (hmn : m ≤ n) (h : F.1 n = 0) :
    F.1 m = 0 := by
  induction n, hmn using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact ih (by rw [← F.2.2.1 n, h, map_zero])

/-- An element of `Sym` of degree `≤ n` is determined by its image in `Sym_n`. -/
theorem eq_zero_of_level_eq_zero {F : SymLim R} {n : ℕ} (hdeg : ∀ m, (F.1 m).totalDegree ≤ n)
    (h0 : F.1 n = 0) : F = 0 := by
  refine symLim_ext fun m => ?_
  change F.1 m = 0
  rcases le_total m n with hmn | hnm
  · exact level_eq_zero_of_le hmn h0
  · induction m, hnm using Nat.le_induction with
    | base => exact h0
    | succ m hm ih =>
      exact eq_zero_of_proj_eq_zero (F.2.1 (m + 1)) ((hdeg (m + 1)).trans hm)
        ((F.2.2.1 m).trans ih)

/-- The projection `Sym → Sym_n` is surjective. -/
theorem exists_level_eq {n : ℕ} {g : MvPolynomial (Fin n) R} (hg : g.IsSymmetric) :
    ∃ F : SymLim R, F.1 n = g := by
  obtain ⟨q, hq⟩ := esymmAlgHom_surjective (σ := Fin n) R (n := n) (by simp) ⟨g, hg⟩
  refine ⟨aeval (fun i : Fin n => eLim R ((i : ℕ) + 1)) q, ?_⟩
  have h := comp_aeval_apply (f := fun i : Fin n => eLim R ((i : ℕ) + 1)) (level n) q
  rw [level_apply] at h
  rw [h]
  have h2 := congrArg Subtype.val hq
  rw [esymmAlgHom_apply] at h2
  exact h2

/-- **Descent**: let `F ∈ Sym` have degree `≤ D` and `H ∈ Sym` degree `≤ D + m`. If at a level
`n ≥ D + m` we have `F_n = d^m(g) + h` with `g ∈ Sym_n` and `H_n` the part of degree `≤ D + m` of
`h`, then `F = d^m(G) + H` for some `G ∈ Sym`. -/
theorem exists_eq_dLim_pow_add {F H : SymLim R} {D m n : ℕ} (hF : ∀ i, (F.1 i).totalDegree ≤ D)
    (hH : ∀ i, (H.1 i).totalDegree ≤ D + m) (hn : D + m ≤ n) {g h : MvPolynomial (Fin n) R}
    (hg : g.IsSymmetric) (hFn : F.1 n = (pdL (Fin n) R ^ m) g + h)
    (hHn : H.1 n = trunc (Fin n) R (D + m) h) : ∃ G : SymLim R, F = (dLim ^ m) G + H := by
  obtain ⟨G0, hG0⟩ := exists_level_eq hg
  refine ⟨truncLim D G0, ?_⟩
  rw [← sub_eq_zero]
  refine eq_zero_of_level_eq_zero (n := n) (fun i => ?_) ?_
  · change (F.1 i - (((dLim ^ m) (truncLim D G0)).1 i + H.1 i)).totalDegree ≤ n
    rw [dLim_pow_apply]
    have h1 : ((pdL (Fin i) R ^ m) ((truncLim D G0).1 i)).totalDegree ≤ D + m :=
      (totalDegree_pd_pow_le m _).trans (Nat.add_le_add_right (totalDegree_trunc_le D _) m)
    exact (totalDegree_sub _ _).trans (max_le ((hF i).trans (by omega))
      ((totalDegree_add _ _).trans (max_le (h1.trans hn) ((hH i).trans hn))))
  · change F.1 n - (((dLim ^ m) (truncLim D G0)).1 n + H.1 n) = 0
    rw [dLim_pow_apply, hHn]
    change F.1 n - ((pdL (Fin n) R ^ m) (trunc (Fin n) R D (G0.1 n)) +
      trunc (Fin n) R (D + m) h) = 0
    rw [hG0, ← trunc_pd_pow, ← (trunc (Fin n) R (D + m)).map_add, ← hFn,
      trunc_of_totalDegree_le ((hF n).trans (Nat.le_add_right D m)), sub_self]

end Descent

end

end OddMath.Frontier.EQPdg
