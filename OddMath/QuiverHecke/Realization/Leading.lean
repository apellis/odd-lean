/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.Realization.Functor
import OddMath.QuiverHecke.Realization.CliffordModule
import OddMath.QuiverHecke.Spanning
import Categorification.TypeA.Inversions

/-!
# Leading terms of normal forms in the polynomial–Clifford representation

The normal form `x^u ψ_w` of the spanning theorem (`QuiverHecke.span_normalForms`) applied to
`1 ⊗ 1` on the identity permutation has, at the permutation `w`, an invertible operator applied
to `w(m_u)`, where `m_u` is the coefficient of the dots, and is otherwise supported on shorter
permutations (`lead`). This is the leading-term argument behind linear independence
(Kang–Kashiwara–Tsuchioka, arXiv:1107.1039v2, Corollary 3.15; Brundan–Ellis,
arXiv:1701.04133v2, §11).
-/

noncomputable section
open scoped TensorProduct
open Categorification.TypeA
namespace OddMath.QuiverHecke.Realization

universe u v
variable {I : Type u} {X : Type v} [AddCommGroup X] {k : Type*} [CommRing k]

/-! ## Permutations of `Fin n` as permutations of `ℕ` -/

/-- A permutation of `{0, …, n-1}`, extended by the identity. -/
def extN (n : ℕ) : Equiv.Perm (Fin n) →* Equiv.Perm ℕ :=
  Equiv.Perm.extendDomainHom (Fin.equivSubtype (n := n))

theorem extN_apply_lt {n : ℕ} (w : Equiv.Perm (Fin n)) {p : ℕ} (hp : p < n) :
    extN n w p = (w ⟨p, hp⟩ : ℕ) := by
  simp [extN, Equiv.Perm.extendDomain_apply_subtype, hp, Fin.equivSubtype]

theorem extN_apply_ge {n : ℕ} (w : Equiv.Perm (Fin n)) {p : ℕ} (hp : n ≤ p) : extN n w p = p := by
  simp [extN, Equiv.Perm.extendDomain_apply_not_subtype, show ¬ p < n by omega]

theorem extN_injective (n : ℕ) : Function.Injective (extN n) :=
  Equiv.Perm.extendDomainHom_injective _

theorem extN_sadj {n a : ℕ} (ha : a + 1 < n) : extN n (sadj n a) = sw a := by
  show _ = Equiv.swap a (a + 1)
  ext p
  by_cases hp : p < n
  · rw [extN_apply_lt _ hp]; simp only [sadj, ha, ↓reduceDIte]
    simp only [Equiv.swap_apply_def, Fin.ext_iff]
    split_ifs <;> simp_all
  · rw [extN_apply_ge _ (by omega), Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]

theorem desc_extN {n a : ℕ} (ha : a + 1 < n) (w : Equiv.Perm (Fin n)) :
    Desc a (extN n w) ↔ w⁻¹ ⟨a + 1, ha⟩ < w⁻¹ ⟨a, by omega⟩ := by
  rw [Desc, ← map_inv, extN_apply_lt _ ha, extN_apply_lt _ (by omega)]
  rfl

/-- A reduced word starts with an ascent. -/
theorem not_desc_of_isReduced {n a : ℕ} {ρ : List ℕ} (hr : IsReduced n (a :: ρ)) :
    ¬ Desc a (extN n (wordProd n ρ)) := by
  have ha : a + 1 < n := hr.1 a (by simp)
  intro hd
  rw [desc_extN ha] at hd
  have h₁ := length_sadj_mul_of_gt ha hd
  have h₂ := hr.2
  have h₃ := length_wordProd_le (m := n) (ρ := ρ) (fun x hx => hr.1 x (by simp [hx]))
  rw [wordProd_cons, List.length_cons] at h₂
  omega

theorem isReduced_tail {n a : ℕ} {ρ : List ℕ} (hr : IsReduced n (a :: ρ)) : IsReduced n ρ := by
  have hv : ValidWord n ρ := fun x hx => hr.1 x (by simp [hx])
  refine (isReduced_iff_length_le hv).mpr ?_
  have h₂ := hr.2
  have h₃ := length_sadj_mul_le (m := n) a (wordProd n ρ)
  rw [wordProd_cons, List.length_cons] at h₂
  omega

/-! ## Operators on a single component -/

section Single

theorem tw_sgl (a : ℕ) (r : Seq I → K k) (ν : Seq I) (m : M k) :
    tw a r (sgl ν m) = sgl (ν ∘ sw a) (twist a (r (ν ∘ sw a)) m) := by
  ext1 ν'
  rw [tw_apply]
  by_cases h : ν' = ν ∘ sw a
  · subst h; simp
  · have h' : ν' ∘ sw a ≠ ν := fun e => h (by rw [← e, comp_sw_sw])
    simp [h, h']

/-- The coefficient operator of `(c_a - c_{a+1})^{|i||j|}` on the component `ν`. -/
def drC (D : SKM.Datum I X) (i j : I) (a : ℕ) (ν : Seq I) : Module.End k (Coeff k) :=
  if D.parity i = 1 ∧ D.parity j = 1 then
    (if oddAt D.parity ν a then cliff a else 0) - (if oddAt D.parity ν (a + 1) then cliff (a + 1) else 0)
  else 1

theorem dres_eq_diag (D : SKM.Datum I X) (i j : I) (a : ℕ) :
    dres (k := k) D i j a = diag (drC D i j a) := by
  unfold dres drC
  split_ifs with h
  · rw [clif, clif, ← diag_sub]
  · exact diag_one.symm

variable (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

/-- The coefficient operator of a dot at position `p` on the component `ν`. -/
def dC (par : I → ZMod 2) (ν : Seq I) (p : ℕ) : Module.End k (Coeff k) :=
  if oddAt par ν p then cliff p * scalar (y p) else scalar (y p)

theorem dotOp_sgl {i : I} {p : ℕ} {ν : Seq I} (h : ν p = some i) (m : M k) :
    dotOp D i p (sgl ν m) = sgl ν (Finsupp.mapRange.linearMap (dC D.parity ν p) m) := by
  have ho := oddAt_iff (par := D.parity) h
  unfold dotOp dC
  by_cases hi : D.parity i = 1
  · simp only [hi, ho.mpr hi, ↓reduceIte]
    rw [clif, mulK, ← diag_mul', diag_single]
    simp [ho.mpr hi]
  · have hn : ¬ oddAt D.parity ν p := fun h' => hi (ho.mp h')
    simp only [hi, hn, ↓reduceIte]
    rw [mulK, diag_single]

variable [DecidableEq I]

theorem fpq_sgl (par : I → ZMod 2) (a : ℕ) (ν : Seq I) (m : M k) :
    fpq par a (a + 1) (sgl ν m) =
      sgl (ν ∘ sw a) (Finsupp.mapRange.linearMap (fP par a (a + 1) ν) m) := by
  rw [fpq_eq_diag, diag_single]
  by_cases h : ν a = ν (a + 1)
  · rw [comp_sw_of_eq h]
  · have : fP (k := k) par a (a + 1) ν = 0 := by simp [fP, h]
    simp [this]

theorem crossOp_sgl (i j : I) (a : ℕ) (ν : Seq I) (m : M k) :
    crossOp D Sc i j a (sgl ν m) = sgl (ν ∘ sw a) (gam (k := k) D i j • Finsupp.mapRange.linearMap
      (drC D i j a (ν ∘ sw a)) (twist a (cen D.parity (qt D Sc) a (a + 1) (ν ∘ sw a)) m +
        Finsupp.mapRange.linearMap (fP D.parity a (a + 1) ν) m)) := by
  rw [crossOp, LinearMap.smul_apply, Module.End.mul_apply, sig, LinearMap.add_apply, tw_sgl,
    fpq_sgl, ← Pi.single_add, dres_eq_diag, diag_single, ← Pi.single_smul]

end Single

/-! ## Invertible factors -/

theorem isUnit_smul_end {E : Type*} [AddCommGroup E] [Module k E] {c : k} (hc : IsUnit c)
    {A : Module.End k E} (hA : IsUnit A) : IsUnit (c • A) := by
  rw [Algebra.smul_def]
  exact (hc.map (algebraMap k (Module.End k E))).mul hA

theorem isUnit_perm (σ : Equiv.Perm ℕ) : IsUnit (perm (k := k) σ) := by
  refine (Units.mk (perm σ) (perm σ⁻¹) ?_ ?_).isUnit
  · rw [← perm_mul, mul_inv_cancel, perm_one]
  · rw [← perm_mul, inv_mul_cancel, perm_one]

theorem perm_injective (σ : Equiv.Perm ℕ) : Function.Injective (perm (k := k) σ) := by
  have key : ∀ z, perm σ⁻¹ (perm (k := k) σ z) = z := fun z => by
    rw [← Module.End.mul_apply, ← perm_mul, inv_mul_cancel, perm_one]; rfl
  intro x x' h
  rw [← key x, h, key]

theorem isUnit_gam [DecidableEq I] (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (i j : I) :
    IsUnit (gam (k := k) D i j) := by
  unfold gam
  split_ifs with h
  · obtain ⟨u, hu⟩ := Sc.two_isUnit ⟨i, h.2⟩
    rw [half, ← hu, Ring.inverse_unit]
    exact (Units.isUnit _).neg
  · exact isUnit_one

theorem isUnit_drC (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (i j : I) (a : ℕ) (ν : Seq I)
    (ha : ν a = some j) (ha' : ν (a + 1) = some i) : IsUnit (drC (k := k) D i j a ν) := by
  unfold drC
  by_cases h : D.parity i = 1 ∧ D.parity j = 1
  · simp only [h, (oddAt_iff ha).mpr h.2, (oddAt_iff ha').mpr h.1, and_self, ↓reduceIte]
    obtain ⟨u, hu⟩ := Sc.two_isUnit ⟨i, h.1⟩
    have hsq : (cliff (k := k) a - cliff (a + 1)) * (cliff a - cliff (a + 1)) =
        (u : k) • (1 : Module.End k (Coeff k)) := by
      have e1 : ∀ x, cliff a (cliff (k := k) a x) = x := fun x => by
        simpa using LinearMap.congr_fun (cliff_mul_self (k := k) a) x
      have e2 : ∀ x, cliff (a + 1) (cliff (k := k) (a + 1) x) = x := fun x => by
        simpa using LinearMap.congr_fun (cliff_mul_self (k := k) (a + 1)) x
      have e3 : ∀ x, cliff a (cliff (k := k) (a + 1) x) = -cliff (a + 1) (cliff a x) := fun x => by
        simpa using LinearMap.congr_fun (cliff_anticomm (k := k) (p := a) (q := a + 1) (by omega)) x
      refine LinearMap.ext fun x => ?_
      simp only [Module.End.mul_apply, LinearMap.sub_apply, map_sub, e1, e2, e3, hu]
      rw [LinearMap.smul_apply, Module.End.one_apply, two_smul]
      abel
    refine (Units.mk _ ((↑u⁻¹ : k) • (cliff (k := k) a - cliff (a + 1))) ?_ ?_).isUnit
    · rw [mul_smul_comm, hsq, smul_smul, Units.inv_mul, one_smul]
    · rw [smul_mul_assoc, hsq, smul_smul, Units.inv_mul, one_smul]
  · simp only [h, ↓reduceIte]; exact isUnit_one

/-! ## Words -/

theorem twist_apply_sw (a : ℕ) (r : K k) (m : M k) (v : Equiv.Perm ℕ) :
    twist a r m (sw a * v) = scalar (epow a v r) (perm (sw a) (m v)) := by
  classical
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add m m' hm hm' => simp [hm, hm']
  | single w x =>
    rw [twist_single, Finsupp.single_apply, Finsupp.single_apply]
    by_cases h : w = v
    · subst h; simp
    · have : sw a * w ≠ sw a * v := fun e => h (mul_left_cancel e)
      simp [h, this]

theorem seqOf_act_cross {u : List I} {a : ℕ} (ha : a + 1 < u.length) :
    seqOf ((PG.cross a).act u) = seqOf u ∘ sw a := by
  obtain ⟨x, y, hx⟩ : ∃ x y, u.drop a = x :: y :: u.drop (a + 2) := by
    refine ⟨u[a], u[a + 1], ?_⟩
    rw [List.drop_eq_getElem_cons, List.drop_eq_getElem_cons]
  have hu : u = u.take a ++ [x, y] ++ u.drop (a + 2) := by
    conv_lhs => rw [← List.take_append_drop a u, hx]
    simp
  have hl : (u.take a).length = a := by simp; omega
  have e : (PG.cross a).act u = u.take a ++ [y, x] ++ u.drop (a + 2) := by
    simp only [PG.act, hx]; simp
  rw [e]
  conv_rhs => rw [hu, ← seqOf_swap (u.take a) (u.drop (a + 2)) x y]
  rw [hl, Function.comp_assoc]
  ext1 p; simp

theorem ld_cross {u : List I} {a : ℕ} (ha : a + 1 < u.length) :
    (PG.cross a).ld u = [(u.take a, Shape.cross u[a] u[a + 1], u.drop (a + 2))] := by
  simp only [PG.ld]
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons ha]

theorem ld_dot {u : List I} {p : ℕ} (hp : p < u.length) :
    (PG.dot p).ld u = [(u.take p, Shape.dot u[p], u.drop (p + 1))] := by
  simp only [PG.ld]
  rw [List.drop_eq_getElem_cons hp]

variable [DecidableEq I] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

theorem ldList_cross {u : List I} {a : ℕ} (ha : a + 1 < u.length) :
    ldList D Sc 0 ((PG.cross a).ld u) = crossOp D Sc u[a] u[a + 1] a := by
  simp only [ld_cross ha, ldList, one_mul, ldOp]
  simp [Nat.min_eq_left (show a ≤ u.length by omega)]

theorem ldList_dot {u : List I} {p : ℕ} (hp : p < u.length) :
    ldList D Sc 0 ((PG.dot p).ld u) = dotOp D u[p] p := by
  simp only [ld_dot hp, ldList, one_mul, ldOp]
  simp [Nat.min_eq_left hp.le]

/-- The coefficient operator of the dots on the strands `l`, the first one acting first. -/
def mdC (par : I → ZMod 2) (ν : Seq I) : List ℕ → Module.End k (Coeff k)
  | [] => 1
  | p :: l => mdC par ν l * dC par ν p

theorem ldList_dots (t : List I) (l : List ℕ) (hl : ∀ p ∈ l, p < t.length) (m : M k) :
    ldList D Sc 0 (pl t (l.map PG.dot)) (sgl (seqOf t) m) =
      sgl (seqOf t) (Finsupp.mapRange.linearMap (mdC D.parity (seqOf t) l) m) := by
  induction l generalizing m with
  | nil => ext1 ν; simp [ldList, mdC]
  | cons p l ih =>
    have hp : p < t.length := hl p (by simp)
    rw [List.map_cons, pl_cons, show (PG.dot p).act t = t from rfl, ldList_append,
      Module.End.mul_apply, ldList_dot D Sc hp, dotOp_sgl D (by simp [seqOf, hp]), ih (fun q hq => hl q (by simp [hq]))]
    congr 1
    ext w; simp [mdC]

/-! ## The leading term of a reduced crossing word -/

/-- **Leading term.** For a reduced word `ρ` of `w`, the crossings `ψ_ρ` applied to `x` at the
identity permutation give, at `w`, an invertible operator `G` (independent of `x`) applied to
`w(x)`; all other permutations in the result are shorter than `w`. -/
theorem lead (t : List I) {ρ : List ℕ} (hr : IsReduced t.length ρ) :
    ∃ G : Module.End k (Coeff k), IsUnit G ∧ ∀ x : Coeff k, ∃ m : M k,
      ldList D Sc 0 (pl t (cw ρ)) (sgl (seqOf t) (Finsupp.single 1 x)) =
          sgl (seqOf (tgt t (cw ρ))) m ∧
        m (extN t.length (wordProd t.length ρ)) = G (perm (extN t.length (wordProd t.length ρ)) x) ∧
        ∀ v, m v ≠ 0 → v = extN t.length (wordProd t.length ρ) ∨
          ∃ u, v = extN t.length u ∧ length t.length u < ρ.length := by
  classical
  induction ρ with
  | nil =>
    refine ⟨1, isUnit_one, fun x => ⟨Finsupp.single 1 x, by simp [ldList], by simp, fun v hv => ?_⟩⟩
    left
    by_contra h
    have h' : (1 : Equiv.Perm ℕ) ≠ v := fun e => h (by simp [← e])
    exact hv (by simp [h'])
  | cons a ρ ih =>
    have hr' := isReduced_tail hr
    obtain ⟨G', hG', hx⟩ := ih hr'
    have ha : a + 1 < t.length := hr.1 a (by simp)
    have hasc := not_desc_of_isReduced hr
    set w' := wordProd t.length ρ with hw'
    have hlen : length t.length (sadj t.length a * w') = ρ.length + 1 := by
      have := hr.2; rw [wordProd_cons, List.length_cons, ← hw'] at this; omega
    have hW : extN t.length (wordProd t.length (a :: ρ)) = sw a * extN t.length w' := by
      rw [wordProd_cons, map_mul, extN_sadj ha]
    set t₁ := tgt t (cw ρ) with ht₁
    have ha₁ : a + 1 < t₁.length := by simp [t₁, ha]
    set i := t₁[a]
    set j := t₁[a + 1]
    set ν' := seqOf t₁ ∘ sw a
    have hν'a : ν' a = some j := by simp [ν', seqOf, j]
    have hν'a' : ν' (a + 1) = some i := by simp [ν', seqOf, i]
    refine ⟨gam D i j • (drC D i j a ν' * perm (sw a) * G' * perm (sw a)),
      isUnit_smul_end (isUnit_gam D Sc i j) ((((isUnit_drC D Sc i j a ν' hν'a hν'a').mul
        (isUnit_perm _)).mul hG').mul (isUnit_perm _)), fun x => ?_⟩
    obtain ⟨m', e', hm1, hm2⟩ := hx x
    set r := cen D.parity (qt D Sc) a (a + 1) ν'
    refine ⟨gam (k := k) D i j • Finsupp.mapRange.linearMap (drC D i j a ν')
      (twist a r m' + Finsupp.mapRange.linearMap (fP D.parity a (a + 1) (seqOf t₁)) m'), ?_, ?_, ?_⟩
    · rw [cw_cons, pl_append, ldList_append, Module.End.mul_apply, e', tgt_append, ← ht₁,
        pl_cons, pl_nil, List.append_nil, ldList_cross D Sc ha₁, crossOp_sgl, tgt_cons, tgt_nil,
        seqOf_act_cross ha₁]
    · have hm0 : m' (sw a * extN t.length w') = 0 := by
        by_contra hne
        rcases hm2 _ hne with h | ⟨u, hu, hl⟩
        · have : sw a = 1 := mul_right_cancel (h.trans (one_mul _).symm)
          have := congrArg (fun σ : Equiv.Perm ℕ => σ a) this
          simp [sw] at this
        · rw [← extN_sadj ha, ← map_mul] at hu
          rw [← extN_injective _ hu] at hl
          omega
      have hep : epow a (extN t.length w') r = 1 := by simp [epow, hasc]
      rw [hW, Finsupp.smul_apply, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply,
        Finsupp.add_apply, twist_apply_sw, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply,
        hm0, map_zero, add_zero, hep, scalar_one, Module.End.one_apply, hm1]
      simp only [LinearMap.smul_apply, Module.End.mul_apply]
      congr 4
      rw [← Module.End.mul_apply, ← perm_mul, ← mul_assoc, sw_mul_self, one_mul]
    · intro v hv
      have hor : m' (sw a * v) ≠ 0 ∨ m' v ≠ 0 := by
        by_contra hno
        simp only [not_or, ne_eq, not_not] at hno
        apply hv
        have e : v = sw a * (sw a * v) := by rw [← mul_assoc, sw_mul_self, one_mul]
        rw [Finsupp.smul_apply, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply,
          Finsupp.add_apply, e, twist_apply_sw, ← e, hno.1, Finsupp.mapRange.linearMap_apply,
          Finsupp.mapRange_apply, hno.2]
        simp
      rcases hor with h | h
      · rcases hm2 _ h with h' | ⟨u, hu, hl⟩
        · left
          rw [hW, ← h', ← mul_assoc, sw_mul_self, one_mul]
        · right
          refine ⟨sadj t.length a * u, ?_, ?_⟩
          · rw [map_mul, extN_sadj ha, ← hu, ← mul_assoc, sw_mul_self, one_mul]
          · have := length_sadj_mul_le (m := t.length) a u
            simp only [List.length_cons]; omega
      · rcases hm2 _ h with h' | ⟨u, hu, hl⟩
        · right
          refine ⟨w', h', ?_⟩
          have := hr'.2
          rw [← hw'] at this
          simp only [List.length_cons]; omega
        · right
          exact ⟨u, hu, by simp only [List.length_cons]; omega⟩

/-! ## The coefficients of the dots -/

/-- `∏_{p ∈ L} y_p`. -/
def Yl (L : List ℕ) : K k := (L.map y).prod

theorem reflect_Yl (p : ℕ) (L : List ℕ) :
    ∃ ε : k, IsUnit ε ∧ reflect p (Yl (k := k) L) = ε • Yl L := by
  induction L with
  | nil => exact ⟨1, isUnit_one, by simp [Yl]⟩
  | cons q L ih =>
    obtain ⟨ε, hε, h⟩ := ih
    have hq : reflect (k := k) p (y q) = (if q = p then -1 else 1 : k) • y q := by
      by_cases hqp : q = p
      · subst hqp; simp
      · simp [reflect_y_of_ne hqp, hqp]
    refine ⟨(if q = p then -1 else 1 : k) * ε, ?_, ?_⟩
    · exact (by split_ifs <;> simp : IsUnit (if q = p then -1 else 1 : k)).mul hε
    · simp only [Yl, List.map_cons, List.prod_cons, map_mul] at h ⊢
      rw [hq, h, smul_mul_smul_comm, mul_comm (if q = p then -1 else 1 : k)]

/-- The finite set of odd strands carrying an odd number of dots, toggled along `l`. -/
def oddSetFrom (par : I → ZMod 2) (ν : Seq I) : List ℕ → Finset ℕ → Finset ℕ
  | [], S => S
  | p :: l, S => oddSetFrom par ν l (if oddAt par ν p then tog p S else S)

omit [DecidableEq I] in
theorem coord_mdC (par : I → ZMod 2) (ν : Seq I) (l : List ℕ) :
    ∀ (x : Coeff k) (S₀ : Finset ℕ) (L : List ℕ) (e : k), IsUnit e →
      (∀ S, coord S x = if S = S₀ then e • Yl L else 0) →
      ∃ e' : k, IsUnit e' ∧ ∀ S, coord S (mdC par ν l x) =
        if S = oddSetFrom par ν l S₀ then e' • Yl (L ++ l) else 0 := by
  induction l with
  | nil => intro x S₀ L e he hx; exact ⟨e, he, by simpa [mdC, oddSetFrom] using hx⟩
  | cons p l ih =>
    intro x S₀ L e he hx
    rw [show L ++ p :: l = (L ++ [p]) ++ l by simp]
    simp only [mdC, Module.End.mul_apply, oddSetFrom]
    unfold dC
    by_cases ho : oddAt par ν p
    · simp only [ho, ↓reduceIte, Module.End.mul_apply]
      obtain ⟨ε, hε, hr⟩ := reflect_Yl (k := k) p L
      refine ih _ _ _ (-(sgn p S₀ * e * ε)) (((isUnit_sgn p S₀).mul he).mul hε).neg fun S => ?_
      rw [coord_cliff, coord_scalar, hx]
      by_cases hS : S = tog p S₀
      · subst hS
        simp only [tog_tog, ↓reduceIte, map_mul, map_smul, hr, reflect_y_self]
        have hY : Yl (k := k) (L ++ [p]) = Yl L * y p := by simp [Yl]
        rw [hY]
        simp only [Algebra.smul_def, map_mul, map_neg]
        ring
      · have : tog p S ≠ S₀ := fun e => hS (by rw [← e, tog_tog])
        simp [this, hS]
    · simp only [ho, ↓reduceIte]
      refine ih _ _ _ e he fun S => ?_
      rw [coord_scalar, hx]
      split_ifs
      · simp [Yl, mul_comm]
      · simp

theorem coord_one_tmul (S : Finset ℕ) :
    coord S ((1 : K k) ⊗ₜ[k] (1 : Cl k)) = if S = ∅ then (1 : k) • Yl [] else 0 := by
  rw [coord_tmul, vac_one, Finsupp.single_apply]
  by_cases h : S = ∅ <;> simp [h, Yl, eq_comm]

theorem Yl_eq (L : List ℕ) :
    Yl (k := k) L = algebraMap (P k) (K k)
      (MvPolynomial.monomial (Multiset.toFinsupp (L : Multiset ℕ)) 1) := by
  induction L with
  | nil => simp [Yl]
  | cons p L ih =>
    rw [Yl, List.map_cons, List.prod_cons, ← Yl, ih, y, ← map_mul, ← Multiset.cons_coe,
      ← Multiset.singleton_add, Multiset.toFinsupp_add, Multiset.toFinsupp_singleton,
      MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul]

omit [DecidableEq I] in
/-- The dot coefficients `m_l = x^l (1 ⊗ 1)` of distinct increasing lists of strands are
linearly independent. -/
theorem mdC_independent {ι : Type*} (par : I → ZMod 2) (ν : Seq I) (s : Finset ι)
    (L : ι → List ℕ) (hinj : Set.InjOn L s) (hs : ∀ l ∈ s, (L l).Pairwise (· ≤ ·)) (c : ι → k)
    (h : ∑ l ∈ s, c l • mdC par ν (L l) ((1 : K k) ⊗ₜ[k] (1 : Cl k)) = 0) :
    ∀ l ∈ s, c l = 0 := by
  classical
  have hco : ∀ l, ∃ e : k, IsUnit e ∧ ∀ S, coord S (mdC par ν l ((1 : K k) ⊗ₜ[k] (1 : Cl k))) =
      if S = oddSetFrom par ν l ∅ then e • Yl l else 0 := fun l => by
    simpa using coord_mdC par ν l _ ∅ [] 1 isUnit_one coord_one_tmul
  choose e he hco using hco
  intro l₀ hl₀
  have h1 := congrArg (coord (oddSetFrom par ν (L l₀) ∅)) h
  rw [map_sum, map_zero] at h1
  simp only [map_smul, hco] at h1
  have h2 : algebraMap (P k) (K k) (∑ l ∈ s, (if oddSetFrom par ν (L l₀) ∅ = oddSetFrom par ν (L l) ∅
      then c l * e (L l) else 0) • MvPolynomial.monomial (Multiset.toFinsupp (L l : Multiset ℕ)) 1) =
        algebraMap (P k) (K k) 0 := by
    rw [map_zero, ← h1, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs
    · rw [Yl_eq, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, smul_smul,
        Algebra.smul_def (c l * e (L l)), map_mul]
    · simp
  have h3 := IsFractionRing.injective (P k) (K k) h2
  have h4 := congrArg (fun q : P k => q.coeff (Multiset.toFinsupp (L l₀ : Multiset ℕ))) h3
  rw [MvPolynomial.coeff_sum, Finset.sum_eq_single l₀] at h4
  · simp [MvPolynomial.coeff_monomial] at h4
    exact (he (L l₀)).mul_left_eq_zero.mp h4
  · intro l hl hne
    have hd : Multiset.toFinsupp (L l : Multiset ℕ) ≠ Multiset.toFinsupp (L l₀ : Multiset ℕ) :=
      fun heq => hne (hinj hl hl₀ ((Multiset.coe_eq_coe.mp
        (Multiset.toFinsupp.injective heq)).eq_of_pairwise' (hs l hl) (hs l₀ hl₀)))
    simp only [MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial, hd, ↓reduceIte, smul_zero]
  · intro h'; exact absurd hl₀ h'

/-! ## The representation on classes of words -/

theorem opList_layList (ls : List (LayerData I)) :
    (interp D Sc).opList (layList D ls) = ldList D Sc 0 ls := by
  induction ls with
  | nil => rfl
  | cons x ls ih =>
    rw [show layList D (x :: ls) = lay D x.1 x.2.1 x.2.2 :: layList D ls from rfl,
      StringDiagrams.LocalInterpretation.opList_cons, ih]
    obtain ⟨l, g, r⟩ := x
    cases g <;>
    · simp only [ldList, ldOp, interp_op, layOp, lay, zero_add]
      rfl

/-- The representation of `H` on the class of a positioned word. -/
theorem lift_map_cl {t t' : List I} (gs : List PG) (h : SChain t (pl t gs) t') (x : M k) :
    (((pres D Sc).lift (respects D Sc)).map (OddMath.QuiverHecke.cl D Sc t t' gs h)).hom x =
      ldList D Sc 0 (pl t gs) (sgl (seqOf t) x) (seqOf t') := by
  rw [OddMath.QuiverHecke.cl, StringDiagrams.Presentation.lift_diag]
  refine ((interp D Sc).functor_map_apply (mkD D (pl t gs) h) x).trans ?_
  rw [layers_mkD, opList_layList]
  rfl

end OddMath.QuiverHecke.Realization
