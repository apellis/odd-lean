/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ReverseIntertwinerCrossing
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerNaturality

/-!
# Reverse moving-chain balance

Reverse old-diagram transport for the moving chains of Kang–Kashiwara–Oh.
The concrete dot and crossing slides extend to positioned words and arbitrary
old morphisms. No inverse of a moving chain is used.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams MonoidalCategory
open SKM (zsign)
variable {I X : Type*} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type*} [CommRing k] (Sc : SKM.Scalars D k)

/-- Reverse transport of a positioned generator, with word-parity invariance. -/
theorem gen_comp_reverseMoveHom (i : I) {ν ν' : List I} (g : PG) (h : SChain ν (pl ν [g]) ν')
    (hfit : Fits ν.length [g]) :
    cl D Sc (ν ++ [i]) (ν' ++ [i]) [g] (sChain_append_one i h hfit) ≫
        reverseMoveHom D Sc i [] ν' =
      zsign k (g.par D ν * (D.parity i * wordSumParity D ν)) •
        (reverseMoveHom D Sc i [] ν ≫ cl D Sc (i :: ν) (i :: ν') ([g].map (PG.shift 1)) (sChain_shift_one i h)) ∧
      wordSumParity D ν' = wordSumParity D ν := by
  obtain ⟨m, s, v, hν, hg, -, -⟩ := exists_split g 0 ν (Nat.zero_le _)
    (by simpa using hfit g (by simp))
  subst hg
  have ht := tgt_eq h
  cases s with
  | dot x =>
    obtain rfl : ν = m ++ x :: v := by simpa [Shape.dom] using hν
    obtain rfl : ν' = m ++ x :: v := by simpa [PG.ofShape, PG.act] using ht.symm
    refine ⟨?_, rfl⟩
    have key : dotE D Sc (m ++ x :: v ++ [i]) ([].length + m.length) ≫
          reverseMoveHom D Sc i [] (m ++ x :: v) =
        zsign k (D.parity x * (D.parity i * wordSumParity D (m ++ x :: v))) •
          (reverseMoveHom D Sc i [] (m ++ x :: v) ≫ dotE D Sc (i :: (m ++ x :: v)) ([].length + 1 + m.length)) :=
      dot_mem_comp_reverseMoveHom D Sc i x v m [] (m ++ x :: v) (by simp)
    rw [cl_congr_gs D Sc (t := m ++ x :: v ++ [i]) (gs' := [.dot ([].length + m.length)])
        (by simp [PG.ofShape]) _ (sChain_dotAny _ _), ← dotE_eq_cl,
      cl_congr_gs D Sc (t := i :: (m ++ x :: v)) (gs' := [.dot ([].length + 1 + m.length)])
        (by simp [PG.ofShape, PG.shift]) _ (sChain_dotAny _ _), ← dotE_eq_cl]
    have hp : PG.par D (m ++ x :: v) (PG.ofShape (Shape.dot x) (0 + m.length)) = D.parity x := by
      simp [PG.par, PG.ofShape]
    rw [hp]
    exact key
  | cross j c =>
    obtain rfl : ν = m ++ j :: c :: v := by simpa [Shape.dom] using hν
    obtain rfl : ν' = m ++ c :: j :: v := by
      simpa [PG.ofShape, PG.act, List.take_append, List.drop_append] using ht.symm
    refine ⟨?_, ?_⟩
    · have key := cross_comp_reverseMoveHom_all D Sc v i j c m []
      simp only [List.nil_append] at key
      rw [cl_congr_gs D Sc (t := m ++ j :: c :: v ++ [i]) (t' := m ++ c :: j :: v ++ [i])
          (gs' := [.cross ([].length + m.length)]) (by simp [PG.ofShape]) _
          (sChain_mid₂ [] m v i j c),
        cl_congr_gs D Sc (t := i :: (m ++ j :: c :: v)) (t' := i :: (m ++ c :: j :: v))
          (gs' := [.cross ([].length + 1 + m.length)])
          (by simp [PG.ofShape, PG.shift, Nat.add_comm]) _ (sChain_mid₁ [] m v i j c)]
      rw [key]
      congr 1
      have hp : PG.par D (m ++ j :: c :: v) (PG.ofShape (Shape.cross j c) (0 + m.length)) =
          D.parity j * D.parity c := by simp [PG.par, PG.ofShape]
      rw [hp]
      simp only [wordSumParity, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
      generalize D.parity i = a
      generalize D.parity j = b
      generalize D.parity c = d
      generalize (List.map D.parity m).sum = e
      generalize (List.map D.parity v).sum = f
      congr 1
      revert a b d e f
      decide
    · simp only [wordSumParity, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
      abel

/-- Reverse transport of every fitting positioned word. -/
theorem cl_comp_reverseMoveHom (i : I) : ∀ {ν ν' : List I} (gs : List PG) (h : SChain ν (pl ν gs) ν')
    (hfit : Fits ν.length gs),
    cl D Sc (ν ++ [i]) (ν' ++ [i]) gs (sChain_append_one i h hfit) ≫
        reverseMoveHom D Sc i [] ν' =
      zsign k (chainParity D ν gs * (D.parity i * wordSumParity D ν)) •
        (reverseMoveHom D Sc i [] ν ≫ cl D Sc (i :: ν) (i :: ν') (gs.map (PG.shift 1)) (sChain_shift_one i h)) ∧
      wordSumParity D ν' = wordSumParity D ν
  | ν, ν', [], h, _ => by
    obtain rfl : ν = ν' := h
    refine ⟨?_, rfl⟩
    simp [cl_nil, zsign]
  | ν, ν', g :: gs, h, hfit => by
    have h₁ : SChain ν (pl ν [g]) (g.act ν) := sChain_pl ν [g]
    have h₂ : SChain (g.act ν) (pl (g.act ν) gs) ν' := by
      have := tgt_eq h
      simpa [← this] using sChain_pl (g.act ν) gs
    have hfit₁ : Fits ν.length [g] := fun g' hg' => hfit g' (by simp_all)
    have hfit₂ : Fits (g.act ν).length gs := by
      rw [length_act]; exact fun g' hg' => hfit g' (by simp [hg'])
    obtain ⟨e₁, p₁⟩ := gen_comp_reverseMoveHom D Sc i g h₁ hfit₁
    obtain ⟨e₂, p₂⟩ := cl_comp_reverseMoveHom i gs h₂ hfit₂
    refine ⟨?_, p₂.trans p₁⟩
    have s₁ : cl D Sc (i :: ν) (i :: ν') ((g :: gs).map (PG.shift 1)) (sChain_shift_one i h) =
        cl D Sc (i :: ν) (i :: g.act ν) ([g].map (PG.shift 1)) (sChain_shift_one i h₁) ≫
          cl D Sc (i :: g.act ν) (i :: ν') (gs.map (PG.shift 1)) (sChain_shift_one i h₂) := by
      rw [cl_comp]; rfl
    have s₂ : cl D Sc (ν ++ [i]) (ν' ++ [i]) (g :: gs) (sChain_append_one i h hfit) =
        cl D Sc (ν ++ [i]) (g.act ν ++ [i]) [g] (sChain_append_one i h₁ hfit₁) ≫
          cl D Sc (g.act ν ++ [i]) (ν' ++ [i]) gs (sChain_append_one i h₂ hfit₂) := by
      rw [cl_comp]; rfl
    rw [s₂, s₁, Category.assoc, e₂, Linear.comp_smul, ← Category.assoc, e₁, Linear.smul_comp,
      smul_smul, Category.assoc, p₁, chainParity_cons, ← zsign_add_eq]
    congr 2
    ring

open Categorification.TypeA

/-- Reverse balance on arbitrary, possibly inhomogeneous, old diagrams. -/
theorem hom_comp_reverseMoveHom (i : I) {t t' : List I}
    (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :
    (f ▷ (pres D Sc).obj (ob D [i])) ≫ reverseMoveHom D Sc i [] t' =
      reverseMoveHom D Sc i [] t ≫
        ((pres D Sc).obj (ob D [i]) ◁
          Supercategory.twist k (D.parity i * wordSumParity D t) f) := by
  have hf : f ∈ Submodule.span k {f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t') |
      ∃ l : List ℕ, l.Pairwise (· ≤ ·) ∧ (∀ x ∈ l, x < t.length) ∧
        ∃ w : Equiv.Perm (Fin t.length),
          ∃ h, cl D Sc t t' (l.map PG.dot ++ cw (canWord t.length w)) h = f} := by
    rw [span_normalForms]; trivial
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨l, -, hl, w, h, rfl⟩ := hf
    have hfit := fits_append (fits_dots hl) (fits_cw (validWord_canWord t.length w))
    rw [Supercategory.twist_of_mem _ (cl_mem_chainParity D Sc _ h hfit),
      (MonoidalSupercategory.whiskerLeft_smul (R := k)), Linear.comp_smul,
      cl_whiskerRight D Sc _ h [i] hfit, cl_whiskerLeft]
    have hs : ∀ p : ZMod 2, Supercategory.sign k p = zsign k p := by
      intro p
      rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) p with rfl | rfl <;>
        simp [Supercategory.sign, zsign]
    simpa only [List.singleton_append, List.length_singleton, hs, mul_comm] using
      (cl_comp_reverseMoveHom D Sc i _ h hfit).1
  | zero => simp [MonoidalSupercategory.whiskerLeft_zero (R := k),
      MonoidalSupercategory.zero_whiskerRight (R := k)]
  | add f g _ _ hf hg =>
    simp only [map_add, (MonoidalSupercategory.whiskerLeft_add (R := k)),
      (MonoidalSupercategory.add_whiskerRight (R := k)), Preadditive.add_comp,
      Preadditive.comp_add, hf, hg]
  | smul r f _ hf =>
    simp only [map_smul, (MonoidalSupercategory.whiskerLeft_smul (R := k)),
      (MonoidalSupercategory.smul_whiskerRight (R := k)), Linear.smul_comp,
      Linear.comp_smul, hf]

end OddMath.QuiverHecke
