/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ReverseIntertwinerEqual
import OddMath.QuiverHecke.CyclotomicAction.ReverseIntertwinerChain

/-!
# Reverse three-strand intertwiner meet

The reverse chronological form `ψ₀ g₁ g₀ = g₁ g₀ ψ₁` of the intertwiner
meet in Kang–Kashiwara–Oh Lemma 8.3, with arbitrary surrounding words and
all colour coincidences. The factors are the concrete `intertwinerHom`.
The single-colour case uses the opposite-ring braid from `ReverseIntertwinerEqual`;
the adjacent equal-colour case transports both dots and the crossing through
two unequal-colour crossings. Only the palindromic case uses symmetry of the
forward meet. The pair-chain corollary has no colour restrictions.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams SignedNilHecke
open SKM (zsign)
variable {I X : Type*} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type*} [CommRing k] (Sc : SKM.Scalars D k)
namespace ReverseIntertwinerMeet

def g0 (l v : List I) (a b c : I) :
    (pres D Sc).obj (ob D (l ++ a :: b :: c :: v)) ⟶
      (pres D Sc).obj (ob D (l ++ b :: a :: c :: v)) :=
  eqToHom (by simp) ≫ intertwinerHom D Sc l (c :: v) a b ≫ eqToHom (by simp)
def g1 (l v : List I) (a b c : I) :
    (pres D Sc).obj (ob D (l ++ a :: b :: c :: v)) ⟶
      (pres D Sc).obj (ob D (l ++ a :: c :: b :: v)) :=
  eqToHom (by simp) ≫ intertwinerHom D Sc (l ++ [a]) v b c ≫ eqToHom (by simp)
def p0 (l v : List I) (a b c : I) :=
  cl D Sc (l ++ a :: b :: c :: v) (l ++ b :: a :: c :: v) [.cross l.length]
    (sChain_ofShape' l (c :: v) (.cross a b) (by simp [Shape.dom])
      (by simp [Shape.cod]) rfl)
def p1 (l v : List I) (a b c : I) :=
  cl D Sc (l ++ a :: b :: c :: v) (l ++ a :: c :: b :: v)
    [.cross (l.length + 1)] (sChain_cross_succ l v a b c)

theorem g0_ne (l v : List I) {a b : I} (c : I) (h : a ≠ b) :
    g0 D Sc l v a b c = p0 D Sc l v a b c := by
  unfold g0 p0
  rw [intertwinerHom_of_ne D Sc _ _ h, eqToHom_comp_cl_assoc, cl_comp_eqToHom]
  all_goals simp

theorem g1_ne (l v : List I) (a : I) {b c : I} (h : b ≠ c) :
    g1 D Sc l v a b c = p1 D Sc l v a b c := by
  unfold g1 p1
  rw [intertwinerHom_of_ne D Sc _ _ h, eqToHom_comp_cl_assoc, cl_comp_eqToHom]
  all_goals simp

theorem g0_self (l v : List I) (i c : I) :
    g0 D Sc l v i i c = sameIntertwiner D Sc (l ++ i :: i :: c :: v) l.length i := by
  unfold g0
  rw [intertwinerHom_self, sameIntertwiner_congr D Sc
    (w := l ++ i :: i :: c :: v) (by simp) rfl]
  simp

theorem g1_self (l v : List I) (a i : I) :
    g1 D Sc l v a i i = sameIntertwiner D Sc (l ++ a :: i :: i :: v) (l.length + 1) i := by
  unfold g1
  rw [intertwinerHom_self, sameIntertwiner_congr D Sc
    (w := l ++ a :: i :: i :: v) (a := l.length + 1) (by simp) (by simp)]
  simp
end ReverseIntertwinerMeet
open ReverseIntertwinerMeet
/-- The chronological reverse meet `ψ₀ g₁ g₀`, with arbitrary surrounding words. -/
def reverseMeetLeft (l v : List I) (i j c : I) :
    (pres D Sc).obj (ob D (l ++ j :: c :: i :: v)) ⟶
      (pres D Sc).obj (ob D (l ++ i :: c :: j :: v)) :=
  p0 D Sc l v j c i ≫ g1 D Sc l v c j i ≫ g0 D Sc l v c i j
/-- The chronological reverse meet `g₁ g₀ ψ₁`, with arbitrary surrounding words. -/
def reverseMeetRight (l v : List I) (i j c : I) :
    (pres D Sc).obj (ob D (l ++ j :: c :: i :: v)) ⟶
      (pres D Sc).obj (ob D (l ++ i :: c :: j :: v)) :=
  g1 D Sc l v j c i ≫ g0 D Sc l v j i c ≫ p1 D Sc l v i j c

/-- The reverse meet when neither old colour is the moving colour. -/
theorem reverseMeetLeft_eq_ne (l v : List I) {i j c : I} (hji : j ≠ i) (hci : c ≠ i) :
    reverseMeetLeft D Sc l v i j c = reverseMeetRight D Sc l v i j c := by
  simp only [reverseMeetLeft, reverseMeetRight, g0_ne D Sc _ _ _ hji,
    g0_ne D Sc _ _ _ hci, g1_ne D Sc _ _ _ hji, g1_ne D Sc _ _ _ hci, p0, p1]
  rw [cl_comp, cl_comp, cl_comp, cl_comp]
  symm
  refine braid_ne_gen D Sc l v j c i (fun h => hji h.1) ?_ ?_ rfl rfl _ _ <;> simp

/-- The reverse meet in a single-colour block. -/
theorem reverseMeetLeft_eq_self (l v : List I) (i : I) :
    reverseMeetLeft D Sc l v i i i = reverseMeetRight D Sc l v i i i := by
  simp only [reverseMeetLeft, reverseMeetRight, g0_self, g1_self, p0, p1, ← crossE_eq_cl]
  have h := cross_comp_sameIntertwiner_sameIntertwiner D Sc l v i
  have hw : l ++ [i, i, i] ++ v = l ++ i :: i :: i :: v := by simp
  rw [hw] at h
  exact h

/-- The palindromic reverse meet, with its two outer colours equal. -/
theorem reverseMeetLeft_eq_iji (l v : List I) {i c : I} (hic : i ≠ c) :
    reverseMeetLeft D Sc l v i i c = reverseMeetRight D Sc l v i i c := by
  have h := meetLeft_eq_meetRight_iji D Sc l v hic
  rw [IntertwinerMeet.meetLeft_iji D Sc l v hic,
    IntertwinerMeet.meetRight_iji D Sc l v hic] at h
  simp only [← Category.assoc] at h
  rw [cancel_mono] at h
  simpa only [reverseMeetLeft, reverseMeetRight, g1_self, g0_self, Category.assoc,
    g0_ne D Sc _ _ _ hic.symm, g1_ne D Sc _ _ _ hic.symm, p0, p1] using h.symm

/-- Transport the same-colour variant through the two crossings from `j,i,i` to `i,i,j`. -/
theorem reverse_meet_core (l v : List I) {i j : I} (hij : i ≠ j) :
    sameIntertwiner D Sc (l ++ j :: i :: i :: v) (l.length + 1) i ≫
      (p0 D Sc l v j i i ≫ p1 D Sc l v i j i) =
    (p0 D Sc l v j i i ≫ p1 D Sc l v i j i) ≫
      sameIntertwiner D Sc (l ++ i :: i :: j :: v) l.length i := by
  have hu : dotE D Sc (l ++ j :: i :: i :: v) (l.length + 1) ≫
      (p0 D Sc l v j i i ≫ p1 D Sc l v i j i) =
      (p0 D Sc l v j i i ≫ p1 D Sc l v i j i) ≫
        dotE D Sc (l ++ i :: i :: j :: v) l.length := by
    unfold p0 p1
    rw [← Category.assoc, IntertwinerMeet.push_u_P1' D Sc l v hij,
      Linear.smul_comp, Category.assoc,
      eq_zsign_smul_symm (IntertwinerMeet.push_P_u D Sc l v (i := i) (j := j)),
      Linear.comp_smul, smul_smul, zsign_mul_self, one_smul, Category.assoc]
  have hv : dotE D Sc (l ++ j :: i :: i :: v) (l.length + 2) ≫
      (p0 D Sc l v j i i ≫ p1 D Sc l v i j i) =
      (p0 D Sc l v j i i ≫ p1 D Sc l v i j i) ≫
        dotE D Sc (l ++ i :: i :: j :: v) (l.length + 1) := by
    unfold p0 p1
    rw [← Category.assoc, IntertwinerMeet.push_v_P1' D Sc l v (i := i) (j := j),
      Linear.smul_comp, Category.assoc,
      eq_zsign_smul_symm (IntertwinerMeet.push_P_v D Sc l v hij),
      Linear.comp_smul, smul_smul, zsign_mul_self, one_smul, Category.assoc]
  have ht : crossE D Sc (l ++ j :: i :: i :: v) (l.length + 1) ≫
      (p0 D Sc l v j i i ≫ p1 D Sc l v i j i) =
      (p0 D Sc l v j i i ≫ p1 D Sc l v i j i) ≫
        crossE D Sc (l ++ i :: i :: j :: v) l.length := by
    rw [crossE_eq_cl D Sc (sChain_cross_succ l v j i i),
      crossE_eq_cl D Sc (sChain_ofShape' l (j :: v) (.cross i i)
        (by simp [Shape.dom]) (by simp [Shape.cod]) rfl)]
    unfold p0 p1
    simp only [cl_comp]
    refine braid_ne_gen D Sc l v j i i (fun h => hij h.1.symm) ?_ ?_ rfl rfl _ _ <;> simp
  have hs := variants_comp_of D Sc (p0 D Sc l v j i i ≫ p1 D Sc l v i j i) 0
    (by simpa only [zsign, zero_ne_one, ite_false, one_smul] using hu)
    (by simpa only [zsign, zero_ne_one, ite_false, one_smul] using hv)
    (by simpa only [zsign, zero_ne_one, ite_false, one_smul] using ht)
  unfold sameIntertwiner
  split_ifs
  · simpa only [zsign, zero_ne_one, ite_false, one_smul] using hs.1
  · simpa only [zsign, zero_ne_one, ite_false, one_smul] using hs.2

/-- The reverse meet when the middle and moving colours coincide. -/
theorem reverseMeetLeft_eq_jii (l v : List I) {i j : I} (hji : j ≠ i) :
    reverseMeetLeft D Sc l v i j i = reverseMeetRight D Sc l v i j i := by
  simp only [reverseMeetLeft, reverseMeetRight, g1_ne D Sc _ _ _ hji,
    g0_ne D Sc _ _ _ hji, g0_self, g1_self]
  simpa only [Category.assoc] using (reverse_meet_core D Sc l v hji.symm).symm

/-- The reverse three-strand meet for arbitrary colours, including every coincidence. -/
theorem reverseMeetLeft_eq_all (l v : List I) (i j c : I) :
    reverseMeetLeft D Sc l v i j c = reverseMeetRight D Sc l v i j c := by
  by_cases hji : j = i
  · subst j
    by_cases hci : c = i
    · subst c
      exact reverseMeetLeft_eq_self D Sc l v i
    · exact reverseMeetLeft_eq_iji D Sc l v (Ne.symm hci)
  · by_cases hci : c = i
    · subst c
      exact reverseMeetLeft_eq_jii D Sc l v hji
    · exact reverseMeetLeft_eq_ne D Sc l v hji hci

/-- Reverse crossing naturality on a pair of old strands, without colour restrictions. -/
theorem cross_comp_reverseMoveHom_pair_all (l : List I) (i j c : I) :
    cl D Sc (l ++ [j, c] ++ [i]) (l ++ [c, j] ++ [i]) [.cross l.length]
      (sChain_crossAt l [i] j c) ≫ reverseMoveHom D Sc i l [c, j] =
    reverseMoveHom D Sc i l [j, c] ≫
      cl D Sc (l ++ i :: [j, c]) (l ++ i :: [c, j]) [.cross (l.length + 1)]
        (sChain_cross_succ l [] i j c) := by
  have h := reverseMeetLeft_eq_all D Sc l [] i j c
  unfold reverseMeetLeft reverseMeetRight g0 g1 p0 p1 at h
  apply (cancel_epi (eqToHom (congrArg (fun s => (pres D Sc).obj (ob D s))
    (show l ++ j :: c :: i :: [] = l ++ [j, c] ++ [i] by simp)))).1
  simp only [reverseMoveHom, Category.assoc, eqToHom_trans_assoc]
  simp only [Category.assoc, eqToHom_trans_assoc] at h
  rw [eqToHom_comp_cl_assoc, cl_comp_eqToHom_assoc]
  · rw [cl_comp_eqToHom_assoc] at h
    · exact h
    · simp
  all_goals simp

end OddMath.QuiverHecke
