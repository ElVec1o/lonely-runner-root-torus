/-
# Root tori: the 2-torus loneliness function and the critical rank-two root tori

Formalisation of the root-torus statements of the accompanying note (Theorem 1 there).

A 2-dimensional subtorus `U` of `T^(k+1)` is the image of `(s,t) ↦ s·g1 + t·g2 (mod 1)` for integer
vectors `g1 g2 : Fin (k+1) → ℤ`; its coordinate forms are `φ_i(s,t) = g1 i · s + g2 i · t`.
`torusGap g1 g2 s t = min_i ‖φ_i(s,t)‖` and `torusML g1 g2 = sup_{s,t} torusGap` (the maximal loneliness `M(U)`).
With `g2 = 0` this is the project's `ML` (`torusML_zero_snd`).

Main results (`M(U) = 1/h`, with an explicit maximiser and an exact upper bound by case analysis):

* `torusML_A2`   : forms `A, B, A+B`                           `M = 1/3`
* `torusML_B2`   : forms `A, B, A+B, A+2B`                     `M = 1/4`
* `torusML_G2`   : forms `A, B, A+B, 2A+B, 3A+B, 3A+2B`        `M = 1/6`
* `torusML_JK_U2`   : Jain-Kravitz `U^2 = <(1,0,1,1),(1,1,0,2)>`  `M = 1/4`
* `torusML_Cordella_UC` : Cordella `U_C = <(1,0,1,2,3,3),(0,1,1,1,1,2)>`  `M = 1/6`
* `JK_U2_forms_eq_B2`, `Cordella_UC_forms_eq_G2` : equality of the sets of forms.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.MaxLoneliness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation

set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace LRSpectrumFull
namespace ObsRootTorus

/-! ## Section 1: the 2-torus loneliness function -/

section Defs

variable {k : ℕ}

/-- Instantaneous loneliness on the 2-torus `s·g1 + t·g2`: the minimum over the coordinate forms of
the nearest-integer distance. -/
noncomputable def torusGap (g1 g2 : Fin (k + 1) → ℤ) (s t : ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun i => nearestIntDist ((g1 i : ℝ) * s + (g2 i : ℝ) * t))

/-- `M(U)`: the supremum of `torusGap` over the parameter plane. -/
noncomputable def torusML (g1 g2 : Fin (k + 1) → ℤ) : ℝ :=
  sSup (Set.range (fun p : ℝ × ℝ => torusGap g1 g2 p.1 p.2))

theorem torusGap_le (g1 g2 : Fin (k + 1) → ℤ) (s t : ℝ) (i : Fin (k + 1)) :
    torusGap g1 g2 s t ≤ nearestIntDist ((g1 i : ℝ) * s + (g2 i : ℝ) * t) := by
  simp only [torusGap]
  exact Finset.inf'_le _ (Finset.mem_univ i)

theorem le_torusGap (g1 g2 : Fin (k + 1) → ℤ) (s t c : ℝ)
    (h : ∀ i, c ≤ nearestIntDist ((g1 i : ℝ) * s + (g2 i : ℝ) * t)) : c ≤ torusGap g1 g2 s t := by
  simp only [torusGap, Finset.le_inf'_iff]
  intro i _
  exact h i

theorem lt_torusGap_iff (g1 g2 : Fin (k + 1) → ℤ) (s t c : ℝ) :
    c < torusGap g1 g2 s t ↔ ∀ i, c < nearestIntDist ((g1 i : ℝ) * s + (g2 i : ℝ) * t) := by
  simp only [torusGap, Finset.lt_inf'_iff, Finset.mem_univ, true_implies]

theorem torusGap_le_half (g1 g2 : Fin (k + 1) → ℤ) (s t : ℝ) : torusGap g1 g2 s t ≤ 1 / 2 :=
  (torusGap_le g1 g2 s t 0).trans (nearestIntDist_le_half _)

theorem bddAbove_range_torusGap (g1 g2 : Fin (k + 1) → ℤ) :
    BddAbove (Set.range (fun p : ℝ × ℝ => torusGap g1 g2 p.1 p.2)) := by
  refine ⟨1 / 2, ?_⟩
  rintro y ⟨p, rfl⟩
  exact torusGap_le_half g1 g2 p.1 p.2

/-- A value attained by `torusGap` and never exceeded is `torusML`. -/
theorem torusML_eq_of (g1 g2 : Fin (k + 1) → ℤ) (c s0 t0 : ℝ)
    (hat : torusGap g1 g2 s0 t0 = c) (hub : ∀ s t, torusGap g1 g2 s t ≤ c) :
    torusML g1 g2 = c := by
  unfold torusML
  refine IsGreatest.csSup_eq ⟨⟨(s0, t0), hat⟩, ?_⟩
  rintro y ⟨p, rfl⟩
  exact hub p.1 p.2

/-- On the line `t = 0` with `g2 = 0` the torus loneliness is the project's `gap`. -/
theorem torusGap_zero_snd (v : Fin (k + 1) → ℤ) (s t : ℝ) :
    torusGap v (fun _ => 0) s t = gap v s := by
  simp [torusGap, gap]

/-- With `g2 = 0` the torus loneliness is the project's `ML`. -/
theorem torusML_zero_snd (v : Fin (k + 1) → ℤ) : torusML v (fun _ => 0) = ML v := by
  unfold torusML ML
  congr 1
  ext y
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.1, (torusGap_zero_snd v p.1 p.2).symm⟩
  · rintro ⟨s, rfl⟩
    exact ⟨(s, 0), torusGap_zero_snd v s 0⟩

/-- Integer parts of the parameters do not matter: reduce to `s, t ∈ [0,1)`. -/
theorem torusGap_fract (g1 g2 : Fin (k + 1) → ℤ) (s t : ℝ) :
    torusGap g1 g2 s t = torusGap g1 g2 (Int.fract s) (Int.fract t) := by
  simp only [torusGap]
  congr 1
  funext i
  have hs : s = Int.fract s + ((⌊s⌋ : ℤ) : ℝ) := by linarith [Int.floor_add_fract s]
  have ht : t = Int.fract t + ((⌊t⌋ : ℤ) : ℝ) := by linarith [Int.floor_add_fract t]
  have e : (g1 i : ℝ) * s + (g2 i : ℝ) * t =
      ((g1 i : ℝ) * Int.fract s + (g2 i : ℝ) * Int.fract t) +
        ((g1 i * ⌊s⌋ + g2 i * ⌊t⌋ : ℤ) : ℝ) := by
    push_cast
    nth_rewrite 1 [hs]
    nth_rewrite 1 [ht]
    ring
  rw [e, nearestIntDist_add_int]

/-- Floor-cell lemma: if `‖z‖ > c` and `0 ≤ z < N`, then `z` lies strictly inside one of the
intervals `(n + c, n + 1 - c)`, `0 ≤ n < N`. -/
theorem nd_gt_cell (z c : ℝ) (N : ℕ) (h0 : 0 ≤ z) (hN : z < N)
    (h : c < nearestIntDist z) : ∃ n : ℕ, n < N ∧ (n : ℝ) + c < z ∧ z < n + 1 - c := by
  have hf := Int.floor_add_fract z
  have hf0 := Int.fract_nonneg z
  have hf1 := Int.fract_lt_one z
  simp only [nearestIntDist, lt_min_iff] at h
  obtain ⟨h1, h2⟩ := h
  have hfl0 : 0 ≤ ⌊z⌋ := Int.floor_nonneg.mpr h0
  have hflN : ⌊z⌋ < (N : ℤ) := by
    have : (⌊z⌋ : ℝ) < N := by linarith
    exact_mod_cast this
  refine ⟨⌊z⌋.toNat, by omega, ?_, ?_⟩
  · have e : ((⌊z⌋.toNat : ℕ) : ℝ) = (⌊z⌋ : ℝ) := by
      have : ((⌊z⌋.toNat : ℕ) : ℤ) = ⌊z⌋ := Int.toNat_of_nonneg hfl0
      exact_mod_cast this
    rw [e]; linarith
  · have e : ((⌊z⌋.toNat : ℕ) : ℝ) = (⌊z⌋ : ℝ) := by
      have : ((⌊z⌋.toNat : ℕ) : ℤ) = ⌊z⌋ := Int.toNat_of_nonneg hfl0
      exact_mod_cast this
    rw [e]; linarith

end Defs

/-! ## Section 2: the value `1/N` is attained on the diagonal -/

section Attained

variable {k : ℕ}

/-- Maximiser on the diagonal: if every form has coefficient sum `m_i` with `1 ≤ m_i ≤ N - 1` and some
form has `m_i = 1`, then `torusGap g1 g2 (1/N) (1/N) = 1/N`. -/
theorem torusGap_diag (g1 g2 : Fin (k + 1) → ℤ) (N : ℕ) (hN : 0 < N)
    (hb : ∀ i, 1 ≤ g1 i + g2 i ∧ g1 i + g2 i + 1 ≤ (N : ℤ)) (i0 : Fin (k + 1))
    (h0 : g1 i0 + g2 i0 = 1) :
    torusGap g1 g2 (1 / (N : ℝ)) (1 / (N : ℝ)) = 1 / (N : ℝ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hu : (1 / (N : ℝ)) * N = 1 := by field_simp
  have hupos : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  have hval : ∀ i, (g1 i : ℝ) * (1 / (N : ℝ)) + (g2 i : ℝ) * (1 / (N : ℝ))
      = ((g1 i + g2 i : ℤ) : ℝ) * (1 / (N : ℝ)) := by
    intro i; push_cast; ring
  apply le_antisymm
  · refine (torusGap_le g1 g2 _ _ i0).trans ?_
    rw [hval i0, h0]
    have := nearestIntDist_le_dist (((1 : ℤ) : ℝ) * (1 / (N : ℝ))) 0
    simpa using this
  · apply le_torusGap
    intro i
    rw [hval i]
    obtain ⟨hb1, hb2⟩ := hb i
    have hm1 : (1 : ℝ) ≤ ((g1 i + g2 i : ℤ) : ℝ) := by exact_mod_cast hb1
    have hm2 : ((g1 i + g2 i : ℤ) : ℝ) + 1 ≤ N := by exact_mod_cast hb2
    apply nearestIntDist_ge
    · exact mul_nonneg (by linarith) hupos.le
    · nlinarith
    · nlinarith
    · nlinarith

end Attained

/-! ## Section 3: exact upper bounds by cell analysis, the five tori -/

section Roots

open Matrix

/-- `A2`: forms `A, B, A+B`. -/
def A2g1 : Fin 3 → ℤ := ![1, 0, 1]
def A2g2 : Fin 3 → ℤ := ![0, 1, 1]
/-- `B2`: forms `A, B, A+B, A+2B`. -/
def B2g1 : Fin 4 → ℤ := ![1, 0, 1, 1]
def B2g2 : Fin 4 → ℤ := ![0, 1, 1, 2]
/-- `G2`: forms `A, B, A+B, 2A+B, 3A+B, 3A+2B`. -/
def G2g1 : Fin 6 → ℤ := ![1, 0, 1, 2, 3, 3]
def G2g2 : Fin 6 → ℤ := ![0, 1, 1, 1, 1, 2]
/-- Jain-Kravitz `U^2 = <(1,0,1,1),(1,1,0,2)>` (their ordering of the coordinates). -/
def JKg1 : Fin 4 → ℤ := ![1, 0, 1, 1]
def JKg2 : Fin 4 → ℤ := ![1, 1, 0, 2]
/-- Cordella `U_C = <(1,0,1,2,3,3),(0,1,1,1,1,2)>`. -/
def CORg1 : Fin 6 → ℤ := ![1, 0, 1, 2, 3, 3]
def CORg2 : Fin 6 → ℤ := ![0, 1, 1, 1, 1, 2]

theorem A2_upper (s t : ℝ) : torusGap A2g1 A2g2 s t ≤ 1 / 3 := by
  rw [torusGap_fract]
  have hx0 := Int.fract_nonneg s
  have hx1 := Int.fract_lt_one s
  have hy0 := Int.fract_nonneg t
  have hy1 := Int.fract_lt_one t
  generalize Int.fract s = x at *
  generalize Int.fract t = y at *
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 / 3 := ⟨_, rfl⟩
  rw [← hc]
  by_contra hcon
  rw [not_le, lt_torusGap_iff] at hcon
  have h0 := hcon 0
  have h1 := hcon 1
  have h2 := hcon 2
  simp [A2g1, A2g2] at h0 h1 h2
  obtain ⟨n0, hn0, a0, b0⟩ := nd_gt_cell x c 1 (by linarith) (by push_cast; linarith) h0
  obtain ⟨n1, hn1, a1, b1⟩ := nd_gt_cell y c 1 (by linarith) (by push_cast; linarith) h1
  obtain ⟨n2, hn2, a2, b2⟩ := nd_gt_cell (x + y) c 2 (by linarith) (by push_cast; linarith) h2
  interval_cases n0 <;> interval_cases n1 <;> interval_cases n2 <;> (push_cast at *; linarith)

theorem B2_upper (s t : ℝ) : torusGap B2g1 B2g2 s t ≤ 1 / 4 := by
  rw [torusGap_fract]
  have hx0 := Int.fract_nonneg s
  have hx1 := Int.fract_lt_one s
  have hy0 := Int.fract_nonneg t
  have hy1 := Int.fract_lt_one t
  generalize Int.fract s = x at *
  generalize Int.fract t = y at *
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 / 4 := ⟨_, rfl⟩
  rw [← hc]
  by_contra hcon
  rw [not_le, lt_torusGap_iff] at hcon
  have h0 := hcon 0
  have h1 := hcon 1
  have h2 := hcon 2
  have h3 := hcon 3
  simp [B2g1, B2g2] at h0 h1 h2 h3
  obtain ⟨n0, hn0, a0, b0⟩ := nd_gt_cell x c 1 (by linarith) (by push_cast; linarith) h0
  obtain ⟨n1, hn1, a1, b1⟩ := nd_gt_cell y c 1 (by linarith) (by push_cast; linarith) h1
  obtain ⟨n2, hn2, a2, b2⟩ := nd_gt_cell (x + y) c 2 (by linarith) (by push_cast; linarith) h2
  obtain ⟨n3, hn3, a3, b3⟩ := nd_gt_cell (x + 2 * y) c 3 (by linarith) (by push_cast; linarith) h3
  interval_cases n0 <;> interval_cases n1 <;> interval_cases n2 <;> interval_cases n3 <;>
    (push_cast at *; linarith)

theorem JK_upper (s t : ℝ) : torusGap JKg1 JKg2 s t ≤ 1 / 4 := by
  rw [torusGap_fract]
  have hx0 := Int.fract_nonneg s
  have hx1 := Int.fract_lt_one s
  have hy0 := Int.fract_nonneg t
  have hy1 := Int.fract_lt_one t
  generalize Int.fract s = x at *
  generalize Int.fract t = y at *
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 / 4 := ⟨_, rfl⟩
  rw [← hc]
  by_contra hcon
  rw [not_le, lt_torusGap_iff] at hcon
  have h0 := hcon 0
  have h1 := hcon 1
  have h2 := hcon 2
  have h3 := hcon 3
  simp [JKg1, JKg2] at h0 h1 h2 h3
  obtain ⟨n0, hn0, a0, b0⟩ := nd_gt_cell (x + y) c 2 (by linarith) (by push_cast; linarith) h0
  obtain ⟨n1, hn1, a1, b1⟩ := nd_gt_cell y c 1 (by linarith) (by push_cast; linarith) h1
  obtain ⟨n2, hn2, a2, b2⟩ := nd_gt_cell x c 1 (by linarith) (by push_cast; linarith) h2
  obtain ⟨n3, hn3, a3, b3⟩ := nd_gt_cell (x + 2 * y) c 3 (by linarith) (by push_cast; linarith) h3
  interval_cases n0 <;> interval_cases n1 <;> interval_cases n2 <;> interval_cases n3 <;>
    (push_cast at *; linarith)

theorem G2_upper (s t : ℝ) : torusGap G2g1 G2g2 s t ≤ 1 / 6 := by
  rw [torusGap_fract]
  have hx0 := Int.fract_nonneg s
  have hx1 := Int.fract_lt_one s
  have hy0 := Int.fract_nonneg t
  have hy1 := Int.fract_lt_one t
  generalize Int.fract s = x at *
  generalize Int.fract t = y at *
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 / 6 := ⟨_, rfl⟩
  rw [← hc]
  by_contra hcon
  rw [not_le, lt_torusGap_iff] at hcon
  have h0 := hcon 0
  have h1 := hcon 1
  have h2 := hcon 2
  have h3 := hcon 3
  have h4 := hcon 4
  have h5 := hcon 5
  simp [G2g1, G2g2] at h0 h1 h2 h3 h4 h5
  obtain ⟨n0, hn0, a0, b0⟩ := nd_gt_cell x c 1 (by linarith) (by push_cast; linarith) h0
  obtain ⟨n1, hn1, a1, b1⟩ := nd_gt_cell y c 1 (by linarith) (by push_cast; linarith) h1
  obtain ⟨n2, hn2, a2, b2⟩ := nd_gt_cell (x + y) c 2 (by linarith) (by push_cast; linarith) h2
  obtain ⟨n3, hn3, a3, b3⟩ := nd_gt_cell (2 * x + y) c 3 (by linarith) (by push_cast; linarith) h3
  obtain ⟨n4, hn4, a4, b4⟩ := nd_gt_cell (3 * x + y) c 4 (by linarith) (by push_cast; linarith) h4
  obtain ⟨n5, hn5, a5, b5⟩ := nd_gt_cell (3 * x + 2 * y) c 5 (by linarith) (by push_cast; linarith) h5
  interval_cases n0 <;> interval_cases n1 <;> interval_cases n2 <;> interval_cases n3 <;>
    interval_cases n4 <;> interval_cases n5 <;> (push_cast at *; linarith)

theorem torusML_A2 : torusML A2g1 A2g2 = 1 / 3 := by
  have h := torusGap_diag A2g1 A2g2 3 (by norm_num) (by decide) 0 (by decide)
  refine torusML_eq_of A2g1 A2g2 (1 / 3) (1 / ((3 : ℕ) : ℝ)) (1 / ((3 : ℕ) : ℝ)) ?_ A2_upper
  rw [h]; norm_num

theorem torusML_B2 : torusML B2g1 B2g2 = 1 / 4 := by
  have h := torusGap_diag B2g1 B2g2 4 (by norm_num) (by decide) 0 (by decide)
  refine torusML_eq_of B2g1 B2g2 (1 / 4) (1 / ((4 : ℕ) : ℝ)) (1 / ((4 : ℕ) : ℝ)) ?_ B2_upper
  rw [h]; norm_num

theorem torusML_JK_U2 : torusML JKg1 JKg2 = 1 / 4 := by
  have h := torusGap_diag JKg1 JKg2 4 (by norm_num) (by decide) 1 (by decide)
  refine torusML_eq_of JKg1 JKg2 (1 / 4) (1 / ((4 : ℕ) : ℝ)) (1 / ((4 : ℕ) : ℝ)) ?_ JK_upper
  rw [h]; norm_num

theorem torusML_G2 : torusML G2g1 G2g2 = 1 / 6 := by
  have h := torusGap_diag G2g1 G2g2 6 (by norm_num) (by decide) 0 (by decide)
  refine torusML_eq_of G2g1 G2g2 (1 / 6) (1 / ((6 : ℕ) : ℝ)) (1 / ((6 : ℕ) : ℝ)) ?_ G2_upper
  rw [h]; norm_num

/-- Cordella's `U_C` has literally the generators of `G2`. -/
theorem CORg_eq_G2 : CORg1 = G2g1 ∧ CORg2 = G2g2 := ⟨rfl, rfl⟩

theorem torusML_Cordella_UC : torusML CORg1 CORg2 = 1 / 6 := torusML_G2

/-- The forms of Jain-Kravitz `U^2` are those of `B2` (as a set of coefficient pairs `(a,b)` of
`a·s + b·t`). -/
theorem JK_U2_forms_eq_B2 :
    (Finset.univ.image (fun i : Fin 4 => (JKg1 i, JKg2 i))) =
      Finset.univ.image (fun i : Fin 4 => (B2g1 i, B2g2 i)) := by
  decide

/-- The forms of Cordella's `U_C` are those of `G2`, i.e. the six positive roots
`A, B, A+B, 2A+B, 3A+B, 3A+2B` of `G2` in simple-root coordinates. -/
theorem Cordella_UC_forms_eq_G2 :
    (Finset.univ.image (fun i : Fin 6 => (CORg1 i, CORg2 i))) =
      Finset.univ.image (fun i : Fin 6 => (G2g1 i, G2g2 i)) := by
  decide

/-! ## Section 4: negative controls (the upper bounds are not vacuous) -/

/-- Cell lower bound: `c ≤ ‖z‖` when `z ∈ [n + c, n + 1 - c]`. -/
theorem nd_ge_cell (z c : ℝ) (n : ℤ) (hc : 0 < c) (h1 : (n : ℝ) + c ≤ z) (h2 : z + c ≤ n + 1) :
    c ≤ nearestIntDist z := by
  have e : z = (z - (n : ℝ)) + ((n : ℤ) : ℝ) := by ring
  rw [e, nearestIntDist_add_int]
  exact nearestIntDist_ge (by linarith) (by linarith) (by linarith) (by linarith)

/-- Planted wrong torus 1: `A2` with `A+B` replaced by `A+2B` has loneliness above `1/3`. -/
def A2'g1 : Fin 3 → ℤ := ![1, 0, 1]
def A2'g2 : Fin 3 → ℤ := ![0, 1, 2]

theorem control_A2' : (1 : ℝ) / 3 < torusGap A2'g1 A2'g2 (2 / 5) (1 / 2) := by
  have h : (2 / 5 : ℝ) ≤ torusGap A2'g1 A2'g2 (2 / 5) (1 / 2) := by
    apply le_torusGap
    intro i
    fin_cases i <;> norm_num [A2'g1, A2'g2] <;>
      first
      | (refine nd_ge_cell _ _ 0 ?_ ?_ ?_ <;> norm_num; done)
      | (refine nd_ge_cell _ _ 1 ?_ ?_ ?_ <;> norm_num; done)
      | (refine nd_ge_cell _ _ 2 ?_ ?_ ?_ <;> norm_num; done)
  linarith

/-- Planted wrong torus 2: `B2` with `A+2B` replaced by `A+3B` has loneliness above `1/4`. -/
def B2'g1 : Fin 4 → ℤ := ![1, 0, 1, 1]
def B2'g2 : Fin 4 → ℤ := ![0, 1, 1, 3]

theorem control_B2' : (1 : ℝ) / 4 < torusGap B2'g1 B2'g2 (3 / 10) (2 / 5) := by
  have h : (3 / 10 : ℝ) ≤ torusGap B2'g1 B2'g2 (3 / 10) (2 / 5) := by
    apply le_torusGap
    intro i
    fin_cases i <;> norm_num [B2'g1, B2'g2] <;>
      first
      | (refine nd_ge_cell _ _ 0 ?_ ?_ ?_ <;> norm_num; done)
      | (refine nd_ge_cell _ _ 1 ?_ ?_ ?_ <;> norm_num; done)
      | (refine nd_ge_cell _ _ 2 ?_ ?_ ?_ <;> norm_num; done)
  linarith

/-- Planted wrong torus 3: `G2` with `3A+2B` replaced by `3A+4B` has loneliness above `1/6`. -/
def G2'g1 : Fin 6 → ℤ := ![1, 0, 1, 2, 3, 3]
def G2'g2 : Fin 6 → ℤ := ![0, 1, 1, 1, 1, 4]

theorem control_G2' : (1 : ℝ) / 6 < torusGap G2'g1 G2'g2 (1 / 2) (1 / 4) := by
  have h : (1 / 4 : ℝ) ≤ torusGap G2'g1 G2'g2 (1 / 2) (1 / 4) := by
    apply le_torusGap
    intro i
    fin_cases i <;> norm_num [G2'g1, G2'g2] <;>
      first
      | (refine nd_ge_cell _ _ 0 ?_ ?_ ?_ <;> norm_num; done)
      | (refine nd_ge_cell _ _ 1 ?_ ?_ ?_ <;> norm_num; done)
      | (refine nd_ge_cell _ _ 2 ?_ ?_ ?_ <;> norm_num; done)
  linarith

end Roots

end ObsRootTorus
end LRSpectrumFull
