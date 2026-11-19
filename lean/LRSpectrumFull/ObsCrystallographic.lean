/-
# The crystallographic lemma (totient condition)

Setting: a 2-torus `U = {s·g1 + t·g2 mod 1}` in `T^(k+1)` (`ObsRootTorus.torusGap`), `N ≥ 3`, and an
integer vector `w` lying in the real span of `g1, g2` (`w ∈ U ∩ ℤ^n`), with `0 < |w_r| < N` for every
coordinate.

* `crystallographic_pair`: if `u` is a unit mod `N` such that exactly one coordinate `p` has
  `|w_p| = u` and exactly one coordinate `q` has `|w_q| = N - u`, and the loneliness of `U` never exceeds
  `1/N`, then the forms of `p` and `q` are proportional (`g1 p * g2 q - g2 p * g1 q = 0`).
* `crystallographic_lemma`: if `|w|` takes each value `1..N-1` once except one value `a` taken
  twice, and the forms are pairwise non-proportional, then `φ(N) = 2` and `a ∈ {1, N-1}`.
* `totient_eq_two_iff`: for `N ≥ 3`, `φ(N) = 2 ↔ N ∈ {3, 4, 6}`.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.ObsRootTorus
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Coprime.Lemmas

set_option linter.unnecessarySeqFocus false

namespace LRSpectrumFull
namespace ObsCrystallographic

open ObsRootTorus

/-! ## Section 1: facts on `nearestIntDist` -/

theorem nd_exists_nearest (y : ℝ) : ∃ m : ℤ, nearestIntDist y = |y - m| := by
  have hf := Int.floor_add_fract y
  have hf0 := Int.fract_nonneg y
  have hf1 := Int.fract_lt_one y
  rcases le_total (Int.fract y) (1 / 2) with h | h
  · refine ⟨⌊y⌋, ?_⟩
    have e : nearestIntDist y = Int.fract y := by
      unfold nearestIntDist; exact min_eq_left (by linarith)
    rw [e, abs_of_nonneg (by linarith)]; linarith
  · refine ⟨⌊y⌋ + 1, ?_⟩
    have e : nearestIntDist y = 1 - Int.fract y := by
      unfold nearestIntDist; exact min_eq_right (by linarith)
    rw [e]; push_cast
    rw [abs_of_nonpos (by linarith)]; linarith

/-- `‖x‖ ≤ ‖x + δ‖ + |δ|`. -/
theorem nd_le_add (x δ : ℝ) : nearestIntDist x ≤ nearestIntDist (x + δ) + |δ| := by
  obtain ⟨m, hm⟩ := nd_exists_nearest (x + δ)
  have h1 := nearestIntDist_le_dist x m
  have h2 : |x - m| ≤ |x + δ - m| + |δ| := by
    have : x - m = (x + δ - m) + (-δ) := by ring
    rw [this]
    calc |(x + δ - m) + (-δ)| ≤ |x + δ - m| + |-δ| := abs_add_le _ _
      _ = |x + δ - m| + |δ| := by rw [abs_neg]
  rw [hm]; linarith

/-- Sign and integer shift do not change `‖·‖`. -/
theorem nd_sign_shift (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (y : ℝ) (m : ℤ) :
    nearestIntDist ((σ : ℝ) * y + (m : ℝ)) = nearestIntDist y := by
  rw [nearestIntDist_add_int]
  rcases hσ with rfl | rfl
  · simp
  · simp [nearestIntDist_neg]

/-- A residue `ρ ∈ [2, N-2]` gives distance at least `2/N`. -/
theorem nd_mod_ge (c : ℤ) (N : ℕ) (hN : 0 < N) (h2 : 2 ≤ c % (N : ℤ))
    (h3 : c % (N : ℤ) ≤ (N : ℤ) - 2) : 2 / (N : ℝ) ≤ nearestIntDist ((c : ℝ) / N) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hdiv := Int.emod_add_mul_ediv c N
  have hlt : c % (N : ℤ) < N := Int.emod_lt_of_pos c (by exact_mod_cast hN)
  have e : (c : ℝ) / N = ((c % (N : ℤ) : ℤ) : ℝ) / N + ((c / (N : ℤ) : ℤ) : ℝ) := by
    have : (c : ℝ) = ((c % (N : ℤ) : ℤ) : ℝ) + N * ((c / (N : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast hdiv.symm
    rw [this]; field_simp
  rw [e, nearestIntDist_add_int]
  have h2R : (2 : ℝ) ≤ ((c % (N : ℤ) : ℤ) : ℝ) := by exact_mod_cast h2
  have h3R : ((c % (N : ℤ) : ℤ) : ℝ) ≤ (N : ℝ) - 2 := by exact_mod_cast h3
  apply nearestIntDist_ge
  · positivity
  · rw [div_lt_one hNR]; exact_mod_cast hlt
  · exact div_le_div_of_nonneg_right h2R hNR.le
  · rw [le_sub_iff_add_le, ← add_div, div_le_one hNR]; linarith

/-! ## Section 2: the residue lemma -/

theorem res_lemma (N : ℕ) (hN : 3 ≤ N) (j b u w : ℤ) (hjb : j * u + b * N = 1) (hu0 : 0 < u)
    (huN : u < N) (hw0 : w ≠ 0) (hwN : |w| < N) :
    (2 ≤ (j * w) % (N : ℤ) ∧ (j * w) % (N : ℤ) ≤ (N : ℤ) - 2) ∨
      w = u ∨ w = u - N ∨ w = -u ∨ w = N - u := by
  have hNpos : (0 : ℤ) < N := by exact_mod_cast (by omega : 0 < N)
  have hcop : IsCoprime (N : ℤ) j := ⟨b, u, by linarith⟩
  have hr0 : 0 ≤ (j * w) % (N : ℤ) := Int.emod_nonneg _ hNpos.ne'
  have hr1 : (j * w) % (N : ℤ) < N := Int.emod_lt_of_pos _ hNpos
  have hdef : (j * w) % (N : ℤ) = j * w - N * (j * w / N) := Int.emod_def _ _
  obtain ⟨hwl, hwr⟩ := abs_lt.mp hwN
  by_cases h0 : (j * w) % (N : ℤ) = 0
  · exfalso
    have hd : (N : ℤ) ∣ j * w := ⟨j * w / N, by linarith⟩
    have hd2 : (N : ℤ) ∣ w := hcop.dvd_of_dvd_mul_left hd
    obtain ⟨m, hm⟩ := hd2
    have : m = 0 := by
      by_contra hm0
      rcases lt_or_gt_of_ne hm0 with h | h
      · nlinarith
      · nlinarith
    subst this
    simp at hm
    exact hw0 hm
  by_cases h1 : (j * w) % (N : ℤ) = 1
  · right
    have hd : (N : ℤ) ∣ j * (w - u) := ⟨j * w / N + b, by nlinarith⟩
    have hd2 : (N : ℤ) ∣ w - u := hcop.dvd_of_dvd_mul_left hd
    obtain ⟨m, hm⟩ := hd2
    have hm1 : m < 1 := by
      by_contra h; push Not at h; nlinarith
    have hm2 : -2 < m := by
      by_contra h; push Not at h; nlinarith
    interval_cases m
    · right; left; linarith
    · left; linarith
  by_cases h2 : (j * w) % (N : ℤ) = (N : ℤ) - 1
  · right
    have hd : (N : ℤ) ∣ j * (w + u) := ⟨j * w / N + 1 - b, by nlinarith⟩
    have hd2 : (N : ℤ) ∣ w + u := hcop.dvd_of_dvd_mul_left hd
    obtain ⟨m, hm⟩ := hd2
    have hm1 : m < 2 := by
      by_contra h; push Not at h; nlinarith
    have hm2 : -1 < m := by
      by_contra h; push Not at h; nlinarith
    interval_cases m
    · right; right; left; linarith
    · right; right; right; linarith
  left
  constructor <;> omega

/-! ## Section 3: the pair of unit heights -/

/-- **Crystallographic pair lemma.**  `w` lies in the real span of `g1, g2`, all `|w_r| ∈ (0, N)`,
`u` is a unit mod `N`, `p` (resp. `q`) is the only coordinate with `|w| = u` (resp. `N - u`), and the
loneliness of the torus never exceeds `1/N`: then the forms of `p` and `q` are proportional. -/
theorem crystallographic_pair {k : ℕ} (g1 g2 w : Fin (k + 1) → ℤ) (N : ℕ) (hN : 3 ≤ N)
    (hw : ∃ s0 t0 : ℝ, ∀ r, (w r : ℝ) = s0 * g1 r + t0 * g2 r)
    (hw0 : ∀ r, w r ≠ 0) (hwN : ∀ r, |w r| < N)
    (u : ℤ) (hu0 : 0 < u) (huN : u < N) (hcop : IsCoprime u (N : ℤ))
    (p q : Fin (k + 1)) (hp : |w p| = u) (hq : |w q| = N - u)
    (hpu : ∀ r, |w r| = u → r = p) (hqu : ∀ r, |w r| = N - u → r = q)
    (hM : ∀ s t, torusGap g1 g2 s t ≤ 1 / (N : ℝ)) :
    g1 p * g2 q - g2 p * g1 q = 0 := by
  by_contra hΔ
  obtain ⟨s0, t0, hw⟩ := hw
  obtain ⟨j, b, hjb⟩ := hcop
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  -- signs
  obtain ⟨σp, hσp, hwp⟩ : ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ w p = σ * u := by
    rcases (abs_eq hu0.le).mp hp with h | h
    · exact ⟨1, Or.inl rfl, by rw [h]; ring⟩
    · exact ⟨-1, Or.inr rfl, by rw [h]; ring⟩
  obtain ⟨σq, hσq, hwq⟩ : ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ w q = σ * (N - u) := by
    rcases (abs_eq (by linarith : (0 : ℤ) ≤ N - u)).mp hq with h | h
    · exact ⟨1, Or.inl rfl, by rw [h]; ring⟩
    · exact ⟨-1, Or.inr rfl, by rw [h]; ring⟩
  have hσpR : (σp : ℝ) * σp = 1 := by rcases hσp with rfl | rfl <;> simp
  have hσqR : (σq : ℝ) * σq = 1 := by rcases hσq with rfl | rfl <;> simp
  -- the direction z
  set Δ : ℝ := (g1 p : ℝ) * g2 q - (g2 p : ℝ) * g1 q with hΔdef
  have hΔR : Δ ≠ 0 := by
    intro h; apply hΔ
    have : ((g1 p * g2 q - g2 p * g1 q : ℤ) : ℝ) = 0 := by push_cast; linarith
    exact_mod_cast this
  set zs : ℝ := ((σp : ℝ) * g2 q + (σq : ℝ) * g2 p) / Δ with hzs
  set zt : ℝ := -((σq : ℝ) * g1 p + (σp : ℝ) * g1 q) / Δ with hzt
  set ζ : Fin (k + 1) → ℝ := fun r => (g1 r : ℝ) * zs + (g2 r : ℝ) * zt with hζ
  have hζp : ζ p = σp := by
    simp only [hζ, hzs, hzt]; field_simp; rw [hΔdef]; ring
  have hζq : ζ q = -σq := by
    simp only [hζ, hzs, hzt]; field_simp; rw [hΔdef]; ring
  set B : ℝ := ∑ r, |ζ r| with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun r _ => abs_nonneg _)
  have hζB : ∀ r, |ζ r| ≤ B := fun r =>
    Finset.single_le_sum (f := fun r => |ζ r|) (fun r _ => abs_nonneg _) (Finset.mem_univ r)
  set ε : ℝ := 1 / (2 * N * (1 + B)) with hε
  have hεpos : 0 < ε := by positivity
  have hεB : ε * B < 1 / (2 * N) := by
    rw [hε, div_mul_eq_mul_div, one_mul, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hε2 : 2 * ε ≤ 1 / N := by
    have : ε ≤ 1 / (2 * N) := by
      rw [hε]; apply one_div_le_one_div_of_le (by positivity); nlinarith
    have h2 : 2 * (1 / (2 * (N : ℝ))) = 1 / N := by field_simp
    linarith
  -- the perturbed point
  set s : ℝ := (j : ℝ) / N * s0 + ε * zs with hs
  set t : ℝ := (j : ℝ) / N * t0 + ε * zt with ht
  have hval : ∀ r, (g1 r : ℝ) * s + (g2 r : ℝ) * t = (j : ℝ) * (w r) / N + ε * ζ r := by
    intro r
    simp only [hs, ht, hζ]
    have := hw r
    rw [this]; ring
  have hjbR : (j : ℝ) * u + b * N = 1 := by exact_mod_cast hjb
  have hy_ge : 1 / (N : ℝ) + ε ≤ nearestIntDist (1 / (N : ℝ) + ε) := by
    apply nearestIntDist_ge
    · positivity
    · have : (1 : ℝ) / N ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hN3
      linarith
    · exact le_refl _
    · have : (1 : ℝ) / N ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hN3
      linarith
  have hgap : 1 / (N : ℝ) < torusGap g1 g2 s t := by
    rw [lt_torusGap_iff]
    intro r
    rw [hval r]
    by_cases hrp : r = p
    · subst hrp
      have e : (j : ℝ) * (w r) / N + ε * ζ r =
          (σp : ℝ) * (1 / (N : ℝ) + ε) + ((-σp * b : ℤ) : ℝ) := by
        rw [hζp, hwp]; push_cast
        field_simp
        have h0 : (j : ℝ) * u = 1 - b * N := by linarith
        have h3 : (σp : ℝ) * ((j : ℝ) * u) = σp * (1 - b * N) := by rw [h0]
        linarith [h3]
      rw [e, nd_sign_shift σp hσp]
      linarith
    by_cases hrq : r = q
    · subst hrq
      have e : (j : ℝ) * (w r) / N + ε * ζ r =
          ((-σq : ℤ) : ℝ) * (1 / (N : ℝ) + ε) + ((σq * j + σq * b : ℤ) : ℝ) := by
        rw [hζq, hwq]; push_cast
        field_simp
        have h0 : (j : ℝ) * u = 1 - b * N := by linarith
        have h3 : (σq : ℝ) * ((j : ℝ) * u) = σq * (1 - b * N) := by rw [h0]
        linarith [h3]
      rw [e, nd_sign_shift (-σq) (by rcases hσq with rfl | rfl <;> simp) ]
      linarith
    · -- all other coordinates are at distance at least 2/N before the perturbation
      have hres := res_lemma N hN j b u (w r) hjb hu0 huN (hw0 r) (hwN r)
      have hmid : 2 ≤ (j * w r) % (N : ℤ) ∧ (j * w r) % (N : ℤ) ≤ (N : ℤ) - 2 := by
        rcases hres with h | h | h | h | h
        · exact h
        · exfalso; apply hrp; apply hpu; rw [h]; exact abs_of_pos hu0
        · exfalso; apply hrq; apply hqu; rw [h, abs_of_neg (by linarith)]; ring
        · exfalso; apply hrp; apply hpu; rw [h, abs_neg]; exact abs_of_pos hu0
        · exfalso; apply hrq; apply hqu; rw [h]; exact abs_of_pos (by linarith)
      have h2N := nd_mod_ge (j * w r) N (by omega) hmid.1 hmid.2
      have hcast : (((j * w r : ℤ)) : ℝ) / N = (j : ℝ) * (w r) / N := by push_cast; ring
      rw [hcast] at h2N
      have hlip := nd_le_add ((j : ℝ) * (w r) / N) (ε * ζ r)
      have hz : |ε * ζ r| ≤ ε * B := by
        rw [abs_mul, abs_of_pos hεpos]
        exact mul_le_mul_of_nonneg_left (hζB r) hεpos.le
      have h2' : (2 : ℝ) / N = 1 / N + 1 / N := by ring
      have hh : 1 / (2 * (N : ℝ)) < 1 / N := by
        apply one_div_lt_one_div_of_lt hNR; linarith
      linarith
  have := hM s t
  linarith

/-! ## Section 4: the totient condition -/

theorem nat_coprime_of_isCoprime {a b : ℕ} (h : IsCoprime (a : ℤ) (b : ℤ)) : Nat.Coprime a b :=
  Nat.isCoprime_iff_coprime.mp h

theorem isCoprime_of_nat_coprime {a b : ℕ} (h : Nat.Coprime a b) : IsCoprime (a : ℤ) (b : ℤ) :=
  Nat.isCoprime_iff_coprime.mpr h

theorem coprime_pred_self (N : ℕ) (hN : 1 ≤ N) : Nat.Coprime N (N - 1) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  simp

/-- **Crystallographic lemma.**  The coordinates of `w ∈ U ∩ ℤ^n` have absolute values
`1, ..., N-1`, with the value `a` taken twice; the forms are pairwise non-proportional; the loneliness of
`U` never exceeds `1/N`.  Then `φ(N) = 2` and `a ∈ {1, N-1}`. -/
theorem crystallographic_lemma {k : ℕ} (g1 g2 w : Fin (k + 1) → ℤ) (N : ℕ) (hN : 3 ≤ N)
    (hw : ∃ s0 t0 : ℝ, ∀ r, (w r : ℝ) = s0 * g1 r + t0 * g2 r)
    (hw0 : ∀ r, w r ≠ 0) (hwN : ∀ r, |w r| < N) (a : ℕ)
    (hheights : ∀ h : ℕ, 1 ≤ h → h < N →
      (Finset.univ.filter (fun r => |w r| = (h : ℤ))).card = if h = a then 2 else 1)
    (hnp : ∀ p q, p ≠ q → g1 p * g2 q - g2 p * g1 q ≠ 0)
    (hM : ∀ s t, torusGap g1 g2 s t ≤ 1 / (N : ℝ)) :
    Nat.totient N = 2 ∧ (a = 1 ∨ a = N - 1) := by
  -- Step A: every unit height is `a` or `N - a`
  have hA : ∀ u : ℕ, 1 ≤ u → u < N → Nat.Coprime N u → (u = a ∨ N - u = a) := by
    intro u hu1 huN hcop
    by_contra hcon
    push Not at hcon
    obtain ⟨hua, hNua⟩ := hcon
    have hne : u ≠ N - u := by
      intro h
      have h2 : N = 2 * u := by omega
      have : u ∣ N := ⟨2, by omega⟩
      have h1 := Nat.Coprime.eq_one_of_dvd hcop.symm this
      omega
    have hc1 := hheights u hu1 huN
    have hc2 := hheights (N - u) (by omega) (by omega)
    rw [if_neg hua] at hc1
    rw [if_neg hNua] at hc2
    obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc1
    obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hc2
    have hpm : |w p| = (u : ℤ) := by
      have : p ∈ Finset.univ.filter (fun r => |w r| = (u : ℤ)) := by rw [hp]; simp
      simpa using this
    have hqm : |w q| = ((N - u : ℕ) : ℤ) := by
      have : q ∈ Finset.univ.filter (fun r => |w r| = ((N - u : ℕ) : ℤ)) := by rw [hq]; simp
      simpa using this
    have hpu : ∀ r, |w r| = (u : ℤ) → r = p := by
      intro r hr
      have : r ∈ Finset.univ.filter (fun r => |w r| = (u : ℤ)) := by simpa using hr
      rw [hp] at this; simpa using this
    have hqu : ∀ r, |w r| = ((N - u : ℕ) : ℤ) → r = q := by
      intro r hr
      have : r ∈ Finset.univ.filter (fun r => |w r| = ((N - u : ℕ) : ℤ)) := by simpa using hr
      rw [hq] at this; simpa using this
    have hcast : ((N - u : ℕ) : ℤ) = (N : ℤ) - u := by omega
    rw [hcast] at hqm hqu
    have hpq : p ≠ q := by
      intro h
      rw [h] at hpm
      rw [hpm] at hqm
      omega
    have hcopZ : IsCoprime (u : ℤ) (N : ℤ) :=
      isCoprime_of_nat_coprime hcop.symm
    exact hnp p q hpq
      (crystallographic_pair g1 g2 w N hN hw hw0 hwN u (by exact_mod_cast hu1)
        (by exact_mod_cast huN) hcopZ p q hpm hqm hpu hqu hM)
  -- Step B: counting units
  have hU : (Finset.range N).filter (fun u => N.Coprime u) ⊆ {a, N - a} := by
    intro u hu
    rw [Finset.mem_filter, Finset.mem_range] at hu
    obtain ⟨huN, hcop⟩ := hu
    have hu1 : 1 ≤ u := by
      rcases Nat.eq_zero_or_pos u with h | h
      · subst h
        simp at hcop; omega
      · exact h
    rcases hA u hu1 huN hcop with h | h
    · simp [h]
    · simp; right; omega
  have h1U : 1 ∈ (Finset.range N).filter (fun u => N.Coprime u) := by
    rw [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, Nat.coprime_one_right N⟩
  have hN1U : N - 1 ∈ (Finset.range N).filter (fun u => N.Coprime u) := by
    rw [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, coprime_pred_self N (by omega)⟩
  have hcard_ge : 2 ≤ ((Finset.range N).filter (fun u => N.Coprime u)).card := by
    have hsub : ({1, N - 1} : Finset ℕ) ⊆ (Finset.range N).filter (fun u => N.Coprime u) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact h1U
      · exact hN1U
    have := Finset.card_le_card hsub
    rw [Finset.card_pair (by omega)] at this
    exact this
  have hcard_le : ((Finset.range N).filter (fun u => N.Coprime u)).card ≤ 2 :=
    (Finset.card_le_card hU).trans (Finset.card_le_two)
  refine ⟨by rw [Nat.totient_eq_card_coprime]; omega, ?_⟩
  have := hU h1U
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  omega

theorem coprime_two_odd (c : ℕ) : Nat.Coprime (2 * c + 1) 2 := by
  have : IsCoprime ((2 * c + 1 : ℕ) : ℤ) ((2 : ℕ) : ℤ) := ⟨1, -(c : ℤ), by push_cast; ring⟩
  exact nat_coprime_of_isCoprime this

theorem coprime_cons_odd (c : ℕ) : Nat.Coprime (2 * c + 1) (2 * c + 3) := by
  have : IsCoprime ((2 * c + 1 : ℕ) : ℤ) ((2 * c + 3 : ℕ) : ℤ) :=
    ⟨(c : ℤ) + 1, -(c : ℤ), by push_cast; ring⟩
  exact nat_coprime_of_isCoprime this

theorem coprime_fourfold (c : ℕ) : Nat.Coprime (2 * c + 1) (4 * c + 4) := by
  have : IsCoprime ((2 * c + 1 : ℕ) : ℤ) ((4 * c + 4 : ℕ) : ℤ) :=
    ⟨(2 * c : ℤ) + 1, -(c : ℤ), by push_cast; ring⟩
  exact nat_coprime_of_isCoprime this

/-- Outside `{3, 4, 6}` the integer `N ≥ 3` has a unit `u` with `2 ≤ u ≤ N - 2`. -/
theorem exists_mid_unit (N : ℕ) (hN : 3 ≤ N) (h3 : N ≠ 3) (h4 : N ≠ 4) (h6 : N ≠ 6) :
    ∃ u, 2 ≤ u ∧ u + 2 ≤ N ∧ Nat.Coprime N u := by
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' N
  · obtain ⟨r, hr | hr⟩ := Nat.even_or_odd' m
    · -- N = 4 r, r ≥ 2: u = 2 (r - 1) + 1
      obtain ⟨c, hc⟩ : ∃ c, r = c + 1 := ⟨r - 1, by omega⟩
      refine ⟨2 * c + 1, by omega, by omega, ?_⟩
      have : N = 4 * c + 4 := by omega
      rw [this]; exact (coprime_fourfold c).symm
    · -- N = 4 r + 2, r ≥ 2: u = 2 (r - 1) + 1
      obtain ⟨c, hc⟩ : ∃ c, r = c + 1 := ⟨r - 1, by omega⟩
      refine ⟨2 * c + 1, by omega, by omega, ?_⟩
      have : N = 2 * (2 * c + 3) := by omega
      rw [this]
      exact (Nat.Coprime.mul_right (coprime_two_odd c) (coprime_cons_odd c)).symm
  · refine ⟨2, le_refl _, by omega, ?_⟩
    rw [hm]
    exact coprime_two_odd m

theorem totient_eq_two_iff (N : ℕ) (hN : 3 ≤ N) :
    Nat.totient N = 2 ↔ N = 3 ∨ N = 4 ∨ N = 6 := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    obtain ⟨h3, h4, h6⟩ := hcon
    obtain ⟨u, hu2, huN, hcop⟩ := exists_mid_unit N hN h3 h4 h6
    have hsub : ({1, u, N - 1} : Finset ℕ) ⊆ (Finset.range N).filter (fun u => N.Coprime u) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_filter, Finset.mem_range]
      rcases hx with rfl | rfl | rfl
      · exact ⟨by omega, Nat.coprime_one_right N⟩
      · exact ⟨by omega, hcop⟩
      · exact ⟨by omega, coprime_pred_self N (by omega)⟩
    have hc3 : ({1, u, N - 1} : Finset ℕ).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_pair (by omega)]
    have := Finset.card_le_card hsub
    rw [hc3, ← Nat.totient_eq_card_coprime] at this
    omega
  · rintro (rfl | rfl | rfl) <;> decide

/-! ## Section 5: non-vacuity, the G2 torus and its tight vector `w = (1,1,2,3,4,5)` -/

/-- The hypotheses of `crystallographic_lemma` hold for the `G2` torus (`N = 6`, `a = 1`), and the
conclusion `φ(6) = 2`, `a = 1` is the one that occurs. -/
theorem G2_instance : Nat.totient 6 = 2 ∧ (1 = 1 ∨ 1 = 6 - 1) := by
  have hw : ∃ s0 t0 : ℝ, ∀ r : Fin 6,
      (((![1, 1, 2, 3, 4, 5] : Fin 6 → ℤ) r : ℤ) : ℝ) = s0 * G2g1 r + t0 * G2g2 r := by
    refine ⟨1, 1, ?_⟩
    intro r
    fin_cases r <;> norm_num [G2g1, G2g2]
  exact crystallographic_lemma G2g1 G2g2 ![1, 1, 2, 3, 4, 5] 6 (by norm_num) hw
    (by decide) (by decide) 1
    (by
      intro h h1 h2
      interval_cases h <;> decide)
    (by decide)
    (by
      have := G2_upper
      simpa using this)

end ObsCrystallographic
end LRSpectrumFull
