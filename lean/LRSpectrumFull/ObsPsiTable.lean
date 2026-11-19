/-
# Theorem PSI, table of levels `N0(n)` for primitive tori, `12 ≤ n ≤ 71`

Companion of `ObsPsiBound`: the cardinalities `|P¹(ℤ/N)| = ψ(N)` for `N = 18, 24, 30` (kernel `decide`,
no `native_decide`) and the resulting bounds `torusML ≥ 1/N` for primitive 2-tori with
`12 ≤ n ≤ 71` forms:

| n         | level N | ψ(N) |
|-----------|---------|------|
| 12 .. 17  | 10      | 18   |
| 18 .. 23  | 12      | 24   |
| 24 .. 35  | 18      | 36   |
| 36 .. 47  | 24      | 48   |
| 48 .. 71  | 30      | 72   |

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.ObsPsiBound

namespace LRSpectrumFull
namespace ObsPsiTable

open ObsRootTorus ObsPsiBound

theorem card_projReps_18 : (projReps 18).card = 36 := by decide +kernel
theorem card_projReps_24 : (projReps 24).card = 48 := by decide +kernel
theorem card_projReps_30 : (projReps 30).card = 72 := by decide +kernel

theorem psiDed_table : psiDed 18 = 36 ∧ psiDed 24 = 48 ∧ psiDed 30 = 72 := by decide +kernel

/-- `torusML ≥ 1/N` for primitive tori, from the cardinality `ψ(N)` of the projective line. -/
theorem torusML_ge_of_primitive_card {k : ℕ} (g1 g2 : Fin (k + 1) → ℤ) (hp : Primitive g1 g2)
    (N : ℕ) (hN : 0 < N) (hcard : k + 1 < (projReps N).card) : 1 / (N : ℝ) ≤ torusML g1 g2 :=
  torusML_ge_inv_of_projReps g1 g2 N hN (fun r => contentCoprime_of_primitive (hp r) N) hcard

theorem torusML_ge_primitive_table {k : ℕ} (g1 g2 : Fin (k + 1) → ℤ) (hp : Primitive g1 g2) :
    (12 ≤ k + 1 → k + 1 ≤ 17 → 1 / ((10 : ℕ) : ℝ) ≤ torusML g1 g2) ∧
    (18 ≤ k + 1 → k + 1 ≤ 23 → 1 / ((12 : ℕ) : ℝ) ≤ torusML g1 g2) ∧
    (24 ≤ k + 1 → k + 1 ≤ 35 → 1 / ((18 : ℕ) : ℝ) ≤ torusML g1 g2) ∧
    (36 ≤ k + 1 → k + 1 ≤ 47 → 1 / ((24 : ℕ) : ℝ) ≤ torusML g1 g2) ∧
    (48 ≤ k + 1 → k + 1 ≤ 71 → 1 / ((30 : ℕ) : ℝ) ≤ torusML g1 g2) := by
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · exact torusML_ge_of_primitive_card g1 g2 hp 10 (by norm_num)
      (by rw [card_projReps_10]; omega)
  · exact torusML_ge_of_primitive_card g1 g2 hp 12 (by norm_num)
      (by rw [card_projReps_12]; omega)
  · exact torusML_ge_of_primitive_card g1 g2 hp 18 (by norm_num)
      (by rw [card_projReps_18]; omega)
  · exact torusML_ge_of_primitive_card g1 g2 hp 24 (by norm_num)
      (by rw [card_projReps_24]; omega)
  · exact torusML_ge_of_primitive_card g1 g2 hp 30 (by norm_num)
      (by rw [card_projReps_30]; omega)

end ObsPsiTable
end LRSpectrumFull
