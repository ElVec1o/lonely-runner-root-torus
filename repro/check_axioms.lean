/-
# check_axioms.lean : print the axioms of the declarations that the paper lists. Builds NOTHING.

Run through `check_axioms.sh` (which runs `lake env lean check_axioms.lean` and checks the printout).
It only needs the .olean files of the 7 modules of MANIFEST.tsv (build them first with build.sh).

Every `#print axioms` below must print exactly the three standard axioms [propext, Classical.choice, Quot.sound],
except the planted control at the end, which must print `sorryAx` (it shows that a `sorry` anywhere below a
theorem would be visible in this printout).  The expected number of axiom lines is the number of `#print axioms`
commands in this file (check_axioms.sh counts them).
-/
import LRSpectrumFull.ObsRootTorus
import LRSpectrumFull.ObsConeLemma
import LRSpectrumFull.ObsCrystallographic
import LRSpectrumFull.ObsPsiBound
import LRSpectrumFull.ObsPsiTable

/-! ## Theorem 1 (root tori) and its companions: ObsRootTorus -/
#print axioms LRSpectrumFull.ObsRootTorus.torusML_A2
#print axioms LRSpectrumFull.ObsRootTorus.torusML_B2
#print axioms LRSpectrumFull.ObsRootTorus.torusML_G2
#print axioms LRSpectrumFull.ObsRootTorus.torusGap_diag
#print axioms LRSpectrumFull.ObsRootTorus.torusML_JK_U2
#print axioms LRSpectrumFull.ObsRootTorus.torusML_Cordella_UC
#print axioms LRSpectrumFull.ObsRootTorus.JK_U2_forms_eq_B2
#print axioms LRSpectrumFull.ObsRootTorus.Cordella_UC_forms_eq_G2
#print axioms LRSpectrumFull.ObsRootTorus.control_A2'
#print axioms LRSpectrumFull.ObsRootTorus.control_B2'
#print axioms LRSpectrumFull.ObsRootTorus.control_G2'
#print axioms LRSpectrumFull.ObsRootTorus.torusML_zero_snd

/-! ## Theorem 2 (repeat lines): ObsConeLemma -/
#print axioms LRSpectrumFull.ObsConeLemma.cone_lemma
#print axioms LRSpectrumFull.ObsConeLemma.cone_lemma_normalised
#print axioms LRSpectrumFull.ObsConeLemma.A2_free_card
#print axioms LRSpectrumFull.ObsConeLemma.A2_slope_card

/-! ## Theorem 3 (totient condition): ObsCrystallographic -/
#print axioms LRSpectrumFull.ObsCrystallographic.crystallographic_pair
#print axioms LRSpectrumFull.ObsCrystallographic.crystallographic_lemma
#print axioms LRSpectrumFull.ObsCrystallographic.G2_instance
#print axioms LRSpectrumFull.ObsCrystallographic.totient_eq_two_iff

/-! ## Theorem 4 (torsion points) and its corollaries: ObsPsiBound, ObsPsiTable -/
#print axioms LRSpectrumFull.ObsPsiBound.det_dvd_of_both_kill
#print axioms LRSpectrumFull.ObsPsiBound.exists_unkilled
#print axioms LRSpectrumFull.ObsPsiBound.torusML_ge_inv_of_indep
#print axioms LRSpectrumFull.ObsPsiBound.torusML_ge_inv_of_two_mul_sub_totient
#print axioms LRSpectrumFull.ObsPsiBound.torusML_ge_inv_of_projReps
#print axioms LRSpectrumFull.ObsPsiBound.torusML_gt_inv_of_primitive
#print axioms LRSpectrumFull.ObsPsiBound.primitive_critical_card
#print axioms LRSpectrumFull.ObsPsiBound.primitive_totient_two
#print axioms LRSpectrumFull.ObsPsiBound.torusML_ge_one_sixth_of_primitive
#print axioms LRSpectrumFull.ObsPsiBound.torusML_A2_primitive
#print axioms LRSpectrumFull.ObsPsiBound.torusML_B2_primitive
#print axioms LRSpectrumFull.ObsPsiBound.torusML_G2_primitive
#print axioms LRSpectrumFull.ObsPsiTable.torusML_ge_primitive_table
#print axioms LRSpectrumFull.ObsPsiTable.torusML_ge_of_primitive_card
#print axioms LRSpectrumFull.ObsPsiTable.psiDed_table

/-! ## NEGATIVE CONTROL (must print sorryAx; check_axioms.sh requires it) -/

theorem check_axioms_planted_sorry : (1 : Nat) = 2 := by sorry
theorem check_axioms_planted_sorry_user : (2 : Nat) = 3 := by
  have := check_axioms_planted_sorry
  omega

#print axioms check_axioms_planted_sorry
#print axioms check_axioms_planted_sorry_user
