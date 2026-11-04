-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.RegistrationHeaderOptimalExtraction.Funs
import BeaconcryptCore.Refinement.RegistrationHeaderCanonical
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
/-! Exact optimal-width source decisions for each raw size tag produced by
the header reader, plus acceptance of every source factory result. Each decision
covers every U64 value, including noncanonical values below its lower threshold;
upper bounds arise from the actual typed reader and are not assumed here. Full
private byte-scan and public malformed-input rejection are separate obligations. -/
namespace BeaconcryptCore.Refinement.RegistrationHeaderOptimal
open beaconcrypt_parse.cbordetveraux RegistrationHeaderCanonical

theorem size0 (value : U64) :
    impl_raw_uint64_optimal { size := 0#u8, value := value } = .ok (decide (value.val < 24)) := by
  simp [impl_raw_uint64_optimal, max_simple_value_additional_info, lift]
  split_ifs <;> simp_all <;> omega

theorem size1 (value : U64) :
    impl_raw_uint64_optimal { size := 1#u8, value := value } = .ok (decide (24 ≤ value.val)) := by
  simp [impl_raw_uint64_optimal, max_simple_value_additional_info, lift]
  split_ifs <;> simp_all <;> omega

theorem size2 (value : U64) :
    impl_raw_uint64_optimal { size := 2#u8, value := value } = .ok (decide (256 ≤ value.val)) := by
  simp [impl_raw_uint64_optimal, max_simple_value_additional_info, lift]
  omega

theorem size3 (value : U64) :
    impl_raw_uint64_optimal { size := 3#u8, value := value } = .ok (decide (65536 ≤ value.val)) := by
  simp [impl_raw_uint64_optimal, max_simple_value_additional_info, lift]
  omega

theorem size4 (value : U64) :
    impl_raw_uint64_optimal { size := 4#u8, value := value } = .ok (decide (4294967296 ≤ value.val)) := by
  simp [impl_raw_uint64_optimal, max_simple_value_additional_info, lift]
  omega

theorem factory_optimal (value : U64) :
    (do let raw ← mk_raw_uint64 value; impl_raw_uint64_optimal raw) = .ok true := by
  simp only [mk_raw_uint64, max_simple_value_additional_info, lift, bind_tc_ok]
  split_ifs with small byte word16 word32
  · rw [bind_tc_ok, size0]
    congr 1
    simp only [decide_eq_true_eq]
    scalar_tac
  · rw [bind_tc_ok, size1]
    congr 1
    simp only [decide_eq_true_eq]
    scalar_tac
  · rw [bind_tc_ok, size2]
    congr 1
    simp only [decide_eq_true_eq]
    scalar_tac
  · rw [bind_tc_ok, size3]
    congr 1
    simp only [decide_eq_true_eq]
    scalar_tac
  · rw [bind_tc_ok, size4]
    congr 1
    simp only [decide_eq_true_eq]
    scalar_tac

end BeaconcryptCore.Refinement.RegistrationHeaderOptimal

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderOptimal.size0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderOptimal.size0

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderOptimal.size1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderOptimal.size1

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderOptimal.size2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderOptimal.size2

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderOptimal.size3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderOptimal.size3

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderOptimal.size4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderOptimal.size4

/-- info: 'BeaconcryptCore.Refinement.RegistrationHeaderOptimal.factory_optimal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationHeaderOptimal.factory_optimal
