-- SPDX-License-Identifier: 0BSD
-- Exact production preflight field lists; original Rust and EverCDDL source unchanged.
import Aeneas
import BeaconcryptCore.Refinement.RegistrationCodecFixedFields
import BeaconcryptCore.Refinement.RegistrationCodecStandardSlices

set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.RegistrationPreflightSourceCertificates
open Aeneas.Std
universe v
variable {S : Type} {m : Type → Type v} [Monad m] [LawfulMonad m]

theorem init_fields_preserved (step : S → U8 → m S) (initial : S) :
    [2#u8, 2#u8, 2#u8, 2#u8, 2#u8, 2#u8].foldlM step initial = (do
      let state0 ← step initial 2#u8
      let state1 ← step state0 2#u8
      let state2 ← step state1 2#u8
      let state3 ← step state2 2#u8
      let state4 ← step state3 2#u8
      step state4 2#u8) :=
  RegistrationCodecFixedFields.fold_six step initial 2#u8 2#u8 2#u8 2#u8 2#u8 2#u8

theorem response_fields_preserved (step : S → U8 → m S) (initial : S) :
    [2#u8, 2#u8, 2#u8, 2#u8, 0#u8, 2#u8].foldlM step initial = (do
      let state0 ← step initial 2#u8
      let state1 ← step state0 2#u8
      let state2 ← step state1 2#u8
      let state3 ← step state2 2#u8
      let state4 ← step state3 0#u8
      step state4 2#u8) :=
  RegistrationCodecFixedFields.fold_six step initial 2#u8 2#u8 2#u8 2#u8 0#u8 2#u8

end BeaconcryptCore.Refinement.RegistrationPreflightSourceCertificates

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightSourceCertificates.init_fields_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightSourceCertificates.init_fields_preserved

/-- info: 'BeaconcryptCore.Refinement.RegistrationPreflightSourceCertificates.response_fields_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationPreflightSourceCertificates.response_fields_preserved
