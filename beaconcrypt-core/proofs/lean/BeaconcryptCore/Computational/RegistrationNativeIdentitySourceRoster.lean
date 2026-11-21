-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityRealization
import BeaconcryptCore.Computational.RegistrationNativeIdentityWorldServices

/-! Private owner realization commutes with the actual current-owner history and phase updates. In particular a signing callback never replaces current metadata with an earlier captured owner value. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentitySourceRoster
open RegistrationNativeIdentityRealization (owner owners)
variable {source : RegistrationNativeMldsa.Source}

def phaseOwners (current : RegistrationNativeIdentityFrontend.State source) (index : Nat)
    (phase : RegistrationNativeBeaconFrontend.Phase) : RegistrationNativeIdentityFrontend.State source :=
  match current[index]? with
  | none => current
  | some selected => current.set index { selected with phase }

/-- A per-owner signing attempt updates the same generated owner and signature history after private source realization. -/
theorem history_source (pool : PqxdhDynamicIdentityPool.SourceState)
    (current : RegistrationNativeIdentityFrontend.State source) (index : Nat) (message : Pqxdh.Bytes)
    (signature : PqxdhEd25519EufCma.Ed25519Signature) :
    owners pool (RegistrationNativeIdentityWorldServices.appendHistory current index message signature) =
      match (owners pool current)[index]? with
      | none => owners pool current
      | some selected => (owners pool current).set index { selected with
          edHistory := selected.edHistory ++ [.signed message signature] } := by
  simp only [RegistrationNativeIdentityWorldServices.appendHistory, owners, List.getElem?_map]
  cases found : current[index]? with
  | none => simp only [Option.map_none]
  | some selected =>
      simp only [Option.map_some, List.map_set]
      rfl

/-- Every retained phase update preserves the source identity and all reached history fields. -/
theorem phase_source (pool : PqxdhDynamicIdentityPool.SourceState)
    (current : RegistrationNativeIdentityFrontend.State source) (index : Nat)
    (phase : RegistrationNativeBeaconFrontend.Phase) :
    owners pool (phaseOwners current index phase) =
      match (owners pool current)[index]? with
      | none => owners pool current
      | some selected => (owners pool current).set index { selected with phase } := by
  simp only [phaseOwners, owners, List.getElem?_map]
  cases found : current[index]? with
  | none => simp only [Option.map_none]
  | some selected =>
      simp only [Option.map_some, List.map_set]
      rfl

end BeaconcryptCore.Computational.RegistrationNativeIdentitySourceRoster

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceRoster.history_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceRoster.history_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentitySourceRoster.phase_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentitySourceRoster.phase_source
