-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServer
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLivePrefix

/-! Preparation validity and the exact retained Server descriptor flags form the internal whole-frontend invariant. Ordinary owner, record and World callbacks leave the Server session table unchanged; their actual reached flags are transported by checked callback monotonicity. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendState
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSecretWordInterpreterChecked (handlerChecked)
open RegistrationNativeSecretWordLiveFlags (Valid Keeps)
open RegistrationNativeSecretWordLiveSessions (Live)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

def Good {source : RegistrationNativeMldsa.Source} (input : Message → Option Key) (before : RegistrationNativeSecretWordMessage.State source)
    (context : RegistrationNativeSecretWordInterpreter.State n KemSK) : Prop :=
  Valid input context ∧ Live before.server context.flags

private theorem beacon_server {source : RegistrationNativeMldsa.Source}
    (work : RegistrationNativeSecretWordOwners.M n KemSK RegistrationServerRoleBackend.State source Value)
    (before : RegistrationNativeSecretWordMessage.State source)
    (result : Value × RegistrationNativeSecretWordMessage.State source)
    (supported : result ∈ support ((RegistrationNativeSecretWordFrontend.beacon work).run before)) :
    result.2.server = before.server := by
  simp only [RegistrationNativeSecretWordFrontend.beacon, StateT.run, support_map] at supported
  obtain ⟨reached, _possible, equal⟩ := supported
  exact (congrArg (fun output => output.2.server) equal).symm

private theorem record_server {source : RegistrationNativeMldsa.Source}
    (query : PqxdhRecordLiftInterface.RecordQuery) (before : RegistrationNativeSecretWordMessage.State source)
    (result : (PqxdhRecordLiftInterface.RecordSpec .O).Range query × RegistrationNativeSecretWordMessage.State source)
    (supported : result ∈ support ((RegistrationNativeSecretWordFrontend.record (n := n) (KemSK := KemSK) query).run before)) :
    result.2.server = before.server := by
  rcases query with (_ | _) | ⟨owner, _ | _⟩
  all_goals simp only [RegistrationNativeSecretWordFrontend.record, StateT.run] at supported
  all_goals try split at supported
  all_goals first
    | rw [mem_support_pure_iff] at supported; cases supported; rfl
    | rw [support_map] at supported; obtain ⟨reached, _possible, equal⟩ := supported; exact (congrArg (fun output => output.2.server) equal).symm

attribute [local irreducible] RegistrationNativeSecretWordServerCompiler.accept RegistrationNativeSecretWordServerCompiler.build

/-- Every non-Server typed callback keeps the complete local Server state, under every actual reply. -/
theorem quiet_server (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (quiet : RegistrationNativeRawAdapter.kind query ≠ 3 ∧ RegistrationNativeRawAdapter.kind query ≠ 4)
    (before : RegistrationNativeSecretWordMessage.State source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × RegistrationNativeSecretWordMessage.State source)
    (supported : result ∈ support ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run before)) :
    result.2.server = before.server := by
  cases query with
  | inl coin =>
      simp only [RegistrationNativeSecretWordFrontend.handler, StateT.run_lift, bind_pure_comp, support_map] at supported
      obtain ⟨reached, _possible, equal⟩ := supported
      exact (congrArg (fun output => output.2.server) equal).symm
  | inr query => cases query with
    | create edPin mlPin keyId | bundle index | finish index packet => exact beacon_server _ before result supported
    | accept packet => exact False.elim (quiet.1 rfl)
    | build handle application => exact False.elim (quiet.2 rfl)
    | hmac key bytes =>
        simp only [RegistrationNativeSecretWordFrontend.handler, StateT.run_pure, mem_support_pure_iff] at supported
        cases supported
        rfl
    | hash bytes =>
        simp only [RegistrationNativeSecretWordFrontend.handler, StateT.run_lift, bind_pure_comp, support_map] at supported
        obtain ⟨reached, _possible, equal⟩ := supported
        exact (congrArg (fun output => output.2.server) equal).symm
    | serverSend keyId plaintext => exact record_server (.inl (.inl (plaintext, keyId))) before result supported
    | serverRaw raw => exact record_server (.inl (.inr raw)) before result supported
    | beaconSend index plaintext => exact record_server (.inr (index, .inl plaintext)) before result supported
    | beaconRaw index raw => exact record_server (.inr (index, .inr raw)) before result supported

end BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendState
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendState.quiet_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFrontendState.quiet_server
