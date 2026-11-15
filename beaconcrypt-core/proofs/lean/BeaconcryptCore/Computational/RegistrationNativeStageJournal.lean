-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeStageTrace
import BeaconcryptCore.Computational.RegistrationNativeServerIssuance

/-! A new response receipt in the actual private native source journal is attached to the exact earlier build cut, moved token, root-bearing initial capability and source record path. All callback outcomes are admitted; no completed peer or later-ratchet reconstruction is used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeStageJournal
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeStageTrace (Call Path)
open RegistrationSigningShared (Receipt)
open BeaconcryptCore.Refinement.RegistrationSigningTrace (Command)
variable {n : Nat} {ι KemSK V : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
local notation "implementation" => RegistrationNativeExperiment.handler setup checks wire route representation created source credential
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

/-- A source-journal response issuance retains its exact same-run earlier native prefix and actual moved-token/root/record provenance, including failed outer build outcomes. -/
theorem build_receipt (work : OracleComp RegistrationNativeRawAdapter.TypedSpec V) (initial : Native)
    (result : V × (Native × List (Call RegistrationNativeRawAdapter.TypedSpec Native)))
    (supported : result ∈ support ((simulateQ (RegistrationNativeStageTrace.handler implementation) work).run (initial, [])))
    (index : Nat) (application : Option (Slice U8)) (beforeBuild afterBuild : Native)
    (answer : RustM (Option (U64 × Pqxdh.Bytes)))
    (member : (⟨.inr (.build index application), beforeBuild, answer, afterBuild⟩ : Call RegistrationNativeRawAdapter.TypedSpec Native) ∈ result.2.2)
    (receipt : Receipt) (recorded : receipt ∈ RegistrationNativeServerIssuance.history afterBuild.server)
    (fresh : receipt ∉ RegistrationNativeServerIssuance.history beforeBuild.server) :
    ∃ leading trailing token current plaintext availability firstRecord hashed,
      result.2.2 = leading ++ (⟨.inr (.build index application), beforeBuild, answer, afterBuild⟩ : Call RegistrationNativeRawAdapter.TypedSpec Native) :: trailing ∧
      Path implementation initial leading beforeBuild ∧ Path implementation afterBuild trailing result.2.1 ∧
      RegistrationServerSdkSource.take index beforeBuild.server = (some token, current) ∧ application = some plaintext ∧
      BeaconcryptCore.Refinement.RegistrationAd.ServerAdmission current.control current.pin availability token.agreement plaintext firstRecord ∧
      RegistrationServerRecordExecutor.Path firstRecord hashed ∧
      receipt.observation.publicKey = hashed.binding.server_pin.public_key ∧ receipt.observation.payload = Command.payload (.server hashed) := by
  have actual := RegistrationNativeStageTrace.path implementation work initial result supported
  obtain ⟨leading, trailing, split, before, called, after⟩ := actual.member
    (⟨.inr (.build index application), beforeBuild, answer, afterBuild⟩ : Call RegistrationNativeRawAdapter.TypedSpec Native) member
  obtain ⟨token, current, plaintext, availability, firstRecord, hashed, taken, input, admitted, path, key, payload⟩ :=
    RegistrationNativeServerIssuance.new_receipt setup checks wire route representation created credential index application beforeBuild afterBuild
      answer called receipt recorded fresh
  exact ⟨leading, trailing, token, current, plaintext, availability, firstRecord, hashed, split, before, after,
    taken, input, admitted, path, key, payload⟩

end BeaconcryptCore.Computational.RegistrationNativeStageJournal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeStageJournal.build_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeStageJournal.build_receipt
