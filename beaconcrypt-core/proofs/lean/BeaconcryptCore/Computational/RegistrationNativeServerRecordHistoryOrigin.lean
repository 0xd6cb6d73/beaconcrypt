-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeServerRecordIssuance
import BeaconcryptCore.Computational.RegistrationNativeMldsaRoleFrame
import BeaconcryptCore.Computational.RegistrationNativeStageJournal
import BeaconcryptCore.Computational.RegistrationNativeMldsaInitializedChronology

/-! Every Server-role receipt in one actual native source history originates at a same-run earlier response build, with its actual moved token and root-bearing source record stage. The derivation includes failed signing, encoding and insertion and does not assume prior-stage provenance. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeServerRecordHistoryOrigin
open RegistrationNativeStageTrace (Call Path Executed)
open RegistrationNativeMldsaRoleFrame (serverReceipts NonBuild)
open RegistrationNativeServerRecordIssuance (history)
open RegistrationSigningShared (Receipt)
open BeaconcryptCore.Refinement.RegistrationSigningTrace (Command)
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK V : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "implementation" => RegistrationNativeExperiment.handler setup checks wire route representation created source credential
attribute [local irreducible] RegistrationNativeExperiment.handler

def SourceAt (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (call : Call RegistrationNativeRawAdapter.TypedSpec Native) (receipt : Receipt) : Prop :=
  ∃ index application token current plaintext availability initial hashed,
    call.query = .inr (.build index application) ∧
    RegistrationServerSdkSource.take index call.before.server = (some token, current) ∧ application = some plaintext ∧
    BeaconcryptCore.Refinement.RegistrationAd.ServerAdmission current.control current.pin availability token.agreement plaintext initial ∧
    RegistrationServerRecordExecutor.Path initial hashed ∧
    RegistrationNativeServerRecordIssuance.RecordCut (n := n) setup (RegistrationNativeWire.ledgerCodec wire) initial hashed (RegistrationNativeWorldCache.cache call.after) ∧
    receipt.observation.publicKey = hashed.binding.server_pin.public_key ∧ receipt.observation.payload = Command.payload (.server hashed)

private theorem call_origin (call : Call RegistrationNativeRawAdapter.TypedSpec Native) (called : Executed implementation call)
    (receipt : Receipt) (member : receipt ∈ serverReceipts (history call.after.server)) :
    receipt ∈ serverReceipts (history call.before.server) ∨ SourceAt setup wire call receipt := by
  rcases call with ⟨query, before, reply, after⟩
  by_cases allowed : NonBuild query
  · have frame : serverReceipts (history after.server) = serverReceipts (history before.server) :=
      RegistrationNativeMldsaRoleFrame.handler setup checks wire route representation created credential query allowed before (reply, after) called
    exact Or.inl (frame ▸ member)
  · cases query with
    | inl coin => exact False.elim (allowed trivial)
    | inr query => cases query with
      | build index application =>
          obtain ⟨raw, role⟩ := List.mem_filter.mp member
          by_cases prior : receipt ∈ history before.server
          · exact Or.inl (List.mem_filter.mpr ⟨prior, role⟩)
          · obtain ⟨token, current, plaintext, availability, initial, hashed, taken, input, admitted, path, recordCut, key, payload⟩ :=
              RegistrationNativeServerRecordIssuance.new_receipt setup checks wire route representation created credential index application before after
                reply called receipt raw prior
            exact Or.inr ⟨index, application, token, current, plaintext, availability, initial, hashed, rfl,
              taken, input, admitted, path, recordCut, key, payload⟩
      | _ => exact False.elim (allowed trivial)

/-- A complete native source path attributes each final Server receipt to an identical initial receipt or its actual earlier root-bearing build stage. -/
theorem path_origin {first last : Native} {calls : List (Call RegistrationNativeRawAdapter.TypedSpec Native)}
    (actual : Path implementation first calls last) (receipt : Receipt)
    (member : receipt ∈ serverReceipts (history last.server)) :
    receipt ∈ serverReceipts (history first.server) ∨ ∃ call ∈ calls, SourceAt setup wire call receipt := by
  induction actual with
  | nil => exact Or.inl member
  | cons call called rest last following ih =>
      rcases ih member with previous | ⟨earlier, inRest, stage⟩
      · rcases call_origin setup checks wire route representation created credential call called receipt previous with old | stage
        · exact Or.inl old
        · exact Or.inr ⟨call, List.mem_cons_self, stage⟩
      · exact Or.inr ⟨earlier, List.mem_cons_of_mem _ inRest, stage⟩


end BeaconcryptCore.Computational.RegistrationNativeServerRecordHistoryOrigin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerRecordHistoryOrigin.path_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerRecordHistoryOrigin.path_origin
