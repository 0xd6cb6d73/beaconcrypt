-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceTrace
/-! Protected unsigned issuance is read from actual source signing requests, keyed only by their public key. Both roles and failed replies remain chronological; key aliases are permitted. This source history is independent of native owner indexes and private credential representations. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceSigningHistory
open BeaconcryptCore.Refinement
open RegistrationNativePlatformPublicAdapterSourceTrace (Stage recorded signingObservation)

def receipt : Stage → Option RegistrationSigningShared.Receipt
  | .sign request payload digest reply => some ⟨⟨request.public_key,payload,RegistrationSigningTrace.replyBytes reply⟩,digest⟩
  | _ => none

def receipts (log : List Stage) : List RegistrationSigningShared.Receipt := log.filterMap receipt

def history (publicKey : Pqxdh.Bytes) (log : List Stage) : List MldsaTranscriptAuth.SigningCall :=
  RegistrationSigningTrace.historyFor publicKey ((receipts log).map RegistrationSigningShared.Receipt.observation)

theorem append_receipts (leading trailing : List Stage) :
    receipts (leading ++ trailing)=receipts leading ++ receipts trailing := List.filterMap_append

def Aligned (current : RegistrationSigningShared.State × List Stage) : Prop :=
  current.1.1=receipts current.2

/-- The actual hash/sign source interpreter appends exactly the receipt observed at that same signing leaf. -/
theorem query (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (request : RegistrationSigningShared.Spec.Domain) (before : RegistrationSigningShared.State × List Stage)
    (aligned : Aligned before) (result : RegistrationSigningShared.Spec.Range request × (RegistrationSigningShared.State × List Stage))
    (supported : result ∈ support ((recorded (RegistrationSigningShared.implementation sign) signingObservation request).run before)) :
    Aligned result.2 := by
  cases request with
  | hash request =>
    simp only [recorded,RegistrationSigningShared.implementation,MldsaSharedNative.authentication,
      StateT.run,Functor.map_map,support_map] at supported
    obtain ⟨inner,_called,same⟩ := supported
    cases same
    simpa only [Aligned,signingObservation,receipts,List.filterMap_append,List.filterMap_cons,
      List.filterMap_nil,receipt,List.append_nil] using aligned
  | sign request payload digest =>
    simp only [recorded,RegistrationSigningShared.implementation,StateT.run,Functor.map_map,support_map] at supported
    obtain ⟨reply,_called,same⟩ := supported
    cases same
    change before.1.1 ++ [_] = receipts (before.2 ++ [_])
    rw [append_receipts]
    change before.1.1 ++ [_] = receipts before.2 ++ [_]
    rw [aligned]

/-- Arbitrary source continuations retain exactly their actual signing history, including every missing reply and failed later publication. -/
theorem program {A : Type} (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp RegistrationSigningShared.Spec A) (before : RegistrationSigningShared.State × List Stage)
    (aligned : Aligned before) (result : A × (RegistrationSigningShared.State × List Stage))
    (supported : result ∈ support ((simulateQ (recorded (RegistrationSigningShared.implementation sign) signingObservation) work).run before)) :
    Aligned result.2 :=
  PqxdhRecordLiftFlat.support_keep_oracle _ Aligned (query sign) work before aligned result supported

theorem history_eq (publicKey : Pqxdh.Bytes) (current : RegistrationSigningShared.State × List Stage)
    (aligned : Aligned current) : RegistrationSigningShared.historyFor publicKey current.1=history publicKey current.2 := by
  unfold RegistrationSigningShared.historyFor history
  rw [aligned]

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceSigningHistory

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceSigningHistory.append_receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceSigningHistory.append_receipts
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceSigningHistory.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceSigningHistory.query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceSigningHistory.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceSigningHistory.program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceSigningHistory.history_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceSigningHistory.history_eq
