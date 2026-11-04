-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildProgram
import BeaconcryptCore.Computational.RegistrationNativeServerBindingReceipt
/-! Every reached complete leaf of the literal SDK Builder prefix uses its actual moved source token. The exact begin-completion receipt is derived from the lookup/reservation AST, including all refusal branches. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildInitialScope
open BeaconcryptCore.Refinement
open RegistrationNativePlatformPublicAdapterBuildProgram (Spec)
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]

def Allowed (token :beaconcrypt_public_wrapper.server.RegistrationOutput) (control :pqxdh.ServerState) :Spec.Domain→Prop
  | .inr (.inr (.inr (self,initial)))=>self.control=control ∧
      ∃pin availability application,
        registration.begin_server_completion control pin availability token.registration.agreement application=.ok (.Ok initial)
  | _=>True

private def returned {A :Type} (result :RustM A)
    (next :A→OracleComp Spec AdapterPublicServerBuildTrace.Word) :OracleComp Spec AdapterPublicServerBuildTrace.Word :=
  match result with
  | .fail error=>pure (none,.fail error)
  | .div=>pure (none,.div)
  | .ok value=>next value

private def checked {A Error :Type} (self :beaconcrypt_public_wrapper.server.Server)
    (result :RustM (core.result.Result A Error))
    (next :A→OracleComp Spec AdapterPublicServerBuildTrace.Word) :OracleComp Spec AdapterPublicServerBuildTrace.Word :=
  match result with
  | .fail error=>pure (none,.fail error)
  | .div=>pure (none,.div)
  | .ok (.Err _)=>pure (none,.ok (.None,self))
  | .ok (.Ok value)=>next value

omit [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
private theorem returned_scope {A :Type} (allowed :Spec.Domain→Prop) (result :RustM A)
    (next :A→OracleComp Spec AdapterPublicServerBuildTrace.Word)
    (safe :∀value,(next value).AllQueriesSatisfy allowed) :
    (returned result next).AllQueriesSatisfy allowed :=by
  cases result with
  | fail error | div=>exact allQueriesSatisfy_pure _ _
  | ok value=>exact safe value

omit [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
private theorem checked_scope {A Error :Type} (allowed :Spec.Domain→Prop) (self :beaconcrypt_public_wrapper.server.Server)
    (result :RustM (core.result.Result A Error)) (next :A→OracleComp Spec AdapterPublicServerBuildTrace.Word)
    (safe :∀value,result=.ok (.Ok value)→(next value).AllQueriesSatisfy allowed) :
    (checked self result next).AllQueriesSatisfy allowed :=by
  cases result with
  | fail error | div=>exact allQueriesSatisfy_pure _ _
  | ok result=>cases result with
    | Err error=>exact allQueriesSatisfy_pure _ _
    | Ok value=>exact safe value rfl

omit [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
private theorem reserved (token :beaconcrypt_public_wrapper.server.RegistrationOutput) (control :pqxdh.ServerState)
    (self :beaconcrypt_public_wrapper.server.Server) (initial :registration.ServerInitialKdf)
    (same :self.control=control)
    (admitted :∃pin availability application,
      registration.begin_server_completion control pin availability token.registration.agreement application=.ok (.Ok initial)) :
    (RegistrationNativePlatformPublicAdapterBuildProgram.reserved self initial).AllQueriesSatisfy (Allowed token control) :=by
  unfold RegistrationNativePlatformPublicAdapterBuildProgram.reserved
  rw [allQueriesSatisfy_query_bind_iff]
  refine ⟨True.intro,?_⟩
  intro reply
  cases reply with
  | fail error | div=>exact allQueriesSatisfy_pure _ _
  | ok result=>
    rcases result with ⟨result,known⟩
    cases result with
    | Err error=>exact allQueriesSatisfy_pure _ _
    | Ok value=>
      change AllQueriesSatisfy ((fun result :(AdapterPublicServerBuildTrace.Publication×RustM AdapterPublicServerBuildBody.Reply)=>(some result.1,result.2)) <$>(Spec.query (.inr (.inr (.inr ({self with known_ids:=known},initial)))) :OracleComp Spec (AdapterPublicServerBuildTrace.Publication×RustM AdapterPublicServerBuildBody.Reply))) (Allowed token control)
      rw [allQueriesSatisfy_def,isQueryBound_map_iff,←allQueriesSatisfy_def,allQueriesSatisfy_query_iff]
      exact ⟨same,admitted⟩

omit [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
private theorem lookup (token :beaconcrypt_public_wrapper.server.RegistrationOutput) (control :pqxdh.ServerState)
    (self :beaconcrypt_public_wrapper.server.Server) (pending :peer.CompletionLookup) (plaintext :Slice U8)
    (same :self.control=control) (pendingControl :pending.control=control)
    (pendingToken :pending.registration=token.registration) :
    (RegistrationNativePlatformPublicAdapterBuildProgram.lookup self pending plaintext).AllQueriesSatisfy (Allowed token control) :=by
  change AllQueriesSatisfy (returned pending.request fun identifier=>
    returned (CoreModels.core.slice.Slice.len plaintext) fun size=>
    returned (transport.registration_response_len size identifier) fun optional=>match optional with
    | .None=>pure (none,.ok (.None,self))
    | .Some _=>do
      let reply←Spec.query (.inr (.inl (self.known_ids,identifier)))
      returned reply fun occupied=>checked self (pending.resume occupied)
        (RegistrationNativePlatformPublicAdapterBuildProgram.reserved self)) (Allowed token control)
  apply returned_scope
  intro identifier
  apply returned_scope
  intro size
  apply returned_scope
  intro optional
  cases optional with
  | none=>exact allQueriesSatisfy_pure _ _
  | some capacity=>
    rw [allQueriesSatisfy_query_bind_iff]
    refine ⟨True.intro,?_⟩
    intro reply
    apply returned_scope
    intro occupied
    apply checked_scope
    intro initial resumed
    apply reserved token control self initial same
    refine ⟨pending.pin,(if occupied then .Occupied else .Available),pending.application,?_⟩
    simpa only [PeerOwnership.completion_lookup_resume,pendingControl,pendingToken] using resumed

omit [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem program (self :beaconcrypt_public_wrapper.server.Server)
    (token :beaconcrypt_public_wrapper.server.RegistrationOutput) (data :core.option.Option (Slice U8)) :
    (RegistrationNativePlatformPublicAdapterBuildProgram.program self token data).AllQueriesSatisfy (Allowed token self.control) :=by
  change AllQueriesSatisfy (returned (transport.normalize_registration_application data) fun application=>
    returned (beaconcrypt_public_wrapper.server.registration_application_bytes application) fun plaintext=>do
      let reply←Spec.query (.inl self)
      returned reply fun optional=>match optional with
      | .None=>pure (none,.ok (.None,self))
      | .Some pin=>checked self (peer.begin_completion_lookup self.control pin token.registration plaintext)
        (fun pending=>RegistrationNativePlatformPublicAdapterBuildProgram.lookup self pending plaintext)) (Allowed token self.control)
  apply returned_scope
  intro application
  apply returned_scope
  intro plaintext
  rw [allQueriesSatisfy_query_bind_iff]
  refine ⟨True.intro,?_⟩
  intro reply
  apply returned_scope
  intro optional
  cases optional with
  | none=>exact allQueriesSatisfy_pure _ _
  | some pin=>
    apply checked_scope
    intro pending began
    obtain ⟨currentControl,_pin,currentToken,_application⟩:=RegistrationNativeServerBindingReceipt.lookup_fields self.control pin token.registration plaintext pending began
    exact lookup token self.control self pending plaintext rfl currentControl currentToken

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildInitialScope
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildInitialScope.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildInitialScope.program
