-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAccept
/-! An actual normal SDK acceptance word cannot have come from a failed or diverging private agreement capture. This is a syntactic implication through the original source replay, reservation, lookup and acceptance programs, independent of any primitive normality, source model or material invariant. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptReceiptNormal
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativePlatformSdkReification (Backend)
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {n :Nat} {I KemSK P R Error :Type} {base :OracleSpec I} {source :RegistrationNativeMldsa.Source}
variable (containers :ContainerOperations (RustT (StateT P ProbComp)))
open AdapterPublicServerAgreementReceipt (Receipt Word)

theorem replay (self :beaconcrypt_public_wrapper.server.Server) (receipt :Receipt R)
    (previous next :P) (actual :Word R)
    (supported :(.ok actual,next)∈support ((RegistrationNativePlatformPublicAdapterAcceptReceipt.replay containers self receipt).run previous)) :
    ∃captured,receipt=.ok captured :=by
  cases receipt with
  | ok captured=>exact ⟨captured,rfl⟩
  | fail error | div=>
    simp only [RegistrationNativePlatformPublicAdapterAcceptReceipt.replay,StateT.run_pure,mem_support_pure_iff] at supported
    cases supported

variable [original :CryptoOperations (RustT ProbComp)]
variable (coins :QueryImpl unifSpec (StateT P ProbComp)) (generator :rand_core.TryCryptoRng R Error)

theorem receipt (keys :AdapterPublicAgreementFields.Keys) (self :beaconcrypt_public_wrapper.server.Server)
    (work :OracleComp RegistrationAgreementExecutor.Spec (RustM agreement.AgreementEffect)) (rng :R)
    (before :Backend n KemSK) (previous :P)
    (result :((Receipt R×RustM (Word R))×Backend n KemSK)×P) (actual :Word R)
    (supported :result∈support (((RegistrationNativePlatformPublicAdapterAcceptReceipt.program containers coins generator keys self work rng).run before).run previous))
    (normal :result.1.1.2=.ok actual) :∃captured,result.1.1.1=.ok captured :=by
  unfold RegistrationNativePlatformPublicAdapterAcceptReceipt.program at supported
  simp only [StateT.run_bind,bind_pure_comp,mem_support_bind_iff] at supported
  obtain ⟨captured,_capturedSupport,supported⟩:=supported
  simp only [StateT.run_map,StateT.run_lift,bind_pure_comp,Functor.map_map,support_map] at supported
  obtain ⟨returned,returnedSupport,same⟩:=supported
  cases same
  exact replay containers self captured.1.1 captured.2 returned.2 actual (by rw [←normal];exact returnedSupport)

theorem reservation (self :beaconcrypt_public_wrapper.server.Server) (control :pqxdh.ServerState)
    (authenticated :registration.AuthenticatedInit) (rng :R) (before :Backend n KemSK) (previous :P)
    (result :((AdapterPublicServerReservationReceipt.Receipt R×RustM (Word R))×Backend n KemSK)×P) (actual :Word R)
    (supported :result∈support (((RegistrationNativePlatformPublicAdapterAcceptLookup.reservation containers coins generator self control authenticated rng).run before).run previous))
    (normal :result.1.1.2=.ok actual) :result.1.1.1=none ∨∃captured,result.1.1.1=some (.ok captured) :=by
  unfold RegistrationNativePlatformPublicAdapterAcceptLookup.reservation at supported
  simp only [StateT.run_bind,StateT.run_lift,mem_support_bind_iff] at supported
  obtain ⟨allocated,_allocatedSupport,supported⟩:=supported
  cases allocation:allocated.1.1 with
  | fail error | div=>
    simp only [allocation,StateT.run_pure,mem_support_pure_iff] at supported
    cases supported
    exact Or.inl rfl
  | ok pair=>
    rcases pair with ⟨business,history⟩
    cases business with
    | Err error=>
      simp only [allocation,StateT.run_pure,mem_support_pure_iff] at supported
      cases supported
      exact Or.inl rfl
    | Ok _accepted=>
      simp only [allocation,StateT.run_map,support_map] at supported
      obtain ⟨called,calledSupport,same⟩:=supported
      cases same
      obtain ⟨captured,formed⟩:=receipt containers coins generator _ _ _ rng allocated.1.2 allocated.2 called actual calledSupport normal
      exact Or.inr ⟨captured,congrArg some formed⟩

theorem lookup (self :beaconcrypt_public_wrapper.server.Server) (pending :peer.RegistrationLookup)
    (rng :R) (before :Backend n KemSK) (previous :P)
    (result :((AdapterPublicServerReservationReceipt.Receipt R×RustM (Word R))×Backend n KemSK)×P) (actual :Word R)
    (supported :result∈support (((RegistrationNativePlatformPublicAdapterAcceptLookup.lookup containers coins generator self pending rng).run before).run previous))
    (normal :result.1.1.2=.ok actual) :result.1.1.1=none ∨∃captured,result.1.1.1=some (.ok captured) :=by
  unfold RegistrationNativePlatformPublicAdapterAcceptLookup.lookup at supported
  simp only [StateT.run_bind,StateT.run_lift,mem_support_bind_iff] at supported
  obtain ⟨observed,_observedSupport,supported⟩:=supported
  cases queried:observed.1.1 with
  | fail error | div=>
    simp only [queried,StateT.run_pure,mem_support_pure_iff] at supported
    cases supported
    exact Or.inl rfl
  | ok present=>cases present with
    | true=>
      simp only [queried,StateT.run_pure,mem_support_pure_iff] at supported
      cases supported
      exact Or.inl rfl
    | false=>
      simp only [queried] at supported
      exact reservation containers coins generator self pending.control pending.authenticated rng observed.1.2 observed.2 result actual supported normal

variable (setup :PqxdhServerAuthExperiment.Setup base KemSK) (checks :PqxdhServerAuthExperiment.Checks)
variable (verify :MldsaTranscriptAuth.Verify) (representation :RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created :PqxdhLiveServerConstruction.Created Unit)

theorem program (view :AdapterPublicWrapperState.MaterialView source KemSK)
    (self :beaconcrypt_public_wrapper.server.Server) (input :Slice U8) (rng :R)
    (before :Backend n KemSK) (previous :P)
    (result :((AdapterPublicServerReservationReceipt.Receipt R×RustM (Word R))×Backend n KemSK)×P) (actual :Word R)
    (supported :result∈support (((RegistrationNativePlatformPublicAdapterAccept.program containers coins setup checks verify representation created generator view self input rng).run before).run previous))
    (normal :result.1.1.2=.ok actual) :result.1.1.1=none ∨∃captured,result.1.1.1=some (.ok captured) :=by
  unfold RegistrationNativePlatformPublicAdapterAccept.program at supported
  cases decoded:RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input) with
  | none=>
    simp only [decoded,StateT.run_pure,mem_support_pure_iff] at supported
    cases supported
    exact Or.inl rfl
  | some packet=>
    simp only [decoded,StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨checked,_checkedSupport,supported⟩:=supported
    cases authenticated:checked.1.1 with
    | fail error | div=>
      simp only [authenticated,StateT.run_pure,mem_support_pure_iff] at supported
      cases supported
      exact Or.inl rfl
    | ok optional=>cases optional with
      | none=>
        simp only [authenticated,StateT.run_pure,mem_support_pure_iff] at supported
        cases supported
        exact Or.inl rfl
      | some pending=>
        simp only [authenticated] at supported
        exact lookup containers coins generator self pending rng checked.1.2 checked.2 result actual supported normal

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptReceiptNormal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptReceiptNormal.replay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptReceiptNormal.replay

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptReceiptNormal.receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptReceiptNormal.receipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptReceiptNormal.reservation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptReceiptNormal.reservation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptReceiptNormal.lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptReceiptNormal.lookup

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptReceiptNormal.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptReceiptNormal.program
