-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerAuthenticationPrefix
import BeaconcryptCore.Computational.RegistrationNativePlatformHashReceipt
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! Every actual pin/authentication prefix preserves installed Server records and returns a lookup capability with the original source control. The facts follow from actual hash effects and original Core lookup construction, without a whole authentication-frame premise. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerPrefixFrame
open BeaconcryptCore.Computational
variable [ed : AdapterInitEdPrimitive.Operations]
variable {n : Nat} {I KemSK Reader Response : Type} {base : OracleSpec I}

omit ed in
theorem observed (control : pqxdh.ServerState)
    (reply : RustM (List RegistrationAuthenticationFlow.Event × registration.InitAuthentication))
    (pending : peer.RegistrationLookup)
    (returned : AdapterPublicServerAuthentication.observed control reply = .ok (.Some pending)) :
    ∃ events, reply = .ok (events, .Accepted pending.authenticated) ∧ pending.control = control := by
  cases reply with
  | fail error | div => cases returned
  | ok pair =>
    rcases pair with ⟨events, state⟩
    cases state <;> simp only [AdapterPublicServerAuthentication.observed,
      AdapterInitAuthenticationDriver.observe, AdapterInitAuthenticationStateful.stateOption,
      bind_tc_ok, PeerOwnership.registration_lookup_begin, RustM.ok.injEq, reduceCtorEq] at returned
    case Accepted authenticated =>
      cases returned
      exact ⟨events, rfl, rfl⟩

attribute [local irreducible] RegistrationWorldAuthentication.begin RegistrationAuthenticationExecutor.begin

theorem program_server {PlatformState : Type}
    (coins : QueryImpl unifSpec (StateT PlatformState ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (edLaws : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (control : pqxdh.ServerState) (binding : pqxdh.ServerBinding) (publicKey : Std.Array U8 1952#usize)
    (packet : registration.InitPacket) (before after : PqxdhRecordLiftWorld.State n)
    (reply : RustM (core.option.Option peer.RegistrationLookup)) (previous next : PlatformState)
    (supported : ((reply, after), next) ∈ support
      (((AdapterPublicServerAuthenticationPrefix.program coins setup codec route verify edLaws control binding publicKey packet).run before).run previous)) :
    after.server = before.server := by
  simp only [AdapterPublicServerAuthenticationPrefix.program, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨⟨pinReply, middle⟩, between⟩, called, continued⟩ := supported
  change ((pinReply, middle), between) ∈ support
    ((simulateQ coins ((RegistrationNativeServerPinRecompute.native binding publicKey).run before)).run previous) at called
  have pinFrame := AdapterPublicServerPrefixMaterial.pin_server binding publicKey before middle pinReply
    (RegistrationNativePlatformHashReceipt.native_support coins _ (pinReply, middle) previous between called)
  rw [AdapterPublicServerAuthenticationPrefix.after_pin_run] at continued
  cases pinReply with
  | fail error | div =>
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at continued
    have same := congrArg (fun value => value.1.2) continued
    cases same
    exact pinFrame
  | ok pin => cases pin with
    | none =>
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at continued
      have same := congrArg (fun value => value.1.2) continued
      cases same
      exact pinFrame
    | some pin =>
      simp only [StateT.run_map, support_map] at continued
      obtain ⟨⟨⟨authenticated, current⟩, finalExternal⟩, checked, returned⟩ := continued
      have same := congrArg (fun value => value.1.2) returned
      cases same
      exact (AdapterPublicServerAuthenticationFrame.begin_server setup codec route verify pin packet middle after authenticated
        (RegistrationNativePlatformHashReceipt.native_support coins _ (authenticated, after) between finalExternal checked)).trans pinFrame


theorem program_lookup {PlatformState : Type}
    (coins : QueryImpl unifSpec (StateT PlatformState ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (edLaws : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (control : pqxdh.ServerState) (binding : pqxdh.ServerBinding) (publicKey : Std.Array U8 1952#usize)
    (packet : registration.InitPacket) (before after : PqxdhRecordLiftWorld.State n)
    (pending : peer.RegistrationLookup) (previous next : PlatformState)
    (supported : ((.ok (.Some pending), after), next) ∈ support
      (((AdapterPublicServerAuthenticationPrefix.program coins setup codec route verify edLaws control binding publicKey packet).run before).run previous)) :
    pending.control = control := by
  simp only [AdapterPublicServerAuthenticationPrefix.program, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨⟨pinReply, middle⟩, between⟩, _called, continued⟩ := supported
  rw [AdapterPublicServerAuthenticationPrefix.after_pin_run] at continued
  cases pinReply with
  | fail error | div =>
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
      reduceCtorEq, false_and] at continued
  | ok pin => cases pin with
    | none =>
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
        RustM.ok.injEq, reduceCtorEq, false_and] at continued
    | some pin =>
      simp only [StateT.run_map, support_map] at continued
      obtain ⟨⟨⟨authenticated, current⟩, finalExternal⟩, _checked, returned⟩ := continued
      exact (observed control authenticated pending (congrArg (fun value => value.1.1) returned)).choose_spec.2


end BeaconcryptCore.Refinement.AdapterPublicServerPrefixFrame

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerPrefixFrame.observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerPrefixFrame.observed

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerPrefixFrame.program_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerPrefixFrame.program_server

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerPrefixFrame.program_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerPrefixFrame.program_lookup
