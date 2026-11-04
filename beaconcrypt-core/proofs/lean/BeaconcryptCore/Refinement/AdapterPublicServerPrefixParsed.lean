-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerPrefixFrame
import BeaconcryptCore.Refinement.RegistrationAuthenticationReparse
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! An actual lookup returned by the same pin/authentication prefix carries repeatable source Ed parsing for its original bound Beacon identity. This is derived from its actual accepted parse/open sequence and read-only primitive parsing; no validity or parse-success premise is supplied for arbitrary input bytes. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerPrefixParsed
open BeaconcryptCore.Computational
variable [ed : AdapterInitEdPrimitive.Operations]
variable {n : Nat} {I KemSK Reader Response : Type} {base : OracleSpec I}
attribute [local irreducible] RegistrationAuthenticationExecutor.begin

noncomputable def parser (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (verify : MldsaTranscriptAuth.Verify)
    (edLaws : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto) :
    RegistrationAuthenticationReparse.Parser
      (RegistrationNativePlatformAuthentication.native (n := n) (QueryImpl.id' unifSpec) setup codec route verify edLaws) where
  parse := edLaws.parse
  source := edLaws.parseRun
  native := by intro bytes; rfl

theorem reparse (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (verify : MldsaTranscriptAuth.Verify)
    (edLaws : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (events : List RegistrationAuthenticationFlow.Event) (authenticated : registration.AuthenticatedInit)
    (before after : PqxdhRecordLiftWorld.State n)
    (called : (.ok (events, .Accepted authenticated), after) ∈ support
      ((RegistrationWorldAuthentication.begin setup codec route verify pin packet).run before)) :
    AdapterPublicServerToken.ParsedKey authenticated.binding.beacon_identity_public_key := by
  let native := RegistrationNativePlatformAuthentication.native (n := n) (QueryImpl.id' unifSpec) setup codec route verify edLaws
  have callbacks : native ∘ₛ AdapterInitAuthenticationStateful.abstractNative =
      RegistrationNativePlatformAuthentication.core (QueryImpl.id' unifSpec) setup codec route verify := by
    funext query
    exact RegistrationNativePlatformAuthentication.abstract_query (QueryImpl.id' unifSpec) setup codec route verify edLaws query
  have run : (simulateQ (native ∘ₛ AdapterInitAuthenticationStateful.abstractNative)
      (RegistrationAuthenticationExecutor.begin pin packet)).run before =
      (RegistrationWorldAuthentication.begin setup codec route verify pin packet).run before := by
    rw [callbacks, AdapterPublicServerAuthenticationPrefix.core_run, simulateQ_id']
  exact RegistrationAuthenticationReparse.reparse native (parser setup codec route verify edLaws)
    pin packet events authenticated before after (by rw [run]; exact called)

theorem program {PlatformState : Type}
    (coins : QueryImpl unifSpec (StateT PlatformState ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (edLaws : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)
    (control : pqxdh.ServerState) (binding : pqxdh.ServerBinding) (publicKey : Std.Array U8 1952#usize)
    (packet : registration.InitPacket) (before after : PqxdhRecordLiftWorld.State n)
    (pending : peer.RegistrationLookup) (previous next : PlatformState)
    (supported : ((.ok (.Some pending), after), next) ∈ support
      (((AdapterPublicServerAuthenticationPrefix.program coins setup codec route verify edLaws control binding publicKey packet).run before).run previous)) :
    AdapterPublicServerToken.ParsedKey pending.authenticated.binding.beacon_identity_public_key := by
  simp only [AdapterPublicServerAuthenticationPrefix.program, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨⟨pinReply, middle⟩, between⟩, _called, continued⟩ := supported
  rw [AdapterPublicServerAuthenticationPrefix.after_pin_run] at continued
  cases pinReply with
  | fail error | div =>
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
      reduceCtorEq, false_and] at continued
  | ok optional => cases optional with
    | none =>
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
        RustM.ok.injEq, reduceCtorEq, false_and] at continued
    | some pin =>
      simp only [StateT.run_map, support_map] at continued
      obtain ⟨⟨⟨authenticated, current⟩, finalExternal⟩, checked, returned⟩ := continued
      obtain ⟨events, same, _control⟩ := AdapterPublicServerPrefixFrame.observed control authenticated pending
        (congrArg (fun value => value.1.1) returned)
      have actual := RegistrationNativePlatformHashReceipt.native_support coins _ (authenticated, current) between finalExternal checked
      rw [same] at actual
      exact reparse setup codec route verify edLaws pin packet events pending.authenticated middle current actual

end BeaconcryptCore.Refinement.AdapterPublicServerPrefixParsed

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerPrefixParsed.reparse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerPrefixParsed.reparse

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerPrefixParsed.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerPrefixParsed.program
