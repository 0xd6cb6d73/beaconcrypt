-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeTokenTrace
import BeaconcryptCore.Computational.RegistrationNativeServerAgreementInputReceipt

/-! A token taken by an actual same-run build points back to its genuine earlier Server accept and private pre-erasure root collection. No current ratchet reconstruction or paired-root equality is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeTokenRootReceipt
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhBeaconPhase2Preparation (Word32)
open RegistrationNativeStageTrace (Call Path Executed)
open RegistrationWorldAgreement (project)
attribute [local irreducible] RegistrationServerNativeSource.authenticate RegistrationServerNativeSource.agree RegistrationNativeExperiment.handler
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)

/-- The source witness retains the actual collector execution and exact checked source root input/output at the agreement cut. -/
structure Input (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before after : RegistrationServerFrontendCompiler.State n) (completed : agreement.ServerAgreement) where
  collected : PqxdhServerRootPreparation.Inputs registration.InitPacket Unit Word32
  atRoot : RawCtxSharedPrimitive.SharedState RegistrationServerRoleBackend.State
  next : pqxdh.ServerState
  original : pqxdh.PendingServerRegistration
  supported : (some collected, atRoot) ∈ support ((simulateQ (RegistrationAgreementShared.implementation setup.source
    (RegistrationServerRoleBackend.native setup checks representation created.seed))
      (simulateQ RegistrationAgreementRoot.callbacks
        (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated)))).run (project before.world))
  verified : collected.verified = RegistrationRootInput.verified packet authenticated
  accepted : PqxdhServerRelatedRootInput.accept before.control authenticated.binding.server_pin.binding collected = .ok (.Ok (next, original))
  completedEq : completed = ⟨{ original with root_key_input := ⟨Array.repeat 192#usize 0#u8⟩ },
    authenticated.binding, ⟨RegistrationAgreementShared.rootResponse setup.source.crypto ⟨original.root_key_input.bytes, pqxdh.PQXDH_INFO⟩⟩⟩
  atRootEq : project after.world = atRoot
  nextEq : next = before.control
  built : pqxdh.build_root_key_input (PqxdhServerRelatedRootInput.secrets collected) = .ok (.Ok original.root_key_input)
  bytes : absBytes original.root_key_input.bytes = Pqxdh.pqxdhIKM (absBytes collected.first) (absBytes collected.second)
    (absBytes collected.third) (absBytes collected.fourth) (absBytes collected.kem)

/-- The retained completed capability contains exactly the source HKDF root output for the collected checked input. -/
theorem Input.root (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before after : RegistrationServerFrontendCompiler.State n) (completed : agreement.ServerAgreement)
    (receipt : Input setup checks representation created packet authenticated before after completed) :
    completed.root.bytes = RegistrationAgreementShared.rootResponse setup.source.crypto
      ⟨receipt.original.root_key_input.bytes, pqxdh.PQXDH_INFO⟩ := by
  exact congrArg (fun value : agreement.ServerAgreement => value.root.bytes) receipt.completedEq

/-- Every actual supported native agreement supplies the pre-erasure root witness. -/
theorem agree (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (completed : agreement.ServerAgreement) (before after : RegistrationServerFrontendCompiler.State n)
    (supported : (.ok (.ServerComplete completed), after) ∈ support
      ((RegistrationServerNativeSource.agree setup checks representation created packet authenticated).run before)) :
    Nonempty (Input setup checks representation created packet authenticated before after completed) := by
  obtain ⟨_fresh, collected, atRoot, next, original, ran, verified, accepted, completedEq, atRootEq, nextEq, built, bytes⟩ :=
    RegistrationNativeServerAgreementInputReceipt.agree setup checks representation created packet authenticated completed before after supported
  exact ⟨⟨collected, atRoot, next, original, ran, verified, accepted, completedEq, atRootEq, nextEq, built, bytes⟩⟩

/-- Actual replay insertion leaves the consumed token attached to its precise completed agreement and source root witness. -/
theorem born (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationServerFrontendCompiler.State n) (token : peer.ConsumedRegistration)
    (birth : RegistrationNativeTokenSource.Born setup checks representation created packet authenticated before token) :
    ∃ after history,
      (.ok (.ServerComplete token.agreement), after) ∈ support
        ((RegistrationServerNativeSource.agree setup checks representation created packet authenticated).run before) ∧
      RegistrationReplaySchedule.consume token.agreement after.consumed = .ok (.Some token, history) ∧
      Nonempty (Input setup checks representation created packet authenticated before after token.agreement) := by
  obtain ⟨accepted, after, history, supported, consumed⟩ := birth
  have same := RegistrationNativeTokenSource.consume_agreement accepted after.consumed history token consumed
  rw [← same] at supported consumed
  exact ⟨after, history, supported, consumed, agree setup checks representation created packet authenticated token.agreement before after supported⟩

variable (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
    (credential : RegistrationNativeMldsa.Credential source)
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "implementation" => RegistrationNativeExperiment.handler setup checks wire route representation created source credential

/-- A token taken by a native build has an earlier actual accept with its mandatory authentication cut and reached private root inputs in that same execution. -/
theorem taken {first beforeBuild : Native} {calls : List (Call RegistrationNativeRawAdapter.TypedSpec Native)}
    (actual : Path implementation first calls beforeBuild) (empty : first.server.sessions = [])
    (index : Nat) (token : peer.ConsumedRegistration) (current : RegistrationServerFrontendCompiler.State n)
    (take : RegistrationServerSdkSource.take index beforeBuild.server = (some token, current)) :
    ∃ call leading trailing packet events authenticated afterAuthentication afterAgreement history,
      calls = leading ++ call :: trailing ∧ Path implementation first leading call.before ∧
      Executed implementation call ∧ Path implementation call.after trailing beforeBuild ∧
      call.query = .inr (.accept packet) ∧
      (.ok (events, .Accepted authenticated), afterAuthentication) ∈ support
        ((RegistrationServerNativeSource.authenticate setup (RegistrationNativeWire.ledgerCodec wire) route source.verify created packet).run call.before.server) ∧
      (.ok (.ServerComplete token.agreement), afterAgreement) ∈ support
        ((RegistrationServerNativeSource.agree setup checks representation created packet authenticated).run afterAuthentication) ∧
      RegistrationReplaySchedule.consume token.agreement afterAgreement.consumed = .ok (.Some token, history) ∧
      Nonempty (Input setup checks representation created packet authenticated afterAuthentication afterAgreement token.agreement) := by
  obtain ⟨call, leading, trailing, split, earlier, called, later, packet, events, authenticated, afterAuthentication, queryEq, checked, birth⟩ :=
    RegistrationNativeTokenTrace.taken_origin setup checks wire route representation created credential actual empty index token current take
  obtain ⟨afterAgreement, history, supported, consumed, input⟩ := born setup checks representation created packet authenticated afterAuthentication token birth
  exact ⟨call, leading, trailing, packet, events, authenticated, afterAuthentication, afterAgreement, history,
    split, earlier, called, later, queryEq, checked, supported, consumed, input⟩

end BeaconcryptCore.Computational.RegistrationNativeTokenRootReceipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTokenRootReceipt.Input.root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTokenRootReceipt.Input.root

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTokenRootReceipt.agree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTokenRootReceipt.agree

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTokenRootReceipt.born' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTokenRootReceipt.born

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTokenRootReceipt.taken' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTokenRootReceipt.taken
