-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAcceptFresh
import BeaconcryptCore.Computational.RegistrationNativeResponsePaired
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetLedger

/-! A successful actual Word accept always returns its fresh append index under the same raw/full outer interpretation. This rules out an earlier successful build of that handle when cutting one actual chronological path. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAcceptFreshSource
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSecretWordTargetSource (State)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
local notation "typedImpl" => RegistrationNativeSecretWordTargetSource.typed (n := n) (source := source)
  setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey
local notation "rawImpl" => RegistrationNativeRawAdapter.handler wire typedImpl
attribute [local irreducible] RegistrationNativeSecretWordServerCompiler.accept
  RegistrationNativeSecretWordTargetSource.typed RegistrationNativeSecretWordTargetSource.implementation
  RegistrationNativeSecretWordInterpreter.handler

private theorem frontend (packet : registration.InitPacket) (handle : Nat)
    (before after : RegistrationNativeSecretWordMessage.State source)
    (supported : (.ok (some handle), after) ∈ support
      ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept
        publicPrekey (.inr (.accept packet))).run before)) : handle = before.server.sessions.length := by
  simp only [RegistrationNativeSecretWordFrontend.handler, StateT.run_bind, StateT.run_get,
    StateT.run_modify, pure_bind] at supported
  simp only [RegistrationNativeSecretWordFrontend.serverOpen, StateT.run, support_map] at supported
  obtain ⟨result, reached, returned⟩ := supported
  have original := RegistrationNativeResponsePaired.simulation_support
    (RegistrationNativeSecretWordInterface.liftLocal (decide (before.parsedAccepts = selectedAccept))) _ _ reached
  have success : result.1.1 = .ok (some handle) := congrArg Prod.fst returned
  rcases result with ⟨⟨reply, server⟩, env⟩
  dsimp only at success
  subst reply
  exact (RegistrationNativeSecretWordAcceptFresh.success setup checks source.verify packet before.server before.environment
    server env handle original).1

/-- Arbitrary outer protected-key replies preserve the exact fresh successful accept index. -/
theorem typed (packet : registration.InitPacket) (handle : Nat) (before after : State n KemSK source)
    (supported : (.ok (some handle), after) ∈ support ((typedImpl (.inr (.accept packet))).run before)) :
    handle = before.1.server.sessions.length := by
  rw [RegistrationNativeSecretWordTargetSource.typed_run, support_map] at supported
  obtain ⟨result, reached, returned⟩ := supported
  have original : result.1 ∈ support
      ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept
        publicPrekey (.inr (.accept packet))).run before.1) := by
    apply OracleComp.support_simulateQ_run'_subset
      (RegistrationNativeSecretWordTargetSource.implementation setup wire route sign input inside provider outer) _ before.2
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst reached
  have success : result.1.1 = .ok (some handle) := congrArg Prod.fst returned
  rcases result with ⟨⟨reply, front⟩, current⟩
  dsimp only at success
  subst reply
  exact frontend setup checks wire sign selectedOwner selectedAccept publicPrekey packet handle before.1 front original

/-- The same successfully decoded original raw accept returns that fresh index. -/
theorem raw (raw : Pqxdh.Bytes) (packet : registration.InitPacket) (handle : Nat)
    (decoded : RegistrationNativeWire.readInit wire raw = some packet) (before after : State n KemSK source)
    (supported : (some handle, after) ∈ support ((rawImpl (.inr (.accept raw))).run before)) :
    handle = before.1.server.sessions.length := by
  simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose, RegistrationNativeRawAdapter.adapter,
    decoded, simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map] at supported
  obtain ⟨⟨reply, current⟩, reached, returned⟩ := supported
  cases actual : reply with
  | fail error | div => simp [actual, RegistrationNativeRawAdapter.resultOption] at returned
  | ok reply =>
      simp only [actual, RegistrationNativeRawAdapter.resultOption, Prod.mk.injEq] at returned
      obtain ⟨rfl, rfl⟩ := returned
      exact typed setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey
        packet handle before _ (by simpa only [actual] using reached)

/-- The original complete ledger accept retains its same actual pre-call fresh index. -/
theorem full (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (raw : Pqxdh.Bytes) (packet : registration.InitPacket) (handle : Nat)
    (decoded : RegistrationNativeWire.readInit wire raw = some packet)
    (before after : RegistrationNativeLedger.State × State n KemSK source)
    (supported : (some handle, after) ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId
      bounds typedImpl (.inl (.inr (.accept raw)))).run before)) : handle = before.2.1.server.sessions.length := by
  rw [RegistrationNativeSecretWordTargetLedger.core_run, support_map] at supported
  obtain ⟨⟨reply, current⟩, reached, returned⟩ := supported
  have success : reply = some handle := congrArg Prod.fst returned
  subst reply
  exact RegistrationNativeSecretWordAcceptFreshSource.raw setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey
    raw packet handle decoded before.2 current reached

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAcceptFreshSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAcceptFreshSource.typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAcceptFreshSource.typed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAcceptFreshSource.raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAcceptFreshSource.raw
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAcceptFreshSource.full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAcceptFreshSource.full
