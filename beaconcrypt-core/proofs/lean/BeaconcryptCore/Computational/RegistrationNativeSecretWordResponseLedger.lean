-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordResponseSource
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetLedger

/-! Original raw/full build entries retain the exact successful Word response metadata and its same pre-build stored session. This receipt includes optional application conversion and the literal original public ledger wrapper. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordResponseLedger
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

/-- The original raw response bytes come from the exact Ready moved by the same successful Word build. -/
theorem raw (handle : Nat) (payload : Option Pqxdh.Bytes)
    (response : PqxdhServerRegistrationPublication.Response) (before after : State n KemSK source)
    (supported : (some response, after) ∈ support ((rawImpl (.inr (.build handle payload))).run before)) :
    ∃ ready, before.1.server.sessions[handle]? = some (some ready) ∧
      RegistrationNativeSecretWordResponse.EncodedFrom wire ready before.1.server.pin response.serialized := by
  simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
    RegistrationNativeRawAdapter.adapter, simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map] at supported
  obtain ⟨⟨reply, current⟩, reached, returned⟩ := supported
  cases actual : reply with
  | fail error | div => simp [actual, RegistrationNativeRawAdapter.responseOption, RegistrationNativeRawAdapter.resultOption] at returned
  | ok reply => cases reply with
    | none => simp [actual, RegistrationNativeRawAdapter.responseOption, RegistrationNativeRawAdapter.resultOption] at returned
    | some reply =>
        rcases reply with ⟨keyId, bytes⟩
        simp only [actual, RegistrationNativeRawAdapter.responseOption, RegistrationNativeRawAdapter.resultOption,
          Option.map_some, Prod.mk.injEq] at returned
        obtain ⟨same, stateEq⟩ := returned
        have responseEq : (⟨bytes, keyId⟩ : PqxdhServerRegistrationPublication.Response) = response := Option.some.inj same
        cases responseEq
        cases stateEq
        exact RegistrationNativeSecretWordResponseSource.typed setup checks wire route sign input inside provider outer
          selectedOwner selectedAccept publicPrekey handle (RegistrationNativeRawAdapter.application payload) before after keyId bytes
          (by simpa only [actual] using reached)

/-- The literal original full-ledger build retains its same pre-call stored registration and response fields. -/
theorem full (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (handle : Nat) (payload : Option Pqxdh.Bytes) (response : PqxdhServerRegistrationPublication.Response)
    (before after : RegistrationNativeLedger.State × State n KemSK source)
    (supported : (some response, after) ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire
      serverKeyId bounds typedImpl (.inl (.inr (.build handle payload)))).run before)) :
    ∃ ready, before.2.1.server.sessions[handle]? = some (some ready) ∧
      RegistrationNativeSecretWordResponse.EncodedFrom wire ready before.2.1.server.pin response.serialized := by
  rw [RegistrationNativeSecretWordTargetLedger.core_run, support_map] at supported
  obtain ⟨⟨reply, current⟩, reached, returned⟩ := supported
  have success : reply = some response := congrArg Prod.fst returned
  subst reply
  exact raw setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey
    handle payload response before.2 current reached

end BeaconcryptCore.Computational.RegistrationNativeSecretWordResponseLedger

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordResponseLedger.raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordResponseLedger.raw
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordResponseLedger.full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordResponseLedger.full
