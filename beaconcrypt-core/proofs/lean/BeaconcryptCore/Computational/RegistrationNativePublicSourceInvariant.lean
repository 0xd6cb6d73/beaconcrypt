-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicSourceBuildLive

/-! Every actual adaptive typed frontend execution preserves its internal live-root and source-memo invariants. The unchanged original full secrecy compiler is one such typed client, so no public win or eligibility predicate requires an external root-preparation premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePublicSourceInvariant
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePublicSourceServer (State)
open RegistrationNativePublicSourceState (Live MemoCorrect)
open RegistrationNativePublicSourceExecution (execute)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationServerOpenReferenceCompiler.accept RegistrationAuthenticationCompiler.program

private theorem record_live (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (query : PqxdhRecordLiftInterface.RecordQuery) (before : State n KemSK source)
    (result : (PqxdhRecordLiftInterface.RecordSpec .O).Range query × State n KemSK source)
    (live : Live before.1 before.2) (correct : MemoCorrect setup seed scalar before.2.roots)
    (supported : result ∈ support ((execute setup wire route sign seed scalar
      (RegistrationNativePublicFrontend.record query)).run before)) :
    Live result.2.1 result.2.2 ∧ MemoCorrect setup seed scalar result.2.2.roots := by
  apply RegistrationNativePublicSourceExecution.live_of_subset setup wire route sign seed scalar _ before result _ live correct supported
  intro output reached ready member
  cases query with
  | inl query =>
      simp only [RegistrationNativePublicFrontend.record, StateT.run, support_map] at reached
      obtain ⟨reply, _possible, equal⟩ := reached
      have fixed : output.2 = before.1 := (congrArg Prod.snd equal).symm
      rwa [fixed] at member
  | inr query =>
      rcases query with ⟨owner, request⟩
      cases request <;> cases present : before.1.beacons[owner]? with
      | none =>
          simp only [RegistrationNativePublicFrontend.record, present, StateT.run, mem_support_pure_iff] at reached
          subst output
          exact member
      | some owned =>
          simp only [RegistrationNativePublicFrontend.record, present, StateT.run, support_map] at reached
          obtain ⟨reply, _possible, equal⟩ := reached
          have fixed : output.2 = before.1 := (congrArg Prod.snd equal).symm
          rwa [fixed] at member

theorem accept_run (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (packet : registration.InitPacket) (before : State n KemSK source) :
    (execute setup wire route sign seed scalar
      (RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey
        (.inr (.accept packet)))).run before =
      (RegistrationNativePublicSourceServer.run setup wire route sign seed scalar
        (decide (before.1.parsedAccepts = selectedAccept))
        (RegistrationServerOpenReferenceCompiler.accept setup checks source.verify packet)).run
          ({ before.1 with parsedAccepts := before.1.parsedAccepts + 1 }, before.2) := by
  rfl

/-- Every actual typed command preserves live capabilities' prepared roots, including rejected authentication, all moved handles and arbitrary owner interleavings. -/
theorem query_live (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State n KemSK source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK source)
    (live : Live before.1 before.2) (correct : MemoCorrect setup seed scalar before.2.roots)
    (supported : result ∈ support ((execute setup wire route sign seed scalar
      (RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey query)).run before)) :
    Live result.2.1 result.2.2 ∧ MemoCorrect setup seed scalar result.2.2.roots := by
  cases query with
  | inl coin => exact RegistrationNativePublicSourceExecution.lifted_live setup wire route sign seed scalar _ before result live correct supported
  | inr command => cases command with
    | create edPin mlPin keyId => exact RegistrationNativePublicSourceExecution.beacon_live setup wire route sign seed scalar _ before result live correct supported
    | bundle owner => exact RegistrationNativePublicSourceExecution.beacon_live setup wire route sign seed scalar _ before result live correct supported
    | accept packet =>
        rw [accept_run] at supported
        exact RegistrationNativePublicSourceLive.accept_live setup wire checks route sign source.verify seed scalar
          (decide (before.1.parsedAccepts = selectedAccept)) packet
          ({ before.1 with parsedAccepts := before.1.parsedAccepts + 1 }, before.2) result live correct supported
    | build handle application => exact RegistrationNativePublicSourceBuildLive.build_live setup wire checks route sign seed scalar handle application before result live correct supported
    | finish owner packet => exact RegistrationNativePublicSourceExecution.beacon_live setup wire route sign seed scalar _ before result live correct supported
    | hmac key bytes =>
        change result ∈ support (pure (setup.hmac.eval key bytes, before)) at supported
        rw [mem_support_pure_iff] at supported
        subst result
        exact ⟨live, correct⟩
    | hash bytes => exact RegistrationNativePublicSourceExecution.lifted_live setup wire route sign seed scalar _ before result live correct supported
    | serverSend keyId plaintext => exact record_live setup wire route sign seed scalar (.inl (.inl (plaintext, keyId))) before result live correct supported
    | serverRaw raw => exact record_live setup wire route sign seed scalar (.inl (.inr raw)) before result live correct supported
    | beaconSend owner plaintext => exact record_live setup wire route sign seed scalar (.inr (owner, .inl plaintext)) before result live correct supported
    | beaconRaw owner raw => exact record_live setup wire route sign seed scalar (.inr (owner, .inr raw)) before result live correct supported

private theorem execute_program {Index : Type} {spec : OracleSpec Index}
    (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (handler : QueryImpl spec (RegistrationNativePublicFrontend.M n KemSK source))
    (work : OracleComp spec Value) (before : State n KemSK source) :
    (execute setup wire route sign seed scalar (simulateQ handler work)).run before =
      (simulateQ (fun query => execute setup wire route sign seed scalar (handler query)) work).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure output => rfl
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, RegistrationNativePublicSourceExecution.execute_bind,
        simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      apply bind_congr
      rintro ⟨reply, current⟩
      exact ih reply current

/-- Complete adaptive typed execution preserves the internal native live-root invariant; this includes the full original hidden-bit/fresh controller after compilation. -/
theorem program_live (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (before : State n KemSK source) (result : Value × State n KemSK source)
    (live : Live before.1 before.2) (correct : MemoCorrect setup seed scalar before.2.roots)
    (supported : result ∈ support ((execute setup wire route sign seed scalar
      (simulateQ (RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey) work)).run before)) :
    Live result.2.1 result.2.2 ∧ MemoCorrect setup seed scalar result.2.2.roots := by
  rw [execute_program] at supported
  induction work using OracleComp.inductionOn generalizing before result with
  | pure output =>
      rw [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact ⟨live, correct⟩
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨step, reached, tail⟩ := supported
      obtain ⟨firstLive, firstCorrect⟩ := query_live setup checks wire route sign seed scalar selectedOwner selectedAccept publicPrekey query before step live correct reached
      exact ih step.1 step.2 result firstLive firstCorrect tail

end BeaconcryptCore.Computational.RegistrationNativePublicSourceInvariant
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceInvariant.query_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceInvariant.query_live
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceInvariant.program_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceInvariant.program_live

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceInvariant.accept_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceInvariant.accept_run
