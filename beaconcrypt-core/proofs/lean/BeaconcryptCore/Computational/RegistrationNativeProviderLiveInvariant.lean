-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeProviderBuildLive
import BeaconcryptCore.Computational.RegistrationNativeProviderLive

/-! Every actual adaptive typed frontend execution preserves its internal live-root and source-memo invariants. The unchanged original full secrecy compiler is one such typed client, so no public win or eligibility predicate requires an external root-preparation premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProviderLiveInvariant
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeProviderInterpreter (Provider)
open RegistrationNativeProviderSource (FrontState)
abbrev State (n : Nat) (KemSK ProviderState : Type) (source : RegistrationNativeMldsa.Source) :=
  FrontState n KemSK ProviderState source
open RegistrationNativePublicSourceState (Live MemoCorrect)
open RegistrationNativeProviderSource (execute)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationServerOpenReferenceCompiler.accept RegistrationAuthenticationCompiler.program

private theorem record_live (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState)
    (query : PqxdhRecordLiftInterface.RecordQuery) (before : State n KemSK ProviderState source)
    (result : (PqxdhRecordLiftInterface.RecordSpec .O).Range query × State n KemSK ProviderState source)
    (live : Live before.1 before.2.1) (correct : MemoCorrect setup seed scalar before.2.1.roots)
    (supported : result ∈ support ((execute setup wire route sign seed scalar provider
      (RegistrationNativePublicFrontend.record query)).run before)) :
    Live result.2.1 result.2.2.1 ∧ MemoCorrect setup seed scalar result.2.2.1.roots := by
  apply RegistrationNativeProviderExecution.live_of_subset setup wire route sign seed scalar provider _ before result _ live correct supported
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

private theorem execute_get (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (before : State n KemSK ProviderState source) :
    (execute setup wire route sign seed scalar provider get).run before = pure (before.1, before) := by
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (pure ((before.1, before.1), before.2) : ProbComp _) = _
  rw [map_pure]

private theorem execute_modify (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (update : RegistrationNativePublicFrontend.State source → RegistrationNativePublicFrontend.State source)
    (before : State n KemSK ProviderState source) :
    (execute setup wire route sign seed scalar provider (modify update)).run before =
      pure ((), (update before.1, before.2)) := by
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (pure (((), update before.1), before.2) : ProbComp _) = _
  rw [map_pure]

theorem accept_run (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (packet : registration.InitPacket) (before : State n KemSK ProviderState source) :
    (execute setup wire route sign seed scalar provider
      (RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey
        (.inr (.accept packet)))).run before =
      (execute setup wire route sign seed scalar provider
      (RegistrationNativePublicFrontend.serverOpen (decide (before.1.parsedAccepts = selectedAccept))
        (RegistrationServerOpenReferenceCompiler.accept setup checks source.verify packet))).run
          ({ before.1 with parsedAccepts := before.1.parsedAccepts + 1 }, before.2) := by
  rw [RegistrationNativePublicFrontend.handler, RegistrationNativeProviderExecution.execute_bind,
    execute_get, pure_bind, RegistrationNativeProviderExecution.execute_bind, execute_modify, pure_bind]

/-- Every actual typed command preserves live capabilities' prepared roots, including rejected authentication, all moved handles and arbitrary owner interleavings. -/
theorem query_live (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State n KemSK ProviderState source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK ProviderState source)
    (live : Live before.1 before.2.1) (correct : MemoCorrect setup seed scalar before.2.1.roots)
    (supported : result ∈ support ((execute setup wire route sign seed scalar provider
      (RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey query)).run before)) :
    Live result.2.1 result.2.2.1 ∧ MemoCorrect setup seed scalar result.2.2.1.roots := by
  cases query with
  | inl coin => exact RegistrationNativeProviderExecution.lifted_live setup wire route sign seed scalar provider _ before result live correct supported
  | inr command => cases command with
    | create edPin mlPin keyId => exact RegistrationNativeProviderExecution.beacon_live setup wire route sign seed scalar provider _ before result live correct supported
    | bundle owner => exact RegistrationNativeProviderExecution.beacon_live setup wire route sign seed scalar provider _ before result live correct supported
    | accept packet =>
        rw [accept_run] at supported
        exact RegistrationNativeProviderLive.accept_live setup wire checks route sign source.verify seed scalar provider
          (decide (before.1.parsedAccepts = selectedAccept)) packet
          ({ before.1 with parsedAccepts := before.1.parsedAccepts + 1 }, before.2) result live correct supported
    | build handle application => exact RegistrationNativeProviderBuildLive.build_live setup checks wire route sign seed scalar provider handle application before result live correct supported
    | finish owner packet => exact RegistrationNativeProviderExecution.beacon_live setup wire route sign seed scalar provider _ before result live correct supported
    | hmac key bytes =>
        change result ∈ support (pure (setup.hmac.eval key bytes, before)) at supported
        rw [mem_support_pure_iff] at supported
        subst result
        exact ⟨live, correct⟩
    | hash bytes => exact RegistrationNativeProviderExecution.lifted_live setup wire route sign seed scalar provider _ before result live correct supported
    | serverSend keyId plaintext => exact record_live setup wire route sign seed scalar provider (.inl (.inl (plaintext, keyId))) before result live correct supported
    | serverRaw raw => exact record_live setup wire route sign seed scalar provider (.inl (.inr raw)) before result live correct supported
    | beaconSend owner plaintext => exact record_live setup wire route sign seed scalar provider (.inr (owner, .inl plaintext)) before result live correct supported
    | beaconRaw owner raw => exact record_live setup wire route sign seed scalar provider (.inr (owner, .inr raw)) before result live correct supported

private theorem execute_program {Index : Type} {spec : OracleSpec Index}
    (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState)
    (handler : QueryImpl spec (RegistrationNativePublicFrontend.M n KemSK source))
    (work : OracleComp spec Value) (before : State n KemSK ProviderState source) :
    (execute setup wire route sign seed scalar provider (simulateQ handler work)).run before =
      (simulateQ (fun query => execute setup wire route sign seed scalar provider (handler query)) work).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure output => rfl
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, RegistrationNativeProviderExecution.execute_bind,
        simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      apply bind_congr
      rintro ⟨reply, current⟩
      exact ih reply current

/-- Complete adaptive typed execution preserves the internal native live-root invariant; this includes the full original hidden-bit/fresh controller after compilation. -/
theorem program_live (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (before : State n KemSK ProviderState source) (result : Value × State n KemSK ProviderState source)
    (live : Live before.1 before.2.1) (correct : MemoCorrect setup seed scalar before.2.1.roots)
    (supported : result ∈ support ((execute setup wire route sign seed scalar provider
      (simulateQ (RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey) work)).run before)) :
    Live result.2.1 result.2.2.1 ∧ MemoCorrect setup seed scalar result.2.2.1.roots := by
  rw [execute_program] at supported
  induction work using OracleComp.inductionOn generalizing before result with
  | pure output =>
      rw [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact ⟨live, correct⟩
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨step, reached, tail⟩ := supported
      obtain ⟨firstLive, firstCorrect⟩ := query_live setup checks wire route sign seed scalar provider selectedOwner selectedAccept publicPrekey query before step live correct reached
      exact ih step.1 step.2 result firstLive firstCorrect tail

end BeaconcryptCore.Computational.RegistrationNativeProviderLiveInvariant
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderLiveInvariant.accept_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderLiveInvariant.accept_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderLiveInvariant.query_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderLiveInvariant.query_live
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderLiveInvariant.program_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderLiveInvariant.program_live
