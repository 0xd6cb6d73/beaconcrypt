-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaTableRestore
import BeaconcryptCore.Computational.RegistrationNativeMldsaGlobalMap

/-! Every actual non-creation native callback restores through its reached private key table. The live-owner invariant is proved on the free bundle program and the original ordinary source continuations, without evaluating the opaque source's dummy signer or inferring ownership through a noninjective representation map. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaTableCallbacks
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (Pool handleSource restore)
open RegistrationNativeMldsaMap (nativeState)
open RegistrationNativeMldsaPoolMap (CredentialLive StateLive)
open RegistrationNativeMldsaTableProgram (evaluate runState)
open RegistrationNativeMldsaTableRestore (observe)
open RegistrationNativeMldsaLiveOwners (NonCreate)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable (source : Source)
attribute [local irreducible] RegistrationNativeExperiment.handler

/-- A supported result of a private table interpretation is supported by its free program, for arbitrary primitive replies and private counts. -/
theorem evaluate_support (work : OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source)) Value)
    (before : Pool source) (result : Value × Pool source) (supported : result ∈ support (evaluate source work before)) :
    result.1 ∈ support work := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [evaluate, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      simp only [support_pure, Set.mem_singleton_iff]
  | query_bind query next ih =>
      simp only [evaluate, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, _reached, continued⟩ := supported
      rw [mem_support_bind_iff]
      exact ⟨middle.1, mem_support_query query middle.1, ih middle.1 middle.2 continued⟩

private theorem ordinary_all (pool : Pool source) (work : ProbComp Value) :
    (RegistrationNativeMldsaProgram.lift (source := handleSource source) work).AllQueriesSatisfy
      (RegistrationNativeMldsaTableSign.Valid source pool) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind query next ih =>
      simp only [RegistrationNativeMldsaProgram.lift, simulateQ_bind, simulateQ_spec_query,
        RegistrationNativeMldsaProgram.ordinary]
      exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial, ih⟩

private theorem map_all {Query : Type} {queries : OracleSpec Query} {Answer Result : Type}
    (predicate : Query → Prop) (observer : Answer → Result) (work : OracleComp queries Answer)
    (allowed : work.AllQueriesSatisfy predicate) : (observer <$> work).AllQueriesSatisfy predicate := by
  rw [map_eq_pure_bind]
  exact allQueriesSatisfy_bind allowed (fun _ => allQueriesSatisfy_pure _ _)

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit)
variable (credential : Credential (handleSource source)) (pool : Pool source)
local notation "callback" => RegistrationNativeMldsaProfile.handler setup checks wire route representation created credential

/-- Every reached non-creation callback issues only ordinary queries or a live named signing request. -/
theorem valid (credentialLive : CredentialLive source pool credential)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (allowed : NonCreate query)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) (live : StateLive source pool before) :
    ((callback query).run before).AllQueriesSatisfy (RegistrationNativeMldsaTableSign.Valid source pool) := by
  have ordinary (work : StateT (RegistrationNativeExperiment.State n KemSK (handleSource source)) ProbComp
      (RegistrationNativeRawAdapter.TypedSpec.Range query)) :
      ((RegistrationNativeMldsaProgram.liftState work).run before).AllQueriesSatisfy
        (RegistrationNativeMldsaTableSign.Valid source pool) := ordinary_all source pool _
  cases query with
  | inl coin => exact ordinary _
  | inr query => cases query with
    | create _ _ _ => exact allowed.elim
    | bundle index =>
        exact RegistrationNativeMldsaControllerValid.Bundle.sourceBundle source pool
          setup checks representation created wire index before live
    | build handle application =>
        exact map_all _ _ _ (RegistrationNativeMldsaControllerValid.Server.build source pool credential credentialLive
          setup (RegistrationNativeWire.ledgerCodec wire) checks wire.encodeResponse handle application before.server)
    | _ => exact ordinary _

private theorem ordinary (fallback : Credential source) (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (allowed : RegistrationNativeMldsaGlobalMap.NonML query)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) :
    observe source fallback <$> runState source
      (RegistrationNativeMldsaProgram.liftState
        (RegistrationNativeExperiment.handler setup checks wire route representation created (handleSource source) credential query)) before pool =
      (RegistrationNativeExperiment.handler setup checks wire route representation created source
        (RegistrationNativeMldsaMap.credential (restore source fallback pool) credential) query).run
          (nativeState (restore source fallback pool) before) := by
  rw [RegistrationNativeMldsaTableProgram.run_liftState]
  simp only [Functor.map_map, observe]
  exact RegistrationNativeMldsaGlobalMap.non_ml_natural (restore source fallback pool) rfl
    setup checks wire route representation created credential query allowed before

/-- Complete actual non-creation callbacks restore the unchanged native source handler, including every record and authentication failure. -/
theorem restored (fallback : Credential source) (credentialLive : CredentialLive source pool credential)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (allowed : NonCreate query)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) (live : StateLive source pool before) :
    observe source fallback <$> runState source (callback query) before pool =
      (RegistrationNativeExperiment.handler setup checks wire route representation created source
        (RegistrationNativeMldsaMap.credential (restore source fallback pool) credential) query).run
          (nativeState (restore source fallback pool) before) := by
  cases query with
  | inl coin => exact ordinary source setup checks wire route representation created credential pool fallback _ (by trivial) before
  | inr query => cases query with
    | create _ _ _ => exact allowed.elim
    | bundle index =>
        simp only [RegistrationNativeMldsaProfile.handler, RegistrationNativeExperiment.handler]
        exact RegistrationNativeMldsaTableRestore.bundle source fallback pool
          setup checks wire representation created index before live
    | build handle application =>
        simp only [RegistrationNativeMldsaProfile.handler, RegistrationNativeExperiment.handler]
        exact RegistrationNativeMldsaTableRestore.build source fallback pool
          setup checks wire credential credentialLive handle application before
    | _ => exact ordinary source setup checks wire route representation created credential pool fallback _ (by trivial) before

/-- Non-creation callbacks retain every exact private key row, independently of optional signing replies. -/
theorem keys (credentialLive : CredentialLive source pool credential)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (allowed : NonCreate query)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) (live : StateLive source pool before)
    (result : (RegistrationNativeRawAdapter.TypedSpec.Range query × RegistrationNativeExperiment.State n KemSK (handleSource source)) × Pool source)
    (supported : result ∈ support (runState source (callback query) before pool)) : result.2.keys = pool.keys :=
  RegistrationNativeMldsaTableRestore.program_keys source pool _
    (valid source setup checks wire route representation created credential pool credentialLive query allowed before live) result supported

private theorem keys_live (initial final : Pool source) (same : final.keys = initial.keys)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) (live : StateLive source initial before) :
    StateLive source final before := by
  intro owner member
  obtain ⟨key, row, publicKey⟩ := live owner member
  exact ⟨key, by rw [same]; exact row, publicKey⟩

private theorem ordinary_live (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (allowed : NonCreate query)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) (live : StateLive source pool before)
    (result : (RegistrationNativeRawAdapter.TypedSpec.Range query × RegistrationNativeExperiment.State n KemSK (handleSource source)) × Pool source)
    (supported : result ∈ support (runState source
      (RegistrationNativeMldsaProgram.liftState
        (RegistrationNativeExperiment.handler setup checks wire route representation created (handleSource source) credential query)) before pool)) :
    StateLive source result.2 result.1.2 := by
  rw [RegistrationNativeMldsaTableProgram.run_liftState, support_map] at supported
  obtain ⟨answer, reached, same⟩ := supported
  cases same
  exact RegistrationNativeMldsaLiveOwners.handler source setup checks wire route representation created
    credential pool query allowed before answer live reached

/-- Every actual non-creation callback preserves reached owned handles at its final private table. -/
theorem live (credentialLive : CredentialLive source pool credential)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (allowed : NonCreate query)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) (old : StateLive source pool before)
    (result : (RegistrationNativeRawAdapter.TypedSpec.Range query × RegistrationNativeExperiment.State n KemSK (handleSource source)) × Pool source)
    (supported : result ∈ support (runState source (callback query) before pool)) :
    StateLive source result.2 result.1.2 := by
  have rows := keys source setup checks wire route representation created credential pool credentialLive query allowed before old result supported
  have possible := evaluate_support source ((callback query).run before) pool result supported
  cases query with
  | inl coin => exact ordinary_live source setup checks wire route representation created credential pool (.inl coin) trivial before old result supported
  | inr query => cases query with
    | create _ _ _ => exact allowed.elim
    | bundle index =>
        exact keys_live source pool result.2 rows result.1.2
          (RegistrationNativeMldsaBundleOwnership.sourceBundle_live source pool setup checks wire representation created
            index before result.1 old possible)
    | build handle application =>
        simp only [RegistrationNativeMldsaProfile.handler, RegistrationNativeMldsaProfile.server, StateT.run, support_map] at possible
        obtain ⟨answer, _reached, same⟩ := possible
        have retained : before.beacons = result.1.2.beacons := congrArg (fun pair => pair.2.beacons) same
        apply keys_live source pool result.2 rows result.1.2
        change RegistrationNativeMldsaPoolMap.OwnersLive source pool result.1.2.beacons
        rw [← retained]
        exact old
    | accept packet =>
        simp only [RegistrationNativeMldsaProfile.handler] at supported
        exact ordinary_live source setup checks wire route representation created credential pool (.inr (.accept packet)) trivial before old result supported
    | finish index packet =>
        simp only [RegistrationNativeMldsaProfile.handler] at supported
        exact ordinary_live source setup checks wire route representation created credential pool (.inr (.finish index packet)) trivial before old result supported
    | hmac key message =>
        simp only [RegistrationNativeMldsaProfile.handler] at supported
        exact ordinary_live source setup checks wire route representation created credential pool (.inr (.hmac key message)) trivial before old result supported
    | hash bytes =>
        simp only [RegistrationNativeMldsaProfile.handler] at supported
        exact ordinary_live source setup checks wire route representation created credential pool (.inr (.hash bytes)) trivial before old result supported
    | serverSend keyId plaintext =>
        simp only [RegistrationNativeMldsaProfile.handler] at supported
        exact ordinary_live source setup checks wire route representation created credential pool (.inr (.serverSend keyId plaintext)) trivial before old result supported
    | serverRaw raw =>
        simp only [RegistrationNativeMldsaProfile.handler] at supported
        exact ordinary_live source setup checks wire route representation created credential pool (.inr (.serverRaw raw)) trivial before old result supported
    | beaconSend index plaintext =>
        simp only [RegistrationNativeMldsaProfile.handler] at supported
        exact ordinary_live source setup checks wire route representation created credential pool (.inr (.beaconSend index plaintext)) trivial before old result supported
    | beaconRaw index raw =>
        simp only [RegistrationNativeMldsaProfile.handler] at supported
        exact ordinary_live source setup checks wire route representation created credential pool (.inr (.beaconRaw index raw)) trivial before old result supported
end BeaconcryptCore.Computational.RegistrationNativeMldsaTableCallbacks

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTableCallbacks.evaluate_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTableCallbacks.evaluate_support

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTableCallbacks.valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTableCallbacks.valid

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTableCallbacks.restored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTableCallbacks.restored

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTableCallbacks.keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTableCallbacks.keys

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTableCallbacks.live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTableCallbacks.live
