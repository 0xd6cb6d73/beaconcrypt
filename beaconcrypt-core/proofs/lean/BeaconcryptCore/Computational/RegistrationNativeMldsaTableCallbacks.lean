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
open RegistrationNativeMldsaPoolMap (CredentialLive)
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
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (credential : Credential (handleSource source)) (pool : Pool source)
local notation "callback" => RegistrationNativeMldsaProfile.handler setup checks wire route representation created credential

/-- Every reached non-creation callback issues only ordinary queries or a live named signing request. -/
theorem valid (credentialLive : CredentialLive source pool credential)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (allowed : NonCreate query)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) :
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
          setup checks representation created wire index before
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
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) :
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
          setup checks wire representation created index before
    | build handle application =>
        simp only [RegistrationNativeMldsaProfile.handler, RegistrationNativeExperiment.handler]
        exact RegistrationNativeMldsaTableRestore.build source fallback pool
          setup checks wire credential credentialLive handle application before
    | _ => exact ordinary source setup checks wire route representation created credential pool fallback _ (by trivial) before

/-- Non-creation callbacks retain every exact private key row, independently of optional signing replies. -/
theorem keys (credentialLive : CredentialLive source pool credential)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (allowed : NonCreate query)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source))
    (result : (RegistrationNativeRawAdapter.TypedSpec.Range query × RegistrationNativeExperiment.State n KemSK (handleSource source)) × Pool source)
    (supported : result ∈ support (runState source (callback query) before pool)) : result.2.keys = pool.keys :=
  RegistrationNativeMldsaTableRestore.program_keys source pool _
    (valid source setup checks wire route representation created credential pool credentialLive query allowed before) result supported

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
