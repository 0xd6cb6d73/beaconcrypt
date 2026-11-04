-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableCreation
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableOrdinary
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServerOwners
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBundleOwnership

/-! The actual corrected adaptive handler restores through the real-count private ML table, with its shared external platform state retained. Ownership and valid signing are derived from reached creation and source-controller states, including failed publication and installation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableHandler
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (Pool handleSource restore Live)
open RegistrationNativeMldsaMap (nativeState)
open RegistrationNativeMldsaPoolMap (StateLive CredentialLive)
open RegistrationNativeMldsaLiveOwners (NonCreate)
open RegistrationNativePlatformMldsaTableProgram (runState)
open RegistrationNativePlatformMldsaTableRestore (observe)
variable {n : Nat} {KemSK Platform E Value ι : Type} {base : OracleSpec ι}
variable (source : Source) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : Credential (handleSource source))
variable [primitive : AdapterSealPrimitive.Operations]
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "callback" => RegistrationNativePlatformMldsaProfile.handler (n := n) setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer

omit primitive in
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) : (f <$> work) before = Prod.map f id <$> work before := bind_pure_comp _ _

omit primitive in
private theorem lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (before : S) : (StateT.lift work) before = (fun value => (value, before)) <$> work := bind_pure_comp _ _

/-- The actual non-generation callbacks contain only ordinary randomness or a signing request on a reached live owned credential. -/
theorem valid (pool : Pool source) (server : CredentialLive source pool credential)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (allowed : NonCreate query)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) (previous : Platform)
    (owners : StateLive source pool before) :
    (((callback query).run before).run previous).AllQueriesSatisfy (RegistrationNativeMldsaTableSign.Valid source pool) := by
  have ordinary (work : StateT (RegistrationNativeExperiment.State n KemSK (handleSource source)) (StateT Platform ProbComp)
      (RegistrationNativeRawAdapter.TypedSpec.Range query)) :
      (((RegistrationNativePlatformMldsaProgram.lift work).run before).run previous).AllQueriesSatisfy
        (RegistrationNativeMldsaTableSign.Valid source pool) :=
    RegistrationNativePlatformQuerySafety.lift_safe _ (fun _ => trivial) work before previous
  cases query with
  | inl coin => exact ordinary _
  | inr query => cases query with
    | create _ _ _ => exact allowed.elim
    | bundle index => exact RegistrationNativePlatformMldsaControllerValid.Bundle.sourceBundle source pool setup checks representation created writer index before previous owners
    | build handle application =>
      simp only [RegistrationNativePlatformMldsaProfile.handler, RegistrationNativePlatformExperiment.server,
        StateT.run, bind_pure_comp, map_apply, Functor.map_map]
      rw [map_eq_pure_bind]
      exact allQueriesSatisfy_bind
        (RegistrationNativePlatformMldsaControllerValid.Server.build source pool credential server setup
          (RegistrationNativeWire.ledgerCodec wire) view failure allocation erased reservePeer helper writer handle application before.server previous)
        (fun _ => allQueriesSatisfy_pure _ _)
    | _ => exact ordinary _

/-- Every non-generation callback keeps exactly the reached private key rows, including failed source writer and signer outcomes. -/
theorem keys (pool : Pool source) (server : CredentialLive source pool credential)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (allowed : NonCreate query)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) (previous : Platform)
    (owners : StateLive source pool before)
    (result : ((RegistrationNativeRawAdapter.TypedSpec.Range query × RegistrationNativeExperiment.State n KemSK (handleSource source)) × Platform) × Pool source)
    (supported : result ∈ support (runState source (callback query) before previous pool)) : result.2.keys = pool.keys :=
  RegistrationNativeMldsaTableRestore.program_keys source pool _
    (valid source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer pool server query allowed before previous owners)
    result supported

/-- The complete actual table-backed callback restores the literal corrected source callback and its real platform poststate. -/
theorem restored (fallback : Credential source) (pool : Pool source) (server : Live source pool credential fallback)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) (previous : Platform)
    (owners : StateLive source pool before) :
    observe source fallback <$> runState source (callback query) before previous pool =
      (((RegistrationNativePlatformExperiment.handler RegistrationNativePlatformMldsaProgram.coins setup checks wire route representation created source fallback
        view failure allocation reserveRegistration reservePeer erased helper writer query).run
          (nativeState (restore source fallback pool) before)).run previous) := by
  have ordinary (allowed : RegistrationNativeMldsaGlobalMap.NonML query) :
      observe source fallback <$> runState source (callback query) before previous pool =
      (((RegistrationNativePlatformExperiment.handler RegistrationNativePlatformMldsaProgram.coins setup checks wire route representation created source fallback
        view failure allocation reserveRegistration reservePeer erased helper writer query).run
          (nativeState (restore source fallback pool) before)).run previous) := by
    have same := RegistrationNativePlatformMldsaTableOrdinary.restored source setup checks wire route representation created credential
      view failure allocation reserveRegistration reservePeer erased helper writer fallback pool query allowed before previous
    rw [RegistrationNativeMldsaOpaque.restore_live source fallback pool credential fallback server] at same
    cases query with
    | inl coin => exact same
    | inr query => cases query <;> first | exact allowed.elim | exact same
  cases query with
  | inl coin => exact ordinary trivial
  | inr query => cases query with
    | create edPin mlPin keyId =>
      have same := RegistrationNativePlatformMldsaTableCreation.restored source setup checks representation created edPin mlPin keyId fallback pool before previous owners
      simp only [RegistrationNativePlatformMldsaProfile.handler, RegistrationNativePlatformExperiment.handler,
        RegistrationNativePlatformExperiment.liftNative, StateT.run, RegistrationNativePlatformMldsaProgram.lift_coins,
        lift_apply, RegistrationNativeExperiment.handler]
      exact same
    | bundle index => exact RegistrationNativePlatformMldsaTableRestore.bundle source fallback pool setup checks representation created writer index before previous owners
    | build handle application =>
      have same := RegistrationNativePlatformMldsaTableRestore.build source fallback pool credential ⟨fallback, server⟩ setup
        (RegistrationNativeWire.ledgerCodec wire) view failure allocation erased reservePeer helper writer handle application before previous
      rw [RegistrationNativeMldsaOpaque.restore_live source fallback pool credential fallback server] at same
      let convertResult := fun result : RustM (Option (U64 × alloc.vec.Vec U8)) =>
        (do let optional ← result; .ok (optional.map fun value : U64 × alloc.vec.Vec U8 => (value.1, TranscriptAuthParts.absSlice value.2)))
      have mapped := congrArg (fun action => Prod.map (Prod.map convertResult id) id <$> action) same
      simp only [RegistrationNativePlatformMldsaProfile.handler, RegistrationNativePlatformExperiment.handler,
        runState, StateT.run, bind_pure_comp, map_apply,
        RegistrationNativeMldsaTableProgram.evaluate, simulateQ_map, Functor.map_map, observe] at mapped ⊢
      exact mapped
    | _ => exact ordinary trivial

/-- The actual owned Server key remains the same private row across every complete callback, including owner birth. -/
theorem server_live (fallback : Credential source) (pool : Pool source) (server : Live source pool credential fallback)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) (previous : Platform)
    (owners : StateLive source pool before)
    (result : ((RegistrationNativeRawAdapter.TypedSpec.Range query × RegistrationNativeExperiment.State n KemSK (handleSource source)) × Platform) × Pool source)
    (supported : result ∈ support (runState source (callback query) before previous pool)) :
    Live source result.2 credential fallback := by
  have ordinary (allowed : NonCreate query) : Live source result.2 credential fallback := by
    have rows := keys source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer
      pool ⟨fallback, server⟩ query allowed before previous owners result supported
    exact ⟨by rw [rows]; exact server.1, server.2⟩
  cases query with
  | inl coin => exact ordinary trivial
  | inr query => cases query with
    | create edPin mlPin keyId =>
      exact RegistrationNativePlatformMldsaTableCreation.key_live source setup checks representation created edPin mlPin keyId pool before previous
        credential fallback server result supported
    | _ => exact ordinary trivial


omit primitive in
private theorem keys_live (initial final : Pool source) (same : final.keys = initial.keys)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) (live : StateLive source initial before) :
    StateLive source final before := by
  intro owner member
  obtain ⟨key, row, publicKey⟩ := live owner member
  exact ⟨key, by rw [same]; exact row, publicKey⟩

/-- Every actual complete source callback preserves all reached live owner handles at its actual final private table. -/
theorem live (pool : Pool source) (server : CredentialLive source pool credential)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) (previous : Platform)
    (owners : StateLive source pool before)
    (result : ((RegistrationNativeRawAdapter.TypedSpec.Range query × RegistrationNativeExperiment.State n KemSK (handleSource source)) × Platform) × Pool source)
    (supported : result ∈ support (runState source (callback query) before previous pool)) :
    StateLive source result.2 result.1.1.2 := by
  have ordinary (allowed : RegistrationNativeMldsaGlobalMap.NonML query) : StateLive source result.2 result.1.1.2 := by
    apply RegistrationNativePlatformMldsaTableOrdinary.live source setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper writer pool query allowed before previous owners result
    cases query with
    | inl coin => exact supported
    | inr query => cases query <;> first | exact allowed.elim | exact supported
  have retained (allowed : NonCreate query) := keys source setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer erased helper writer pool server query allowed before previous owners result supported
  have possible := RegistrationNativeMldsaTableCallbacks.evaluate_support source (((callback query).run before).run previous) pool result supported
  cases query with
  | inl coin => exact ordinary trivial
  | inr query => cases query with
    | create edPin mlPin keyId =>
      exact RegistrationNativePlatformMldsaTableCreation.live source setup checks representation created
        edPin mlPin keyId pool before previous owners result supported
    | bundle index =>
      exact keys_live source pool result.2 (retained trivial) result.1.1.2
        (RegistrationNativePlatformMldsaBundleOwnership.sourceBundle_live source pool setup checks representation created writer index
          before result.1.1.2 previous result.1.2 result.1.1.1 owners possible)
    | build handle application =>
      have same := RegistrationNativePlatformMldsaServerOwners.build setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer erased helper writer handle application before result.1.1.2 previous result.1.2 result.1.1.1 possible
      exact keys_live source pool result.2 (retained trivial) result.1.1.2
        (RegistrationNativePlatformMldsaServerOwners.owners_live source pool before result.1.1.2 owners same.1)
    | _ => exact ordinary trivial

end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableHandler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableHandler.valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableHandler.valid

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableHandler.keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableHandler.keys

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableHandler.restored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableHandler.restored

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableHandler.server_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableHandler.server_live

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableHandler.live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableHandler.live
