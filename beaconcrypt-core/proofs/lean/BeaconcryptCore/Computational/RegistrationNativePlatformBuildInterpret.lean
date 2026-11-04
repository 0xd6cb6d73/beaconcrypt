-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformInterpret
import Cslib.Foundations.Control.Monad.IsMonadHom

/-! The complete additive stateful Server build commutes with a single common interpreter. Allocator and writer requests, ordinary random draws, signing history, record work and every failed continuation retain their complete shared poststate. This is model interpretation algebra; source codecs, containers and the deployed repeated pin fingerprint remain separate boundaries. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformBuildInterpret
open RegistrationNativePlatformInterpret (state state_pure state_bind state_simulate)
variable {κ State Value : Type} {spec : OracleSpec.{0, 0} κ}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem state_hom (implementation : QueryImpl spec m) :
    Cslib.IsMonadHom (StateT State (OracleComp spec)) (StateT State m) (state implementation) :=
  .mk' (state_pure implementation) (state_bind implementation)

section Hom
variable {left right : Type → Type} [Monad left] [Monad right]
variable {F : ∀ {Value : Type}, left Value → right Value}
variable (hom : Cslib.IsMonadHom left right F)
include hom
variable {Encoded : Type}

private theorem simulate_hom [LawfulMonad left] [LawfulMonad right] {Query : Type} {queries : OracleSpec Query}
    (handler : QueryImpl queries left) (work : OracleComp queries Value) :
    F (simulateQ handler work) = simulateQ (fun query => F (handler query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => exact hom.map_pure _
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, hom.map_bind, ih]

namespace Publication
open RegistrationNativePlatformServerPublication

private theorem continueWith_hom {Input : Type} (action : RustM Input)
    (next : Input → left (RustM (RegistrationWorldServerPublication.Result Encoded))) :
    F (continueWith action next) = continueWith action (fun value => F (next value)) := by
  cases action <;> first | rfl | exact hom.map_pure _

private theorem continueResult_hom {Input : Type} (action : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → left (RustM (RegistrationWorldServerPublication.Result Encoded))) :
    F (continueResult action next) = continueResult action (fun value => F (next value)) := by
  cases action with
  | fail error | div => exact hom.map_pure _
  | ok result => cases result with
    | Ok value => rfl
    | Err previous => exact hom.map_pure _

theorem ready (encode : registration.SignedResponseView → left (RustM (core.option.Option Encoded)))
    (pending : registration.ServerResponseReady) :
    F (RegistrationNativePlatformServerPublication.ready encode pending) =
      RegistrationNativePlatformServerPublication.ready (fun view => F (encode view)) pending := by
  unfold RegistrationNativePlatformServerPublication.ready
  rw [continueWith_hom hom]
  apply congrArg (continueWith pending.message)
  funext view
  rw [hom.map_bind]
  apply bind_congr
  intro encoded
  exact hom.map_pure _

theorem signing (sign : QueryImpl RegistrationSigningShared.Spec left)
    (encode : registration.SignedResponseView → left (RustM (core.option.Option Encoded)))
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.ServerResponseSigning) :
    F (RegistrationNativePlatformServerPublication.signing sign encode payload digest pending) =
      RegistrationNativePlatformServerPublication.signing (fun query => F (sign query))
        (fun view => F (encode view)) payload digest pending := by
  unfold RegistrationNativePlatformServerPublication.signing
  rw [continueWith_hom hom]
  apply congrArg (continueWith pending.request)
  funext request
  rw [hom.map_bind]
  apply bind_congr
  intro signature
  rw [continueResult_hom hom]
  apply congrArg (continueResult (pending.resume signature))
  funext next
  exact ready hom encode next

theorem program (sign : QueryImpl RegistrationSigningShared.Spec left)
    (encode : registration.SignedResponseView → left (RustM (core.option.Option Encoded)))
    (pending : registration.ServerResponseHash) :
    F (RegistrationNativePlatformServerPublication.program sign encode pending) =
      RegistrationNativePlatformServerPublication.program (fun query => F (sign query))
        (fun view => F (encode view)) pending := by
  unfold RegistrationNativePlatformServerPublication.program
  rw [continueWith_hom hom]
  apply congrArg (continueWith pending.request)
  funext request
  rw [hom.map_bind]
  apply bind_congr
  intro digest
  rw [continueResult_hom hom]
  apply congrArg (continueResult (pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest))))
  funext next
  exact signing hom sign encode _ digest next
end Publication
namespace Completion
open RegistrationNativePlatformServerCompletion
variable {n : Nat}

private theorem continueWith_hom {Input : Type} (action : RustM Input)
    (next : Input → left (RustM (RegistrationWorldServerCompletion.Result Encoded))) :
    F (continueWith action next) = continueWith action (fun value => F (next value)) := by
  cases action <;> first | rfl | exact hom.map_pure _

private theorem continueResult_hom {Input : Type} (action : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → left (RustM (RegistrationWorldServerCompletion.Result Encoded))) :
    F (continueResult action next) = continueResult action (fun value => F (next value)) := by
  cases action with
  | fail error | div => exact hom.map_pure _
  | ok result => cases result with
    | Ok value => rfl
    | Err previous => exact hom.map_pure _

theorem installWith (capability : QueryImpl (PqxdhRecordLiftInterface.CapabilitySpec n) left)
    (control : pqxdh.ServerState) (published : registration.PublishedServerResponse Encoded) :
    F (RegistrationNativePlatformServerCompletion.installWith capability control published) =
      RegistrationNativePlatformServerCompletion.installWith (fun query => F (capability query)) control published := by
  unfold RegistrationNativePlatformServerCompletion.installWith
  rw [continueResult_hom hom]
  apply congrArg (continueResult (peer.begin_peer_insert control published))
  funext pending
  rw [continueWith_hom hom]
  apply congrArg (continueWith pending.request)
  funext keyId
  rw [continueWith_hom hom]
  apply congrArg (continueWith pending.into_parts)
  funext parts
  rw [hom.map_bind]
  apply bind_congr
  intro inserted
  exact hom.map_pure _

theorem fromInitialWith [LawfulMonad left] [LawfulMonad right]
    (record : QueryImpl RegistrationRecordPrimitives.Spec left)
    (sign : QueryImpl RegistrationSigningShared.Spec left)
    (capability : QueryImpl (PqxdhRecordLiftInterface.CapabilitySpec n) left)
    (encode : registration.SignedResponseView → left (RustM (core.option.Option Encoded)))
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    F (RegistrationNativePlatformServerCompletion.fromInitialWith record sign capability encode control pending) =
      RegistrationNativePlatformServerCompletion.fromInitialWith (fun query => F (record query))
        (fun query => F (sign query)) (fun query => F (capability query))
        (fun view => F (encode view)) control pending := by
  unfold RegistrationNativePlatformServerCompletion.fromInitialWith
  rw [hom.map_bind, simulate_hom hom]
  apply bind_congr
  intro recorded
  rw [continueResult_hom hom]
  apply congrArg (continueResult recorded)
  funext response
  rw [hom.map_bind, Publication.program hom]
  apply bind_congr
  intro published
  rw [continueResult_hom hom]
  apply congrArg (continueResult published)
  funext ready
  exact installWith hom capability control ready
end Completion
end Hom
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {Auxiliary Encoded ι KemSK Reader Response : Type} {base : OracleSpec ι}

theorem local_native (implementation : QueryImpl spec m) (coins : QueryImpl unifSpec (OracleComp spec))
    (work : StateT (RegistrationWorldAgreement.State n Auxiliary) ProbComp Value) :
    state implementation (RegistrationNativePlatformServerCompletion.liftNative coins work) =
      RegistrationNativePlatformServerCompletion.liftNative (fun query => simulateQ implementation (coins query)) work := by
  funext before
  exact (QueryImpl.simulateQ_compose implementation coins (work.run before)).symm

/-- The actual first record, signing and effectful response writer commute jointly with the complete Local/native state. -/
theorem fromInitial (implementation : QueryImpl spec m) (coins : QueryImpl unifSpec (OracleComp spec))
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → StateT (RegistrationWorldAgreement.State n Auxiliary) (OracleComp spec)
      (RustM (core.option.Option Encoded)))
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    state implementation (RegistrationNativePlatformServerCompletion.fromInitial coins setup codec sign encode control pending) =
      RegistrationNativePlatformServerCompletion.fromInitial (fun query => simulateQ implementation (coins query))
        setup codec sign (fun view => state implementation (encode view)) control pending := by
  unfold RegistrationNativePlatformServerCompletion.fromInitial
  rw [Completion.fromInitialWith (state_hom implementation)]
  simp only [RegistrationNativePlatformServerCompletion.records, RegistrationNativePlatformServerCompletion.outgoing,
    RegistrationNativePlatformServerCompletion.capability, local_native]
  rfl

private theorem world (implementation : QueryImpl spec m)
    (work : StateT (RegistrationServerRootCompiler.Local n) (OracleComp spec) Value) :
    state implementation (RegistrationNativePlatformServerSdk.world work) =
      RegistrationNativePlatformServerSdk.world (state implementation work) := by
  funext before
  simp only [state, RegistrationNativePlatformServerSdk.world, StateT.run, simulateQ_map]

omit [LawfulMonad m] in
private theorem commit (implementation : QueryImpl spec m)
    (result : RustM (RegistrationWorldServerCompletion.Result Encoded)) :
    state implementation (RegistrationNativePlatformServerSdk.commit (n := n) result) =
      RegistrationNativePlatformServerSdk.commit result := by
  funext before
  cases result with
  | fail error | div => rfl
  | ok result => cases result <;> rfl

/-- Publication and native commitment retain the complete Server envelope under a common stateful platform interpreter. -/
theorem sdk_fromInitial (implementation : QueryImpl spec m) (coins : QueryImpl unifSpec (OracleComp spec))
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → StateT (RegistrationServerRootCompiler.Local n) (OracleComp spec)
      (RustM (core.option.Option Encoded)))
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    state implementation (RegistrationNativePlatformServerSdk.fromInitial coins setup codec sign encode control pending) =
      RegistrationNativePlatformServerSdk.fromInitial (fun query => simulateQ implementation (coins query))
        setup codec sign (fun view => state implementation (encode view)) control pending := by
  unfold RegistrationNativePlatformServerSdk.fromInitial
  rw [state_bind, world, fromInitial]
  apply bind_congr
  intro published
  exact commit implementation published

/-- Peer reservation runs at the original post-occupancy stage and forwards its exact poststate to first-record construction. -/
theorem afterOccupancy (implementation : QueryImpl spec m) (coins : QueryImpl unifSpec (OracleComp spec))
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (OracleComp spec) Bool)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → StateT (RegistrationServerRootCompiler.Local n) (OracleComp spec)
      (RustM (core.option.Option Encoded)))
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (occupied : Bool) :
    state implementation (RegistrationNativePlatformServerSdk.afterOccupancy coins setup codec reserve sign encode control lookup occupied) =
      RegistrationNativePlatformServerSdk.afterOccupancy (fun query => simulateQ implementation (coins query))
        setup codec (state implementation reserve) sign (fun view => state implementation (encode view)) control lookup occupied := by
  unfold RegistrationNativePlatformServerSdk.afterOccupancy
  cases resumed : lookup.resume occupied with
  | fail error | div => exact state_pure implementation _
  | ok result => cases result with
    | Err previous => exact state_pure implementation _
    | Ok pending =>
      rw [state_bind]
      apply bind_congr
      intro admitted
      cases admitted with
      | false => exact state_pure implementation _
      | true => exact sdk_fromInitial implementation coins setup codec sign encode control pending

/-- Complete-message preflight, occupancy, reservation and all later record/publication effects preserve their exact shared interpreter state. -/
theorem complete (implementation : QueryImpl spec m) (coins : QueryImpl unifSpec (OracleComp spec))
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (OracleComp spec) Bool)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → StateT (RegistrationServerRootCompiler.Local n) (OracleComp spec)
      (RustM (core.option.Option Encoded)))
    (token : peer.ConsumedRegistration) (application : Slice U8) :
    state implementation (RegistrationNativePlatformServerSdk.complete coins setup codec reserve sign encode token application) =
      RegistrationNativePlatformServerSdk.complete (fun query => simulateQ implementation (coins query))
        setup codec (state implementation reserve) sign (fun view => state implementation (encode view)) token application := by
  funext before
  unfold state RegistrationNativePlatformServerSdk.complete StateT.run
  cases looked : peer.begin_completion_lookup before.control before.pin token application with
  | fail error | div => rfl
  | ok result => cases result with
    | Err previous => rfl
    | Ok lookup =>
      dsimp only
      cases requested : lookup.request with
      | fail error | div => rfl
      | ok keyId =>
        dsimp only
        cases preflight : RegistrationServerSdkSource.preflight application keyId with
        | false => rfl
        | true =>
          simp only [ite_true]
          rw [simulateQ_bind]
          have occupancy : state implementation
              (RegistrationNativePlatformServerSdk.world
                (RegistrationNativePlatformServerCompletion.capability coins (.peerPresent keyId)) :
                StateT (RegistrationServerFrontendCompiler.State n) (OracleComp spec) Bool) =
              RegistrationNativePlatformServerSdk.world
                (RegistrationNativePlatformServerCompletion.capability
                  (fun query => simulateQ implementation (coins query)) (.peerPresent keyId)) := by
            rw [world]
            exact congrArg RegistrationNativePlatformServerSdk.world (local_native implementation coins _)
          have first := congrArg (fun work : StateT (RegistrationServerFrontendCompiler.State n) m Bool => work.run before) occupancy
          rw [show simulateQ implementation
              ((RegistrationNativePlatformServerSdk.world
                (RegistrationNativePlatformServerCompletion.capability coins (.peerPresent keyId))).run before) = _ from first]
          apply bind_congr
          rintro ⟨occupied, current⟩
          exact congrArg (fun work : StateT (RegistrationServerFrontendCompiler.State n) m _ => work.run current)
            (afterOccupancy implementation coins setup codec reserve sign encode before.control lookup occupied)

/-- The full stateful Server build, including moved-token consumption before optional application admission, commutes under one arbitrary common interpreter. -/
theorem build (implementation : QueryImpl spec m) (coins : QueryImpl unifSpec (OracleComp spec))
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (OracleComp spec) Bool)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → StateT (RegistrationServerRootCompiler.Local n) (OracleComp spec)
      (RustM (core.option.Option Encoded)))
    (handle : Nat) (application : Option (Slice U8)) :
    state implementation (RegistrationNativePlatformServerSdk.build coins setup codec reserve sign encode handle application) =
      RegistrationNativePlatformServerSdk.build (fun query => simulateQ implementation (coins query))
        setup codec (state implementation reserve) sign (fun view => state implementation (encode view)) handle application := by
  funext before
  unfold state RegistrationNativePlatformServerSdk.build StateT.run
  cases moved : RegistrationServerSdkSource.take handle before with
  | mk value current => cases value with
    | none => rfl
    | some token =>
      dsimp only
      cases application with
      | none => rfl
      | some application =>
        exact congrArg (fun work : StateT (RegistrationServerFrontendCompiler.State n) m _ => work.run current)
          (complete implementation coins setup codec reserve sign encode token application)

/-- Any adaptive continuation runs after the exact native and external platform poststate, including every failed build outcome. -/
theorem build_bind {Next : Type} (implementation : QueryImpl spec m) (coins : QueryImpl unifSpec (OracleComp spec))
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (OracleComp spec) Bool)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → StateT (RegistrationServerRootCompiler.Local n) (OracleComp spec)
      (RustM (core.option.Option Encoded)))
    (handle : Nat) (application : Option (Slice U8))
    (next : RustM (Option (U64 × Encoded)) → StateT (RegistrationServerFrontendCompiler.State n) (OracleComp spec) Next) :
    state implementation (RegistrationNativePlatformServerSdk.build coins setup codec reserve sign encode handle application >>= next) =
      (RegistrationNativePlatformServerSdk.build (fun query => simulateQ implementation (coins query))
        setup codec (state implementation reserve) sign (fun view => state implementation (encode view)) handle application >>=
          fun result => state implementation (next result)) := by
  rw [state_bind, build]

end BeaconcryptCore.Computational.RegistrationNativePlatformBuildInterpret

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBuildInterpret.state_hom' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBuildInterpret.state_hom

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBuildInterpret.Publication.ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBuildInterpret.Publication.ready

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBuildInterpret.Publication.signing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBuildInterpret.Publication.signing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBuildInterpret.Publication.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBuildInterpret.Publication.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBuildInterpret.Completion.installWith' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBuildInterpret.Completion.installWith

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBuildInterpret.Completion.fromInitialWith' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBuildInterpret.Completion.fromInitialWith

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBuildInterpret.local_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBuildInterpret.local_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBuildInterpret.fromInitial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBuildInterpret.fromInitial

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBuildInterpret.sdk_fromInitial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBuildInterpret.sdk_fromInitial

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBuildInterpret.afterOccupancy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBuildInterpret.afterOccupancy

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBuildInterpret.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBuildInterpret.complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBuildInterpret.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBuildInterpret.build

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBuildInterpret.build_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBuildInterpret.build_bind
