-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProfile
import BeaconcryptCore.Computational.RegistrationNativeMldsaGenerateBounds
/-! Arbitrary query predicates compose through both private-native and external-platform state layers. Actual effectful Beacon/Server publication preserves predicate-safe primitive and encoder leaves through every source failure branch. Instantiating the predicate with generation exclusion supplies resource accounting; signing validity can reuse the same literal controller proofs. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformQuerySafety
open RegistrationNativePlatformMldsaProgram (M)
open RegistrationNativeMldsaProgram (Spec)
variable {source : RegistrationNativeMldsa.Source} {Platform State Value Next : Type}
variable (predicate : (Spec source).Domain → Prop)

def Safe (work : StateT State (M source Platform) Value) : Prop :=
  ∀ before previous, ((work.run before).run previous).AllQueriesSatisfy predicate

theorem pure_safe (value : Value) : Safe predicate (pure value : StateT State (M source Platform) Value) :=
  fun _ _ => allQueriesSatisfy_pure _ _

theorem bind_safe (work : StateT State (M source Platform) Value)
    (next : Value → StateT State (M source Platform) Next)
    (first : Safe predicate work) (rest : ∀ value, Safe predicate (next value)) :
    Safe predicate (work >>= next) := by
  intro before previous
  simp only [StateT.run_bind]
  exact allQueriesSatisfy_bind (first before previous)
    (fun result => rest result.1.1 result.1.2 result.2)

theorem map_safe (work : StateT State (M source Platform) Value) (observe : Value → Next)
    (safe : Safe predicate work) : Safe predicate (observe <$> work) := by
  change Safe predicate (work >>= fun value => pure (observe value))
  exact bind_safe predicate work _ safe (fun _ => pure_safe predicate _)

theorem simulate_safe {I : Type} {queries : OracleSpec I}
    (handler : QueryImpl queries (StateT State (M source Platform)))
    (allowed : ∀ query, Safe predicate (handler query)) (work : OracleComp queries Value) :
    Safe predicate (simulateQ handler work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_safe predicate value
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact bind_safe predicate _ _ (allowed query) ih

private theorem ordinary_safe (coins : ∀ coin, predicate (.inl coin)) (work : ProbComp Value) :
    (RegistrationNativeMldsaProgram.lift (source := source) work).AllQueriesSatisfy predicate := by
  induction work using OracleComp.inductionOn with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind query next ih =>
      simp only [RegistrationNativeMldsaProgram.lift, simulateQ_bind, simulateQ_spec_query,
        RegistrationNativeMldsaProgram.ordinary]
      exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨coins query, ih⟩

theorem lift_safe (coins : ∀ coin, predicate (.inl coin))
    (work : StateT State (StateT Platform ProbComp) Value) :
    Safe predicate (RegistrationNativePlatformMldsaProgram.lift (source := source) work) :=
  fun before previous => ordinary_safe predicate coins ((work.run before).run previous)

theorem inject_safe (work : StateT State (OracleComp (Spec source)) Value)
    (allowed : ∀ before, (work.run before).AllQueriesSatisfy predicate) :
    Safe predicate (RegistrationNativePlatformMldsaProgram.inject (Platform := Platform) work) := by
  intro before previous
  change ((StateT.lift (work.run before) : StateT Platform (OracleComp (Spec source)) (Value × State)).run previous).AllQueriesSatisfy predicate
  rw [StateT.run_lift]
  exact allQueriesSatisfy_bind (allowed before) (fun _ => allQueriesSatisfy_pure _ _)

theorem frame_safe {Inner : Type}
    (select : State → Inner) (update : State → Inner → State)
    (work : StateT Inner (M source Platform) Value) (allowed : Safe predicate work) :
    Safe predicate (fun before => Prod.map id (update before) <$> work.run (select before)) := by
  intro before previous
  change ((Prod.map id (update before) <$> work.run (select before)).run previous).AllQueriesSatisfy predicate
  rw [StateT.run_map]
  rw [← bind_pure_comp]
  exact allQueriesSatisfy_bind (allowed (select before) previous) (fun _ => allQueriesSatisfy_pure _ _)

attribute [local irreducible] registration.BeaconInitHash.resume registration.BeaconFingerprint.resume
  registration.BeaconMldsaSigning.resume registration.BeaconEd25519Signing.resume registration.begin_beacon_init

namespace Beacon
open RegistrationNativePlatformBeaconPublication
open RegistrationBeaconInitExecutor (Spec Result edRank ed_rank)
variable {Encoded : Type}

private theorem continue_safe {Input : Type} (action : RustM Input)
    (next : Input → StateT State (M source Platform) (RustM (Result Encoded)))
    (allowed : ∀ value, Safe predicate (next value)) :
    Safe predicate (continueWith action next) := by
  cases action with
  | ok value => exact allowed value
  | fail error | div => exact pure_safe predicate _

theorem ready (encode : registration.SignedInitView → StateT State (M source Platform) (RustM (core.option.Option Encoded)))
    (allowed : ∀ view, Safe predicate (encode view)) (pending : registration.BeaconInitReady) :
    Safe predicate (RegistrationNativePlatformBeaconPublication.ready encode pending) := by
  unfold RegistrationNativePlatformBeaconPublication.ready
  apply continue_safe
  intro view
  exact bind_safe predicate _ _ (allowed view) (fun _ => pure_safe predicate _)

theorem signing (implementation : QueryImpl Spec (StateT State (M source Platform)))
    (allowed : ∀ query, Safe predicate (implementation query))
    (encode : registration.SignedInitView → StateT State (M source Platform) (RustM (core.option.Option Encoded)))
    (encoded : ∀ view, Safe predicate (encode view))
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.BeaconMldsaSigning) :
    Safe predicate (fromSigning implementation encode payload digest pending) := by
  unfold fromSigning
  apply continue_safe
  intro request
  apply bind_safe predicate _ _ (allowed (.inl (.sign request payload digest)))
  intro reply
  apply continue_safe
  intro effect
  cases effect with
  | Ready selected => exact ready predicate encode encoded selected
  | _ => exact pure_safe predicate _

theorem hashing (implementation : QueryImpl Spec (StateT State (M source Platform)))
    (allowed : ∀ query, Safe predicate (implementation query))
    (encode : registration.SignedInitView → StateT State (M source Platform) (RustM (core.option.Option Encoded)))
    (encoded : ∀ view, Safe predicate (encode view)) (pending : registration.BeaconInitHash) :
    Safe predicate (fromHash implementation encode pending) := by
  unfold fromHash
  apply continue_safe
  intro request
  apply bind_safe predicate _ _ (allowed (.inl (.hash request)))
  intro digest
  apply continue_safe
  intro effect
  cases effect with
  | MldsaSigningRequested selected => exact signing predicate implementation allowed encode encoded _ digest selected
  | _ => exact pure_safe predicate _

theorem fingerprint (implementation : QueryImpl Spec (StateT State (M source Platform)))
    (allowed : ∀ query, Safe predicate (implementation query))
    (encode : registration.SignedInitView → StateT State (M source Platform) (RustM (core.option.Option Encoded)))
    (encoded : ∀ view, Safe predicate (encode view)) (pending : registration.BeaconFingerprint) :
    Safe predicate (fromFingerprint implementation encode pending) := by
  unfold fromFingerprint
  apply continue_safe
  intro request
  apply bind_safe predicate _ _ (allowed (.inl (.hash request)))
  intro digest
  apply continue_safe
  intro effect
  cases effect with
  | HashRequested selected => exact hashing predicate implementation allowed encode encoded selected
  | _ => exact pure_safe predicate _

theorem ed (implementation : QueryImpl Spec (StateT State (M source Platform)))
    (allowed : ∀ query, Safe predicate (implementation query))
    (encode : registration.SignedInitView → StateT State (M source Platform) (RustM (core.option.Option Encoded)))
    (encoded : ∀ view, Safe predicate (encode view)) (pending : registration.BeaconEd25519Signing) :
    Safe predicate (fromEd implementation encode pending) := by
  rw [fromEd.eq_def]
  apply continue_safe
  intro request
  apply bind_safe predicate _ _ (allowed (.inr request))
  intro reply
  cases actual : pending.resume reply with
  | fail error | div => exact pure_safe predicate _
  | ok effect => cases effect with
    | Ed25519SigningRequested next => exact ed implementation allowed encode encoded next
    | FingerprintRequested selected => exact fingerprint predicate implementation allowed encode encoded selected
    | _ => exact pure_safe predicate _
termination_by edRank pending
decreasing_by exact ed_rank pending reply next actual

theorem begin (implementation : QueryImpl Spec (StateT State (M source Platform)))
    (allowed : ∀ query, Safe predicate (implementation query))
    (encode : registration.SignedInitView → StateT State (M source Platform) (RustM (core.option.Option Encoded)))
    (encoded : ∀ view, Safe predicate (encode view)) (control : pqxdh.BeaconFresh)
    (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (publicKey : Std.Array U8 1952#usize) :
    Safe predicate (RegistrationNativePlatformBeaconPublication.begin implementation encode control inputs coins pin publicKey) := by
  unfold RegistrationNativePlatformBeaconPublication.begin
  apply continue_safe
  intro effect
  cases effect with
  | Ed25519SigningRequested selected => exact ed predicate implementation allowed encode encoded selected
  | _ => exact pure_safe predicate _
end Beacon

attribute [local irreducible] registration.ServerResponseHash.resume registration.ServerResponseSigning.resume
namespace Server
open RegistrationNativePlatformServerPublication
open RegistrationWorldServerPublication (Result)
variable {Encoded : Type}

private theorem continue_safe {Input : Type} (action : RustM Input)
    (next : Input → StateT State (M source Platform) (RustM (Result Encoded)))
    (allowed : ∀ value, Safe predicate (next value)) :
    Safe predicate (continueWith action next) := by
  cases action with
  | ok value => exact allowed value
  | fail error | div => exact pure_safe predicate _

private theorem result_safe {Input : Type} (action : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → StateT State (M source Platform) (RustM (Result Encoded)))
    (allowed : ∀ value, Safe predicate (next value)) :
    Safe predicate (continueResult action next) := by
  cases action with
  | fail error | div => exact pure_safe predicate _
  | ok result => cases result with
    | Err previous => exact pure_safe predicate _
    | Ok value => exact allowed value

theorem ready (encode : registration.SignedResponseView → StateT State (M source Platform) (RustM (core.option.Option Encoded)))
    (allowed : ∀ view, Safe predicate (encode view)) (pending : registration.ServerResponseReady) :
    Safe predicate (RegistrationNativePlatformServerPublication.ready encode pending) := by
  unfold RegistrationNativePlatformServerPublication.ready
  apply continue_safe
  intro view
  exact bind_safe predicate _ _ (allowed view) (fun _ => pure_safe predicate _)

theorem signing (implementation : QueryImpl RegistrationSigningShared.Spec (StateT State (M source Platform)))
    (allowed : ∀ query, Safe predicate (implementation query))
    (encode : registration.SignedResponseView → StateT State (M source Platform) (RustM (core.option.Option Encoded)))
    (encoded : ∀ view, Safe predicate (encode view))
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.ServerResponseSigning) :
    Safe predicate (RegistrationNativePlatformServerPublication.signing implementation encode payload digest pending) := by
  unfold RegistrationNativePlatformServerPublication.signing
  apply continue_safe
  intro request
  apply bind_safe predicate _ _ (allowed (.sign request payload digest))
  intro reply
  exact result_safe predicate _ _ (fun selected => ready predicate encode encoded selected)

theorem program (implementation : QueryImpl RegistrationSigningShared.Spec (StateT State (M source Platform)))
    (allowed : ∀ query, Safe predicate (implementation query))
    (encode : registration.SignedResponseView → StateT State (M source Platform) (RustM (core.option.Option Encoded)))
    (encoded : ∀ view, Safe predicate (encode view)) (pending : registration.ServerResponseHash) :
    Safe predicate (RegistrationNativePlatformServerPublication.program implementation encode pending) := by
  unfold RegistrationNativePlatformServerPublication.program
  apply continue_safe
  intro request
  apply bind_safe predicate _ _ (allowed (.hash request))
  intro digest
  exact result_safe predicate _ _ (fun selected => signing predicate implementation allowed encode encoded _ digest selected)
end Server

end BeaconcryptCore.Computational.RegistrationNativePlatformQuerySafety

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformQuerySafety.pure_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformQuerySafety.pure_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformQuerySafety.bind_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformQuerySafety.bind_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformQuerySafety.map_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformQuerySafety.map_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformQuerySafety.simulate_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformQuerySafety.simulate_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformQuerySafety.lift_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformQuerySafety.lift_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformQuerySafety.inject_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformQuerySafety.inject_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformQuerySafety.frame_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformQuerySafety.frame_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformQuerySafety.Beacon.ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformQuerySafety.Beacon.ready

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformQuerySafety.Beacon.signing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformQuerySafety.Beacon.signing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformQuerySafety.Beacon.hashing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformQuerySafety.Beacon.hashing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformQuerySafety.Beacon.fingerprint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformQuerySafety.Beacon.fingerprint

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformQuerySafety.Beacon.ed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformQuerySafety.Beacon.ed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformQuerySafety.Beacon.begin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformQuerySafety.Beacon.begin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformQuerySafety.Server.ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformQuerySafety.Server.ready

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformQuerySafety.Server.signing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformQuerySafety.Server.signing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformQuerySafety.Server.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformQuerySafety.Server.program
