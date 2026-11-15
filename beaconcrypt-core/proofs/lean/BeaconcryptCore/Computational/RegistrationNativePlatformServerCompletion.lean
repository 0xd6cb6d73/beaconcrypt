-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationWorldServerCompletion
import BeaconcryptCore.Computational.RegistrationServerAdHash
import BeaconcryptCore.Computational.RegistrationNativePlatformServerPublication

/-! The actual response-dependent AD hash runs before initial record construction and peer reservation. Effectful response writing follows the first-record source controller and precedes peer installation. Ordinary randomness shares the outer monad with platform actions, and the native Local state retains its World and complete Server signing history. The record codec remains an explicit boundary. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerCompletion
open PqxdhRecordLiftInterface
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationWorldAgreement (State)
open RegistrationWorldServerCompletion (Result)
variable {n : Nat} {Auxiliary Encoded Value ι KemSK Reader Response : Type} {base : OracleSpec ι}

noncomputable def nativeOutgoing
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply) :
    QueryImpl RegistrationSigningShared.Spec (StateT (State n Auxiliary) ProbComp) := fun query before =>
  (fun result => (result.1, { before with world := result.2 })) <$>
    (RegistrationWorldSigning.outgoing sign query).run before.world

private theorem nativeOutgoing_run
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : RegistrationSigningShared.Spec.Domain) (before : State n Auxiliary) :
    (nativeOutgoing sign query).run before =
      (fun result => (result.1, { before with world := result.2 })) <$>
        (RegistrationWorldSigning.outgoing sign query).run before.world := rfl

/-- Every adaptive signing/hash query uses its immediate predecessor's shared World and leaves the other Local coordinates intact. -/
theorem nativeOutgoing_program
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp RegistrationSigningShared.Spec Value) (before : State n Auxiliary) :
    (simulateQ (nativeOutgoing sign) work).run before =
      (fun result => (result.1, { before with world := result.2 })) <$>
        (simulateQ (RegistrationWorldSigning.outgoing sign) work).run before.world := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, nativeOutgoing_run,
        bind_map_left, ih, map_bind]

variable {m : Type → Type} [Monad m]

def liftNative (coins : QueryImpl unifSpec m) (work : StateT (State n Auxiliary) ProbComp Value) :
    StateT (State n Auxiliary) m Value := fun before => simulateQ coins (work.run before)

def continueWith {Input : Type} (action : RustM Input)
    (next : Input → m (RustM (Result Encoded))) : m (RustM (Result Encoded)) :=
  match action with
  | .ok value => next value
  | .fail error => pure (.fail error)
  | .div => pure .div

def continueResult {Input : Type} (action : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → m (RustM (Result Encoded))) : m (RustM (Result Encoded)) :=
  match action with
  | .ok (.Ok value) => next value
  | .ok (.Err previous) => pure (.ok (.Err previous))
  | .fail error => pure (.fail error)
  | .div => pure .div

def installWith (capability : QueryImpl (CapabilitySpec n) m)
    (control : pqxdh.ServerState) (published : registration.PublishedServerResponse Encoded) :
    m (RustM (Result Encoded)) :=
  continueResult (peer.begin_peer_insert control published) fun pending =>
    continueWith pending.request fun keyId =>
      continueWith pending.into_parts fun parts => do
        let inserted ← capability (.installServer keyId (PeerBinding.ofSession parts.1.binding) (.known parts.1.ratchet))
        pure (parts.2.finish inserted)

noncomputable def outgoing (coins : QueryImpl unifSpec m)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply) :
    QueryImpl RegistrationSigningShared.Spec (StateT (State n Auxiliary) m) :=
  fun query => liftNative coins (nativeOutgoing sign query)

noncomputable def capability (coins : QueryImpl unifSpec m) :
    QueryImpl (CapabilitySpec n) (StateT (State n Auxiliary) m) :=
  fun query => liftNative coins (RegistrationWorldServerCompletion.capability query)

noncomputable def records (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response) :
    QueryImpl RegistrationRecordPrimitives.Spec (StateT (State n Auxiliary) m) :=
  fun query => liftNative coins (RegistrationWorldRecords.handler setup codec query)

/-- Arbitrary actual hash replies are consumed by the owned core continuation before record initialization. -/
def adHashWith (hash : registration.HashRequest → m (core.option.Option (Std.Array U8 64#usize)))
    (pending : registration.ServerAdHash) :
    m (RustM (core.result.Result registration.ServerInitialKdf pqxdh.ServerState)) :=
  RegistrationServerAdHash.runWith hash pending

noncomputable def adHash (coins : QueryImpl unifSpec m) (pending : registration.ServerAdHash) :
    StateT (State n Auxiliary) m
      (RustM (core.result.Result registration.ServerInitialKdf pqxdh.ServerState)) :=
  adHashWith (fun request => do
    let digest ← capability coins (.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request))
    pure (.Some (RegistrationAuthenticationShared.digestArray digest))) pending

def fromInitialWith
    (record : QueryImpl RegistrationRecordPrimitives.Spec m)
    (sign : QueryImpl RegistrationSigningShared.Spec m)
    (capability : QueryImpl (CapabilitySpec n) m)
    (encode : registration.SignedResponseView → m (RustM (core.option.Option Encoded)))
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) : m (RustM (Result Encoded)) := do
  let record ← simulateQ record (RegistrationServerRecordExecutor.fromInitial pending)
  continueResult record fun response => do
    let published ← RegistrationNativePlatformServerPublication.program sign encode response
    continueResult published (installWith capability control)

noncomputable def fromInitial (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → StateT (State n Auxiliary) m (RustM (core.option.Option Encoded)))
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    StateT (State n Auxiliary) m (RustM (Result Encoded)) :=
  fromInitialWith (records coins setup codec) (outgoing coins sign) (capability coins) encode control pending

/-- The ordinary random sampler's identity specialization preserves the complete native value and Local state. -/
theorem liftNative_id (work : StateT (State n Auxiliary) ProbComp Value) :
    liftNative (QueryImpl.id' unifSpec) work = work := by
  funext before
  exact simulateQ_id' (work.run before)

private theorem continueWith_interpret {κ : Type} {spec : OracleSpec κ}
    (implementation : QueryImpl spec m) {Input : Type} (action : RustM Input)
    (next : Input → OracleComp spec (RustM (Result Encoded))) :
    simulateQ implementation (continueWith action next) =
      continueWith action (fun value => simulateQ implementation (next value)) := by
  cases action <;> rfl

private theorem continueResult_interpret {κ : Type} {spec : OracleSpec κ}
    (implementation : QueryImpl spec m) {Input : Type} (action : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → OracleComp spec (RustM (Result Encoded))) :
    simulateQ implementation (continueResult action next) =
      continueResult action (fun value => simulateQ implementation (next value)) := by
  cases action with
  | fail error => rfl
  | div => rfl
  | ok result => cases result <;> rfl

variable [LawfulMonad m]

theorem installWith_interpret {κ : Type} {spec : OracleSpec κ}
    (implementation : QueryImpl spec m)
    (capability : QueryImpl (CapabilitySpec n) (OracleComp spec))
    (control : pqxdh.ServerState) (published : registration.PublishedServerResponse Encoded) :
    simulateQ implementation (installWith capability control published) =
      installWith (fun query => simulateQ implementation (capability query)) control published := by
  unfold installWith
  rw [continueResult_interpret]
  apply congrArg (continueResult (peer.begin_peer_insert control published))
  funext pending
  rw [continueWith_interpret]
  apply congrArg (continueWith pending.request)
  funext keyId
  rw [continueWith_interpret]
  apply congrArg (continueWith pending.into_parts)
  funext parts
  rw [simulateQ_bind]
  apply bind_congr
  intro inserted
  exact simulateQ_pure _ _

/-- The first record, response signing/writing and actual install capability compose under one arbitrary shared interpreter. -/
theorem fromInitialWith_interpret {κ : Type} {spec : OracleSpec κ}
    (implementation : QueryImpl spec m)
    (record : QueryImpl RegistrationRecordPrimitives.Spec (OracleComp spec))
    (sign : QueryImpl RegistrationSigningShared.Spec (OracleComp spec))
    (capability : QueryImpl (CapabilitySpec n) (OracleComp spec))
    (encode : registration.SignedResponseView → OracleComp spec (RustM (core.option.Option Encoded)))
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    simulateQ implementation (fromInitialWith record sign capability encode control pending) =
      fromInitialWith (fun query => simulateQ implementation (record query))
        (fun query => simulateQ implementation (sign query))
        (fun query => simulateQ implementation (capability query))
        (fun view => simulateQ implementation (encode view)) control pending := by
  unfold fromInitialWith
  rw [simulateQ_bind, ← QueryImpl.simulateQ_compose]
  apply bind_congr
  intro recorded
  rw [continueResult_interpret]
  apply congrArg (continueResult recorded)
  funext response
  rw [simulateQ_bind, RegistrationNativePlatformServerPublication.program_interpret]
  apply bind_congr
  intro published
  rw [continueResult_interpret]
  apply congrArg (continueResult published)
  funext ready
  exact installWith_interpret implementation capability control ready

/-- The ordinary random interpreter preserves the selected AD hash and its exact continuation. -/
theorem adHash_pure (pending : registration.ServerAdHash) :
    adHash (n := n) (Auxiliary := Auxiliary) (QueryImpl.id' unifSpec) pending =
      RegistrationWorldServerCompletion.adHash pending := by
  have capability_id : capability (n := n) (Auxiliary := Auxiliary) (QueryImpl.id' unifSpec) =
      RegistrationWorldServerCompletion.capability := by
    funext query
    exact liftNative_id _
  unfold adHash adHashWith RegistrationServerAdHash.runWith
  rw [capability_id]
  cases requested : pending.request <;> simp only [RegistrationWorldServerCompletion.adHash, requested, bind_assoc, pure_bind]

theorem installWith_native (control : pqxdh.ServerState) (published : registration.PublishedServerResponse Encoded) :
    installWith (RegistrationWorldServerCompletion.capability (n := n) (Auxiliary := Auxiliary)) control published =
      RegistrationWorldServerCompletion.install control published := rfl

theorem signing_pure
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseHash) :
    RegistrationNativePlatformServerPublication.program (nativeOutgoing (n := n) (Auxiliary := Auxiliary) sign)
      (fun view => pure (.ok (encode view))) pending =
      RegistrationWorldServerCompletion.signing sign encode pending := by
  have same : simulateQ (nativeOutgoing (n := n) (Auxiliary := Auxiliary) sign)
      (RegistrationWorldServerPublication.program encode pending) =
      RegistrationNativePlatformServerPublication.program (nativeOutgoing sign)
        (fun view => pure (.ok (encode view))) pending := by
    rw [← RegistrationNativePlatformServerPublication.program_pure,
      RegistrationNativePlatformServerPublication.program_interpret]
    simp only [simulateQ_spec_query, simulateQ_pure]
  rw [← same]
  funext before
  exact nativeOutgoing_program sign _ before

/-- A pure writer and the unchanged ordinary random sampler recover the complete original logical native first-record/publication/install computation. -/
theorem fromInitial_pure (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    fromInitial (n := n) (Auxiliary := Auxiliary) (QueryImpl.id' unifSpec) setup codec sign
      (fun view => pure (.ok (encode view))) control pending =
      RegistrationWorldServerCompletion.fromInitial setup codec sign encode control pending := by
  have record_id : records (n := n) (Auxiliary := Auxiliary) (QueryImpl.id' unifSpec) setup codec =
      RegistrationWorldRecords.handler setup codec := by
    funext query
    exact liftNative_id _
  have sign_id : outgoing (n := n) (Auxiliary := Auxiliary) (QueryImpl.id' unifSpec) sign = nativeOutgoing sign := by
    funext query
    exact liftNative_id _
  have capability_id : capability (n := n) (Auxiliary := Auxiliary) (QueryImpl.id' unifSpec) =
      RegistrationWorldServerCompletion.capability := by
    funext query
    exact liftNative_id _
  unfold fromInitial
  rw [record_id, sign_id, capability_id]
  unfold fromInitialWith RegistrationWorldServerCompletion.fromInitial
  apply bind_congr
  intro recorded
  cases recorded with
  | fail error => rfl
  | div => rfl
  | ok result =>
    cases result with
    | Err previous => rfl
    | Ok response =>
      change (do
        let published ← RegistrationNativePlatformServerPublication.program (nativeOutgoing sign)
          (fun view => pure (.ok (encode view))) response
        continueResult published (installWith RegistrationWorldServerCompletion.capability control)) = _
      rw [signing_pure]
      unfold RegistrationWorldServerCompletion.publish
      apply bind_congr
      intro published
      cases published with
      | fail error => rfl
      | div => rfl
      | ok result =>
        cases result with
        | Err previous => rfl
        | Ok ready => exact installWith_native control ready
end BeaconcryptCore.Computational.RegistrationNativePlatformServerCompletion

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerCompletion.nativeOutgoing_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerCompletion.nativeOutgoing_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerCompletion.liftNative_id' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerCompletion.liftNative_id

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerCompletion.installWith_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerCompletion.installWith_interpret

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerCompletion.fromInitialWith_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerCompletion.fromInitialWith_interpret

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerCompletion.installWith_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerCompletion.installWith_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerCompletion.signing_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerCompletion.signing_pure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerCompletion.fromInitial_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerCompletion.fromInitial_pure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerCompletion.adHash_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerCompletion.adHash_pure
