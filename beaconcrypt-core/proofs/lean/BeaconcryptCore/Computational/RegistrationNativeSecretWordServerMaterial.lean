-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordServerRoot

/-! The symbolic Server material frontend retains the exact native one-use handle, current-pin/application/allocator gates, raw record publication, ML signing and installation. Only its private material-demand address is a symbolic message. Evaluation forwards that single address and leaves every actual completion callback and reply unchanged. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordServerMaterial
open RegistrationNativeSecretWordMessage (Message ServerReady ServerState)
open PqxdhRecordLiftInterface (EnvEffects)
abbrev Ready := ServerReady
abbrev State := ServerState
variable {n : Nat} {Encoded : Type}

def token (ready : Ready) : peer.ConsumedRegistration := ⟨RegistrationBoundGate.atRoot ready.agreement RegistrationBoundKeySchedule.zero⟩

/-- Native replay insertion occurs before the capability is returned to the public API. -/
def retain (ready : Ready) : State → RustM (Option Nat × State) := fun before =>
  match RegistrationReplaySchedule.consume (RegistrationBoundGate.atRoot ready.agreement RegistrationBoundKeySchedule.zero) before.consumed with
  | .fail error => .fail error
  | .div => .div
  | .ok (.None, history) => .ok (none, { before with consumed := history })
  | .ok (.Some _, history) => .ok (some before.sessions.length,
      { before with consumed := history, sessions := before.sessions ++ [some ready] })

def take (handle : Nat) (before : State) : Option Ready × State :=
  match before.sessions[handle]? with
  | none => (none, before)
  | some none => (none, before)
  | some (some ready) => (some ready, { before with sessions := before.sessions.set handle none })

abbrev Spec (n : Nat) := RegistrationNativeSecretWordInterface.WordPairedPublicSpec n
abbrev Result := RustM (Option (Std.U64 × Pqxdh.Bytes))

def effect (query : (EnvEffects n).Domain) : OracleComp (Spec n) ((EnvEffects n).Range query) :=
  (Spec n).query (.inr (.inr query))

def finish (result : RustM (RegistrationNativePairedServerService.Result Pqxdh.Bytes)) :
    StateT State (OracleComp (Spec n)) Result := fun before =>
  match result with
  | .fail error => pure (.fail error, before)
  | .div => pure (.div, before)
  | .ok (.Err previous) => pure (.ok none, { before with control := previous })
  | .ok (.Ok published) => pure (.ok (some (published.key_id, published.encoded)),
      { before with control := published.control })

def commonLift : QueryImpl (RegistrationNativePairedServerService.Common n) (OracleComp (Spec n)) :=
  fun query => (Spec n).query (.inr query)

def admitted (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial) (reference : Message) :
    OracleComp (Spec n) (RustM (RegistrationNativePairedServerService.Result Encoded)) := do
  let selected ← ((Spec n).query (.inl reference) : OracleComp (Spec n) _)
  match selected with
  | none => pure (.ok (.Err control))
  | some choice =>
      simulateQ commonLift (RegistrationNativePairedServerService.publicBranch encode control initial choice)

/-- The selected transcript request runs through the same public World effect before any reservation or private material demand. -/
def adHash (pending : registration.ServerAdHash) : OracleComp (Spec n) RegistrationServerAdHash.Result :=
  match pending.request with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok request => do
    let digest ← effect (.inr (.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request)))
    pure (pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest)))

/-- The actual lookup is evaluated before preflight/occupancy and reservePeer; only an admitted native initializer asks the material service. -/
noncomputable def complete (wire : RegistrationNativeWire.Wire) (reservePeer : Bool)
    (ready : Ready) (application : Slice U8) : StateT State (OracleComp (Spec n)) Result := fun before =>
  match peer.begin_completion_lookup before.control before.pin (token ready) application with
  | .fail error => pure (.fail error, before)
  | .div => pure (.div, before)
  | .ok (.Err _) => pure (.ok none, before)
  | .ok (.Ok lookup) => match lookup.request with
      | .fail error => pure (.fail error, before)
      | .div => pure (.div, before)
      | .ok keyId =>
          if RegistrationServerSdkSource.preflight application keyId then do
            let occupied ← effect (.inr (.peerPresent keyId))
            match lookup.resume occupied with
            | .fail error => pure (.fail error, before)
            | .div => pure (.div, before)
            | .ok (.Err _) => pure (.ok none, before)
            | .ok (.Ok selected) => do
                let hashed ← adHash selected
                match hashed with
                | .fail error => pure (.fail error, before)
                | .div => pure (.div, before)
                | .ok (.Err _) => pure (.ok none, before)
                | .ok (.Ok initial) =>
                  if reservePeer then do
                    let published ← admitted wire.encodeResponse before.control
                      (RegistrationBoundKeySchedule.publicInitial initial) ready.reference
                    (finish published).run before
                  else pure (.ok none, before)
          else pure (.ok none, before)

/-- None is explicit raw-adapter cancellation. Every case first consumes the one-use handle, including oversized application and every later native failure. -/
noncomputable def build (wire : RegistrationNativeWire.Wire) (reservePeer : Bool)
    (handle : Nat) (application : Option (Slice U8)) : StateT State (OracleComp (Spec n)) Result := fun before =>
  match take handle before with
  | (none, current) => pure (.ok none, current)
  | (some ready, current) => match application with
      | none => pure (.ok none, current)
      | some application => (complete wire reservePeer ready application).run current

def realize (candidate : PqxdhKemIndCca.MlKemSharedSecret) :
    QueryImpl (Spec n) (OracleComp (RegistrationNativePairedServerService.PublicSpec n))
  | .inl message => (RegistrationNativePairedServerService.PublicSpec n).query
      (.inl (RegistrationNativeSecretWordMessage.eval candidate message))
  | .inr query => (RegistrationNativePairedServerService.PublicSpec n).query (.inr query)

/-- Every actual material reply and publication callback is preserved; only the root-service address is evaluated. -/
theorem admitted_source (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial) (reference : Message) :
    simulateQ (realize candidate) (admitted (n := n) encode control initial reference) =
      RegistrationNativePairedServerService.publicAdmitted encode control initial
        (RegistrationNativeSecretWordMessage.eval candidate reference) := by
  simp only [admitted, RegistrationNativePairedServerService.publicAdmitted, simulateQ_bind,
    simulateQ_spec_query, realize]
  apply bind_congr
  intro selected
  cases selected with
  | none => simp only [simulateQ_pure]
  | some choice =>
      rw [← QueryImpl.simulateQ_compose]
      have same : realize candidate ∘ₛ commonLift =
          (RegistrationNativePairedServerService.publicCommon :
            QueryImpl (RegistrationNativePairedServerService.Common n)
              (OracleComp (RegistrationNativePairedServerService.PublicSpec n))) := by
        funext query
        simp only [QueryImpl.compose, commonLift, simulateQ_spec_query, realize,
          RegistrationNativePairedServerService.publicCommon]
      rw [same]

/-- Evaluating the symbolic private address retains the complete same selected hash effect and owned continuation. -/
theorem adHash_source (candidate : PqxdhKemIndCca.MlKemSharedSecret) (pending : registration.ServerAdHash) :
    simulateQ (realize candidate) (adHash (n := n) pending) = RegistrationServerMaterialFrontend.adHash pending := by
  unfold adHash RegistrationServerMaterialFrontend.adHash
  cases pending.request with
  | fail error | div => simp only [simulateQ_pure]
  | ok request =>
      simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, effect, realize,
        RegistrationServerMaterialFrontend.effect]

/-- The consumed native token is independent of symbolic reference evaluation. -/
theorem token_eval (candidate : PqxdhKemIndCca.MlKemSharedSecret) (ready : Ready) :
    RegistrationServerMaterialFrontend.token (ready.eval candidate) = token ready := rfl

/-- Evaluating a moved one-use handle preserves both its result and the entire remaining session table. -/
theorem take_eval (candidate : PqxdhKemIndCca.MlKemSharedSecret) (handle : Nat) (before : State) :
    Prod.map (Option.map (ServerReady.eval candidate)) (ServerState.eval candidate) (take handle before) =
      RegistrationServerMaterialFrontend.take handle (before.eval candidate) := by
  simp only [take, RegistrationServerMaterialFrontend.take, ServerState.eval, List.getElem?_map]
  cases found : before.sessions[handle]? with
  | none => rfl
  | some entry => cases entry with
    | none => rfl
    | some ready => simp only [Option.map_some, Prod.map, ServerState.eval, List.map_set, Option.map_none]

private theorem finish_source (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (result : RustM (RegistrationNativePairedServerService.Result Pqxdh.Bytes)) (before : State) :
    Prod.map id (ServerState.eval candidate) <$> (simulateQ (realize candidate) ((finish (n := n) result).run before)) =
      (RegistrationServerMaterialFrontend.finish result).run (before.eval candidate) := by
  cases result with
  | fail error => rfl
  | div => rfl
  | ok result => cases result <;> rfl

/-- The complete admitted build retains all native gate failures, chronological publication effects and reached state after evaluating its private address. -/
theorem complete_source (candidate : PqxdhKemIndCca.MlKemSharedSecret) (wire : RegistrationNativeWire.Wire)
    (reservePeer : Bool) (ready : Ready) (application : Slice U8) (before : State) :
    Prod.map id (ServerState.eval candidate) <$>
      simulateQ (realize candidate) ((complete (n := n) wire reservePeer ready application).run before) =
      (RegistrationServerMaterialFrontend.complete wire reservePeer (ready.eval candidate) application).run (before.eval candidate) := by
  simp only [complete, RegistrationServerMaterialFrontend.complete, ServerState.eval, token_eval,
    StateT.run]
  split <;> try simp_all only [simulateQ_pure, map_pure, Prod.map, id_eq, ServerState.eval]
  split <;> try simp_all only [simulateQ_pure, map_pure, Prod.map, id_eq, ServerState.eval]
  split <;> try simp_all only [simulateQ_pure, map_pure, Prod.map, id_eq, ServerState.eval]
  simp only [simulateQ_bind, simulateQ_spec_query, effect, RegistrationServerMaterialFrontend.effect,
    realize, map_bind]
  apply bind_congr
  intro occupied
  split <;> try simp_all only [simulateQ_pure, map_pure, Prod.map, id_eq, ServerState.eval]
  simp only [simulateQ_bind, map_bind, adHash_source]
  apply bind_congr
  intro hashed
  cases hashed with
  | fail error | div => simp only [simulateQ_pure, map_pure, Prod.map, id_eq, ServerState.eval]
  | ok answer => cases answer with
    | Err previous => simp only [simulateQ_pure, map_pure, Prod.map, id_eq, ServerState.eval]
    | Ok initial =>
      dsimp only
      by_cases reserved : reservePeer = true
      · simp only [reserved, ite_true, simulateQ_bind, map_bind, admitted_source]
        apply bind_congr
        intro published
        exact finish_source candidate published before
      · simp only [reserved, Bool.false_eq_true, ite_false, simulateQ_pure, map_pure, Prod.map, id_eq, ServerState.eval]

/-- The actual whole one-use build controller has the exact native evaluated result and session state, including cancellation and every subsequent failure. -/
theorem build_source (candidate : PqxdhKemIndCca.MlKemSharedSecret) (wire : RegistrationNativeWire.Wire)
    (reservePeer : Bool) (handle : Nat) (application : Option (Slice U8)) (before : State) :
    Prod.map id (ServerState.eval candidate) <$>
      simulateQ (realize candidate) ((build (n := n) wire reservePeer handle application).run before) =
      (RegistrationServerMaterialFrontend.build wire reservePeer handle application).run (before.eval candidate) := by
  have takeSource := take_eval candidate handle before
  simp only [build, RegistrationServerMaterialFrontend.build, StateT.run]
  rcases actual : take handle before with ⟨selected, current⟩
  rw [actual] at takeSource
  rw [← takeSource]
  cases selected with
  | none => rfl
  | some ready => cases application with
    | none => rfl
    | some application => exact complete_source candidate wire reservePeer ready application current

end BeaconcryptCore.Computational.RegistrationNativeSecretWordServerMaterial
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordServerMaterial.admitted_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordServerMaterial.admitted_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordServerMaterial.token_eval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordServerMaterial.token_eval
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordServerMaterial.take_eval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordServerMaterial.take_eval
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordServerMaterial.complete_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordServerMaterial.complete_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordServerMaterial.build_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordServerMaterial.build_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordServerMaterial.adHash_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordServerMaterial.adHash_source
