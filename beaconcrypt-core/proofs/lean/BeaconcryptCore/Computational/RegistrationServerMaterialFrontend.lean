-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerReferenceRoot
import BeaconcryptCore.Computational.RegistrationNativeWire
import BeaconcryptCore.Computational.RegistrationServerSdkSource

/-! The Server material frontend owns only public control/pin, consumed IDs and one-use reference capabilities. Its state has no World, selected identity seed, prepared root32 or generated kernel. Actual completion lookup, complete response sizing, occupancy and reservation precede every material demand. Actual native signing, dynamic encoding and hidden/known installation remain the concrete paired service below. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerMaterialFrontend
open RegistrationServerReferenceRoot (Ready atRoot)
open PqxdhRecordLiftInterface (EnvEffects CapabilitySpec)
variable {n : Nat}

structure State where
  control : pqxdh.ServerState
  pin : session.ServerAuthenticationPin
  consumed : RegistrationReplaySchedule.State
  sessions : List (Option Ready)

def initial (control : pqxdh.ServerState) (pin : session.ServerAuthenticationPin) : State := ⟨control, pin, [], []⟩

def token (ready : Ready) : peer.ConsumedRegistration := ⟨atRoot ready RegistrationBoundKeySchedule.zero⟩

/-- Native replay insertion occurs before the capability is returned to the public API. -/
def retain (ready : Ready) : State → RustM (Option Nat × State) := fun before =>
  match RegistrationReplaySchedule.consume (atRoot ready RegistrationBoundKeySchedule.zero) before.consumed with
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

abbrev Spec (n : Nat) := RegistrationNativePairedServerService.PublicSpec n
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

/-- The public reference frontend executes the actual selected AD hash before reserving a peer or demanding private material. -/
def adHash (pending : registration.ServerAdHash) :
    OracleComp (Spec n) (RustM (core.result.Result registration.ServerInitialKdf pqxdh.ServerState)) :=
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
                    let published ← RegistrationNativePairedServerService.publicAdmitted wire.encodeResponse before.control
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

/-- Freshness is derived from the owned consumed-ID set, and the stored capability contains only the cleared public agreement/reference. -/
theorem retain_fresh (ready : Ready) (before : State)
    (fresh : before.consumed.contains (absBytes ready.agreement.pending.registration_id.bytes) = false) :
    retain ready before = .ok (some before.sessions.length,
      { before with
        consumed := before.consumed ++ [absBytes ready.agreement.pending.registration_id.bytes]
        sessions := before.sessions ++ [some ready] }) := by
  have actual := RegistrationReplaySchedule.consume_fresh
    (atRoot ready RegistrationBoundKeySchedule.zero) before.consumed
      (by simpa only [atRoot, RegistrationBoundGate.atRoot] using fresh)
  simp only [retain, actual]
  rfl

/-- A live source capability is removed exactly once before it can reach a material query. -/
theorem take_live (handle : Nat) (ready : Ready) (before : State)
    (live : before.sessions[handle]? = some (some ready)) :
    take handle before = (some ready, { before with sessions := before.sessions.set handle none }) := by
  simp only [take, live]

/-- Reusing a taken handle reaches no gate, KDF, hash, signing or key service. -/
theorem build_taken (wire : RegistrationNativeWire.Wire) (reservePeer : Bool) (handle : Nat)
    (application : Option (Slice U8)) (before : State) (taken : before.sessions[handle]? = some none) :
    (build (n := n) wire reservePeer handle application).run before = pure (.ok none, before) := by
  simp only [build, take, taken, StateT.run]

/-- Parsing/size cancellation consumes the live handle and performs no service query. -/
theorem build_cancel (wire : RegistrationNativeWire.Wire) (reservePeer : Bool) (handle : Nat)
    (ready : Ready) (before : State) (live : before.sessions[handle]? = some (some ready)) :
    (build (n := n) wire reservePeer handle none).run before =
      pure (.ok none, { before with sessions := before.sessions.set handle none }) := by
  simp only [build, take_live handle ready before live, StateT.run]

/-- A rejected complete-message preflight performs no occupancy or material request. -/
theorem complete_preflight (wire : RegistrationNativeWire.Wire) (reservePeer : Bool) (ready : Ready)
    (application : Slice U8) (before : State) (lookup : peer.CompletionLookup)
    (actual : peer.begin_completion_lookup before.control before.pin (token ready) application = .ok (.Ok lookup))
    (keyId : Std.U64) (requested : lookup.request = .ok keyId)
    (rejected : RegistrationServerSdkSource.preflight application keyId = false) :
    (complete (n := n) wire reservePeer ready application).run before = pure (.ok none, before) := by
  simp only [complete, StateT.run, actual, requested, rejected, Bool.false_eq_true, ite_false]

end BeaconcryptCore.Computational.RegistrationServerMaterialFrontend

/-- info: 'BeaconcryptCore.Computational.RegistrationServerMaterialFrontend.retain_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerMaterialFrontend.retain_fresh

/-- info: 'BeaconcryptCore.Computational.RegistrationServerMaterialFrontend.take_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerMaterialFrontend.take_live

/-- info: 'BeaconcryptCore.Computational.RegistrationServerMaterialFrontend.build_taken' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerMaterialFrontend.build_taken

/-- info: 'BeaconcryptCore.Computational.RegistrationServerMaterialFrontend.build_cancel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerMaterialFrontend.build_cancel

/-- info: 'BeaconcryptCore.Computational.RegistrationServerMaterialFrontend.complete_preflight' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerMaterialFrontend.complete_preflight
