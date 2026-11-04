-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPairedServerService
import BeaconcryptCore.Computational.RegistrationServerReferenceSourceLookup
/-! The corrected Server frontend retains public control, pin, consumed identifiers and one-use message references. Pin recomputation, peer occupancy, reservation and material demand are effectful operations at their literal source cuts. No root bytes, generated chain or native World occur in this executable frontend state. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialFrontend
open RegistrationServerMaterialFrontend (State token take)
open RegistrationServerReferenceRoot (Ready)
variable {m : Type → Type} [Monad m] {Encoded : Type}

abbrev Result (Encoded : Type) := RustM (Option (U64 × Encoded))
abbrev Service (m : Type → Type) (Encoded : Type) := pqxdh.ServerState →
  RegistrationBoundKeySchedule.PublicInitial → RegistrationNativeRelatedFamily.Message →
  m (RustM (RegistrationHiddenInstall.Result Encoded))

def finish (result : RustM (RegistrationHiddenInstall.Result Encoded)) (before : State) : Result Encoded × State :=
  match result with
  | .fail error => (.fail error, before)
  | .div => (.div, before)
  | .ok (.Err previous) => (.ok none, { before with control := previous })
  | .ok (.Ok published) => (.ok (some (published.key_id, published.encoded)), { before with control := published.control })

def afterResult (reserve : m Bool) (service : Service m Encoded) (control : pqxdh.ServerState)
    (reference : RegistrationNativeRelatedFamily.Message)
    (result : RustM (core.result.Result RegistrationBoundKeySchedule.PublicInitial pqxdh.ServerState)) :
    StateT State m (Result Encoded) :=
  match result with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err _) => pure (.ok none)
  | .ok (.Ok selected) => do
      let admitted ← StateT.lift reserve
      if admitted then do
        let published ← StateT.lift (service control selected reference)
        fun before => pure (finish published before)
      else pure (.ok none)

def afterOccupancy (reserve : m Bool) (service : Service m Encoded) (control : pqxdh.ServerState)
    (lookup : peer.CompletionLookup) (reference : RegistrationNativeRelatedFamily.Message) (occupied : Bool) :
    StateT State m (Result Encoded) :=
  afterResult reserve service control reference
    (RegistrationPublicationKernelErasure.mapOk RegistrationBoundKeySchedule.publicInitial <$> lookup.resume occupied)

def afterPin (reserve : m Bool) (present : U64 → m Bool) (service : Service m Encoded)
    (control : pqxdh.ServerState) (ready : Ready) (application : Slice U8)
    (current : RustM (core.option.Option session.ServerAuthenticationPin)) : StateT State m (Result Encoded) := fun before =>
  match current with
  | .fail error => pure (.fail error, before)
  | .div => pure (.div, before)
  | .ok .None => pure (.ok none, before)
  | .ok (.Some pin) => match peer.begin_completion_lookup control pin (token ready) application with
    | .fail error => pure (.fail error, before)
    | .div => pure (.div, before)
    | .ok (.Err _) => pure (.ok none, before)
    | .ok (.Ok lookup) => match lookup.request with
      | .fail error => pure (.fail error, before)
      | .div => pure (.div, before)
      | .ok keyId => if RegistrationServerSdkSource.preflight application keyId then do
          let occupied ← present keyId
          (afterOccupancy reserve service control lookup ready.reference occupied).run before
        else pure (.ok none, before)

def complete (pin : session.ServerAuthenticationPin → m (RustM (core.option.Option session.ServerAuthenticationPin)))
    (reserve : m Bool) (present : U64 → m Bool) (service : Service m Encoded)
    (ready : Ready) (application : Slice U8) : StateT State m (Result Encoded) := fun before => do
  let current ← pin before.pin
  (afterPin reserve present service before.control ready application current).run before

def build (pin : session.ServerAuthenticationPin → m (RustM (core.option.Option session.ServerAuthenticationPin)))
    (reserve : m Bool) (present : U64 → m Bool) (service : Service m Encoded)
    (handle : Nat) (application : Option (Slice U8)) : StateT State m (Result Encoded) := fun before =>
  match take handle before with
  | (none, current) => pure (.ok none, current)
  | (some ready, current) => match application with
    | none => pure (.ok none, current)
    | some application => (complete pin reserve present service ready application).run current

end BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialFrontend
