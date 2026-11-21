-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCompiler
import BeaconcryptCore.Computational.RegistrationNativeIdentitySigningRole
import BeaconcryptCore.Computational.RegistrationNativeIdentityHashRoute
import BeaconcryptCore.Computational.RegistrationNativeIdentityAdaptiveHashCapture

/-! A public bundle-attempt position arms the indexed one-time-message censor. The proxy runs the actual indexed source program, forwards independent identity/DH/report operations, and substitutes a client-known signature only after a successful fresh-message selection. Only the current target bundle's internal Init hash receives the symbolic token. The scanner also receives the client's complete prior known hash-input prefix at selection. This layer contains no identity seed or physical hidden hash address. The later source coupling and finite causal cover are separate obligations. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCompiler
open PqxdhJointPhase1Reports (ProtocolSpec)
open RegistrationNativeRawAdapter (TypedSpec)
open PqxdhEd25519EufCma (Ed25519Signature)
variable {S Value : Type}

/-- Both annotations are known client data. None is the private physical address token. -/
structure HashInput where
  message : Option Pqxdh.Bytes
  input : Option Pqxdh.Bytes

abbrev SelectSpec := Pqxdh.Bytes →ₒ Bool
abbrev ScanSpec := (Pqxdh.Bytes × List Pqxdh.Bytes) →ₒ Unit
abbrev HashSpec := HashInput →ₒ (CtxRomAuth.CtxDigest × Nat)
abbrev Spec := ((ProtocolSpec + SelectSpec) + ScanSpec) + HashSpec

structure Mode where
  bundles : Nat := 0
  armed : Bool := false
  active : Bool := false
  target : Option Pqxdh.Bytes := none
  knownInputs : List Pqxdh.Bytes := []
  deriving Inhabited

def protocol (query : ProtocolSpec.Domain) : OracleComp Spec (ProtocolSpec.Range query) :=
  Spec.query (.inl (.inl (.inl query)))

def select (message : Pqxdh.Bytes) : OracleComp Spec Bool :=
  Spec.query (.inl (.inl (.inr message)))

def inspect (message : Pqxdh.Bytes) (inputs : List Pqxdh.Bytes) : OracleComp Spec Unit :=
  Spec.query (.inl (.inr (message, inputs)))

/-- All attempted bundles count, including invalid handles and failed writers. Other callbacks disarm the internal hash token. -/
def enter (position : Nat) (query : TypedSpec.Domain) (before : Mode) : Mode :=
  match query with
  | .inr (.bundle _) => { before with bundles := before.bundles + 1, armed := before.bundles == position, active := false }
  | _ => { before with armed := false, active := false }

def hashInput (before : Mode) (bytes : Pqxdh.Bytes) : HashInput :=
  ⟨before.target, if before.active then RegistrationNativeIdentityHashRoute.route bytes else some bytes⟩

/-- Selection occurs before the first omitted signing call. A successful selection scans every earlier client-known address before resuming that source call. -/
def prepare (selected handle : Nat) (message : Pqxdh.Bytes) : StateT Mode (OracleComp Spec) Unit := fun before => do
  if handle = selected ∧ RegistrationNativeIdentitySigningRole.oneTime message then
    let chosen ← if before.armed ∧ before.target = none then select message else pure false
    let target := if chosen then some message else before.target
    if chosen then inspect message before.knownInputs else pure ()
    pure ((), { before with target := target, active := target == some message })
  else pure ((), before)

def signing (selected : Nat) (placeholder : Ed25519Signature) (handle : Nat) (message : Pqxdh.Bytes) :
    StateT Mode (OracleComp Spec) (Option Ed25519Signature) := do
  prepare selected handle message
  let before ← get
  if handle = selected ∧ before.target = some message then pure (some placeholder)
  else StateT.lift (protocol (.inl (.inr (.service handle (.sign message)))))

/-- The frontend still executes its original signing continuation and records only the returned, client-known placeholder. -/
def implementation (selected : Nat) (placeholder : Ed25519Signature) :
    QueryImpl RegistrationNativePlatformIdentityCtxCompiler.Spec (StateT Mode (OracleComp Spec))
  | .inl (.inl (.inr (.service handle (.sign message)))) => signing selected placeholder handle message
  | .inl query => StateT.lift (protocol query)
  | .inr bytes => fun before => do
      let described := hashInput before bytes
      let answer ← Spec.query (.inr described)
      pure (answer, { before with knownInputs := match described.input with
        | none => before.knownInputs
        | some input => before.knownInputs ++ [input] })

/-- The same complete source callback executes after a public position update. No secret signing-stage or bad-accept test is consulted. -/
def callback (selected position : Nat) (placeholder : Ed25519Signature)
    (handler : QueryImpl TypedSpec (StateT S (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec))) :
    QueryImpl TypedSpec (StateT (S × Mode) (OracleComp Spec)) := fun query before => do
  let result ← (simulateQ (implementation selected placeholder) ((handler query).run before.1)).run (enter position query before.2)
  pure (result.1.1, (result.1.2, result.2))

/-- Public ordinary callbacks cannot accidentally retain the previous bundle's hidden-address routing. -/
theorem enter_inactive (position : Nat) (query : TypedSpec.Domain) (before : Mode) :
    (enter position query before).active = false := by
  cases query with
  | inl query => rfl
  | inr query => cases query <;> rfl

/-- A fixed selected message remains the same through every later source signing request, including aliases and other identities. -/
theorem prepare_selected (selected handle : Nat) (message target : Pqxdh.Bytes)
    (before : Mode) (held : before.target = some target) :
    (prepare selected handle message).run before = pure
      ((), if handle = selected ∧ RegistrationNativeIdentitySigningRole.oneTime message then
        { before with active := before.target == some message } else before) := by
  by_cases eligible : handle = selected ∧ RegistrationNativeIdentitySigningRole.oneTime message
  · simp [prepare, StateT.run, eligible, held]
  · simp [prepare, StateT.run, eligible]

/-- Repeated target-message requests issue no primitive signing call and return exactly the same client placeholder. -/
theorem repeated (selected : Nat) (placeholder : Ed25519Signature) (message : Pqxdh.Bytes)
    (before : Mode) (held : before.target = some message) :
    (signing selected placeholder selected message).run before = pure
      (some placeholder, if RegistrationNativeIdentitySigningRole.oneTime message then
        { before with active := true } else before) := by
  rw [signing, StateT.run_bind, prepare_selected selected selected message message before held]
  by_cases tagged : RegistrationNativeIdentitySigningRole.oneTime message = true
  · simp [tagged, held]
  · simp [tagged, held]

/-- Public hashes always retain their literal address outside the currently selected source publication suffix. -/
theorem hash_public (before : Mode) (inactive : before.active = false) (bytes : Pqxdh.Bytes) :
    (hashInput before bytes).input = some bytes := by
  simp only [hashInput, inactive, Bool.false_eq_true, ite_false]

/-- An arbitrary 1952-byte public query stays an ordinary known-address hash even inside the selected callback; this does not model a Beacon fingerprint stage. -/
theorem hash_fingerprint (before : Mode) (bytes : Pqxdh.Bytes) (width : bytes.length = 1952) :
    (hashInput before bytes).input = some bytes := by
  cases active : before.active <;> simp [hashInput, active, RegistrationNativeIdentityHashRoute.route, width]

/-- The token decision uses only current-callback control and the public source-fixed input width. -/
theorem hash_token_iff (before : Mode) (bytes : Pqxdh.Bytes) :
    (hashInput before bytes).input = none ↔ before.active = true ∧ bytes.length = 3543 := by
  cases active : before.active <;> simp [hashInput, active, RegistrationNativeIdentityHashRoute.route]

/-- A source OneTimeKey request passes precisely this proxy's executable role test. -/
theorem source_one_time (pending : beaconcrypt_core.registration.BeaconEd25519Signing)
    (tagged : RegistrationNativeIdentitySigningRole.Tagged pending.state.started)
    (stage : pending.stage = .OneTimeKey) :
    ∃ request, pending.request = .ok request ∧
      RegistrationNativeIdentitySigningRole.oneTime (TranscriptAuthParts.absSlice request.message) = true := by
  obtain ⟨request, requested, role⟩ := RegistrationNativeIdentitySigningRole.request pending tagged
  exact ⟨request, requested, by simpa only [stage, RegistrationNativeIdentitySigningRole.slot] using role⟩

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCompiler
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCompiler.enter_inactive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCompiler.enter_inactive
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCompiler.prepare_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCompiler.prepare_selected
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCompiler.repeated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCompiler.repeated
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCompiler.hash_public' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCompiler.hash_public
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCompiler.hash_fingerprint' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCompiler.hash_fingerprint
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCompiler.hash_token_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCompiler.hash_token_iff
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCompiler.source_one_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorCompiler.source_one_time
