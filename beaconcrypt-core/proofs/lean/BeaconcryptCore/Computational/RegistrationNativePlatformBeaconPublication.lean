-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconInitExecutor

/-! The actual Beacon Core publication controller sequences effectful encoding at its literal Ready stage. Crypto requests and Core resume/publish functions are unchanged. Encoding may retain arbitrary shared platform state on None, fail or div; pure compatibility is proved separately. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublication
open RegistrationBeaconInitExecutor (Spec Result edRank ed_rank)
open BeaconcryptCore.Refinement.RegistrationInputs (hashBytes)
variable {Encoded : Type} {m : Type → Type} [Monad m]

def continueWith {Input : Type} (action : RustM Input) (next : Input → m (RustM (Result Encoded))) : m (RustM (Result Encoded)) :=
  match action with
  | .ok value => next value
  | .fail error => pure (.fail error)
  | .div => pure .div

def ready (encode : registration.SignedInitView → m (RustM (core.option.Option Encoded)))
    (pending : registration.BeaconInitReady) : m (RustM (Result Encoded)) :=
  continueWith pending.message fun view => do
    let encoded ← encode view
    pure (do let value ← encoded; pending.publish value)

def fromSigning (impl : QueryImpl Spec m)
    (encode : registration.SignedInitView → m (RustM (core.option.Option Encoded)))
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.BeaconMldsaSigning) : m (RustM (Result Encoded)) :=
  continueWith pending.request fun request => do
    let signature ← impl (.inl (.sign request payload digest))
    continueWith (pending.resume signature) fun effect =>
      match effect with
      | .Rejected previous => pure (.ok (.Err previous))
      | .Ready selected => ready encode selected
      | _ => pure .div

def fromHash (impl : QueryImpl Spec m)
    (encode : registration.SignedInitView → m (RustM (core.option.Option Encoded)))
    (pending : registration.BeaconInitHash) : m (RustM (Result Encoded)) :=
  continueWith pending.request fun request => do
    let digest ← impl (.inl (.hash request))
    continueWith (pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest))) fun effect =>
      match effect with
      | .Rejected previous => pure (.ok (.Err previous))
      | .MldsaSigningRequested selected => fromSigning impl encode ⟨.beacon, hashBytes request⟩ digest selected
      | _ => pure .div

def fromFingerprint (impl : QueryImpl Spec m)
    (encode : registration.SignedInitView → m (RustM (core.option.Option Encoded)))
    (pending : registration.BeaconFingerprint) : m (RustM (Result Encoded)) :=
  continueWith pending.request fun request => do
    let digest ← impl (.inl (.hash request))
    continueWith (pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest))) fun effect =>
      match effect with
      | .Rejected previous => pure (.ok (.Err previous))
      | .HashRequested selected => fromHash impl encode selected
      | _ => pure .div

def fromEd (impl : QueryImpl Spec m)
    (encode : registration.SignedInitView → m (RustM (core.option.Option Encoded)))
    (pending : registration.BeaconEd25519Signing) : m (RustM (Result Encoded)) :=
  continueWith pending.request fun request => do
    let reply ← impl (.inr request)
    match _actual : pending.resume reply with
    | .ok (.Rejected previous) => pure (.ok (.Err previous))
    | .ok (.Ed25519SigningRequested next) => fromEd impl encode next
    | .ok (.FingerprintRequested selected) => fromFingerprint impl encode selected
    | .ok _ => pure .div
    | .fail error => pure (.fail error)
    | .div => pure .div
termination_by edRank pending
decreasing_by exact ed_rank pending reply next _actual

def begin (impl : QueryImpl Spec m)
    (encode : registration.SignedInitView → m (RustM (core.option.Option Encoded)))
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array Std.U8 1952#usize) : m (RustM (Result Encoded)) :=
  continueWith (registration.begin_beacon_init control inputs coins pin mldsa) fun effect =>
    match effect with
    | .Rejected previous => pure (.ok (.Err previous))
    | .Ed25519SigningRequested selected => fromEd impl encode selected
    | _ => pure .div

attribute [local irreducible] registration.BeaconInitHash.resume registration.BeaconFingerprint.resume
  registration.BeaconMldsaSigning.resume registration.BeaconEd25519Signing.resume

private theorem continueWith_same {Input : Type} (action : RustM Input)
    (left right : Input → OracleComp Spec (RustM (Result Encoded)))
    (same : ∀ value, left value = right value) :
    continueWith action left = RegistrationBeaconInitExecutor.continueWith action right := by
  cases action <;> simp only [continueWith, RegistrationBeaconInitExecutor.continueWith, same]

/-- The actual Ready stage passes its signed view to encoding exactly once, and propagates every writer outcome before source publication. -/
theorem ready_run {State : Type}
    (encode : registration.SignedInitView → StateT State m (RustM (core.option.Option Encoded)))
    (pending : registration.BeaconInitReady) (before : State) :
    (ready encode pending).run before =
      match pending.message with
      | .ok view => do
          let result ← (encode view).run before
          pure ((do let value ← result.1; pending.publish value), result.2)
      | .fail error => pure (.fail error, before)
      | .div => pure (.div, before) := by
  cases message : pending.message <;>
    simp only [ready, continueWith, message, StateT.run_bind, StateT.run_pure]

/-- A pure encoder is recovered as a checked compatibility case of the stateful Ready semantics. -/
theorem ready_pure (encode : registration.SignedInitView → core.option.Option Encoded)
    (pending : registration.BeaconInitReady) :
    ready (m := OracleComp Spec) (fun view => pure (.ok (encode view))) pending =
      RegistrationBeaconInitExecutor.ready encode pending := by
  cases message : pending.message <;>
    simp only [ready, continueWith, RegistrationBeaconInitExecutor.ready,
      RegistrationBeaconInitExecutor.continueWith, message, pure_bind]
  rfl

theorem signing_pure (encode : registration.SignedInitView → core.option.Option Encoded)
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.BeaconMldsaSigning) :
    fromSigning (m := OracleComp Spec) (fun query => Spec.query query)
      (fun view => pure (.ok (encode view))) payload digest pending =
      RegistrationBeaconInitExecutor.fromSigning encode payload digest pending := by
  unfold fromSigning RegistrationBeaconInitExecutor.fromSigning
  apply continueWith_same
  intro request
  apply bind_congr
  intro signature
  apply continueWith_same
  intro effect
  cases effect <;> first | exact ready_pure encode _ | rfl

theorem hash_pure (encode : registration.SignedInitView → core.option.Option Encoded)
    (pending : registration.BeaconInitHash) :
    fromHash (m := OracleComp Spec) (fun query => Spec.query query)
      (fun view => pure (.ok (encode view))) pending =
      RegistrationBeaconInitExecutor.fromHash encode pending := by
  unfold fromHash RegistrationBeaconInitExecutor.fromHash
  apply continueWith_same
  intro request
  apply bind_congr
  intro digest
  apply continueWith_same
  intro effect
  cases effect <;> first | exact signing_pure encode _ _ _ | rfl

theorem fingerprint_pure (encode : registration.SignedInitView → core.option.Option Encoded)
    (pending : registration.BeaconFingerprint) :
    fromFingerprint (m := OracleComp Spec) (fun query => Spec.query query)
      (fun view => pure (.ok (encode view))) pending =
      RegistrationBeaconInitExecutor.fromFingerprint encode pending := by
  unfold fromFingerprint RegistrationBeaconInitExecutor.fromFingerprint
  apply continueWith_same
  intro request
  apply bind_congr
  intro digest
  apply continueWith_same
  intro effect
  cases effect <;> first | exact hash_pure encode _ | rfl

theorem ed_pure (encode : registration.SignedInitView → core.option.Option Encoded)
    (pending : registration.BeaconEd25519Signing) :
    fromEd (m := OracleComp Spec) (fun query => Spec.query query)
      (fun view => pure (.ok (encode view))) pending =
      RegistrationBeaconInitExecutor.fromEd encode pending := by
  rw [fromEd.eq_def, RegistrationBeaconInitExecutor.fromEd.eq_def]
  apply continueWith_same
  intro request
  apply bind_congr
  intro reply
  cases resumed : pending.resume reply with
  | fail error => rfl
  | div => rfl
  | ok effect =>
      cases effect with
      | Ed25519SigningRequested next =>
          exact ed_pure encode next
      | FingerprintRequested next => exact fingerprint_pure encode next
      | _ => rfl
termination_by edRank pending
decreasing_by exact ed_rank pending reply next resumed

theorem begin_pure (encode : registration.SignedInitView → core.option.Option Encoded)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array Std.U8 1952#usize) :
    begin (m := OracleComp Spec) (fun query => Spec.query query)
      (fun view => pure (.ok (encode view))) control inputs coins pin mldsa =
      RegistrationBeaconInitExecutor.begin encode control inputs coins pin mldsa := by
  unfold begin RegistrationBeaconInitExecutor.begin
  apply continueWith_same
  intro effect
  cases effect <;> first | exact ed_pure encode _ | rfl

private theorem continueWith_interpret {ι : Type} {base : OracleSpec ι}
    (implementation : QueryImpl base m) {Input : Type} (action : RustM Input)
    (next : Input → OracleComp base (RustM (Result Encoded))) :
    simulateQ implementation (continueWith action next) =
      continueWith action (fun value => simulateQ implementation (next value)) := by
  cases action <;> rfl

variable [LawfulMonad m]

theorem ready_interpret {ι : Type} {base : OracleSpec ι}
    (implementation : QueryImpl base m)
    (encode : registration.SignedInitView → OracleComp base (RustM (core.option.Option Encoded)))
    (pending : registration.BeaconInitReady) :
    simulateQ implementation (ready encode pending) =
      ready (fun view => simulateQ implementation (encode view)) pending := by
  cases message : pending.message <;>
    simp only [ready, continueWith, message, simulateQ_bind, simulateQ_pure]

theorem signing_interpret {ι : Type} {base : OracleSpec ι}
    (implementation : QueryImpl base m) (impl : QueryImpl Spec (OracleComp base))
    (encode : registration.SignedInitView → OracleComp base (RustM (core.option.Option Encoded)))
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.BeaconMldsaSigning) :
    simulateQ implementation (fromSigning impl encode payload digest pending) =
      fromSigning (fun query => simulateQ implementation (impl query))
        (fun view => simulateQ implementation (encode view)) payload digest pending := by
  unfold fromSigning
  rw [continueWith_interpret]
  apply congrArg (continueWith pending.request)
  funext request
  rw [simulateQ_bind]
  apply bind_congr
  intro signature
  rw [continueWith_interpret]
  apply congrArg (continueWith (pending.resume signature))
  funext effect
  cases effect <;> simp only [simulateQ_pure, ready_interpret]

theorem hash_interpret {ι : Type} {base : OracleSpec ι}
    (implementation : QueryImpl base m) (impl : QueryImpl Spec (OracleComp base))
    (encode : registration.SignedInitView → OracleComp base (RustM (core.option.Option Encoded)))
    (pending : registration.BeaconInitHash) :
    simulateQ implementation (fromHash impl encode pending) =
      fromHash (fun query => simulateQ implementation (impl query))
        (fun view => simulateQ implementation (encode view)) pending := by
  unfold fromHash
  rw [continueWith_interpret]
  apply congrArg (continueWith pending.request)
  funext request
  rw [simulateQ_bind]
  apply bind_congr
  intro digest
  rw [continueWith_interpret]
  apply congrArg (continueWith (pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest))))
  funext effect
  cases effect <;> simp only [simulateQ_pure, signing_interpret]

theorem fingerprint_interpret {ι : Type} {base : OracleSpec ι}
    (implementation : QueryImpl base m) (impl : QueryImpl Spec (OracleComp base))
    (encode : registration.SignedInitView → OracleComp base (RustM (core.option.Option Encoded)))
    (pending : registration.BeaconFingerprint) :
    simulateQ implementation (fromFingerprint impl encode pending) =
      fromFingerprint (fun query => simulateQ implementation (impl query))
        (fun view => simulateQ implementation (encode view)) pending := by
  unfold fromFingerprint
  rw [continueWith_interpret]
  apply congrArg (continueWith pending.request)
  funext request
  rw [simulateQ_bind]
  apply bind_congr
  intro digest
  rw [continueWith_interpret]
  apply congrArg (continueWith (pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest))))
  funext effect
  cases effect <;> simp only [simulateQ_pure, hash_interpret]

theorem ed_interpret {ι : Type} {base : OracleSpec ι}
    (implementation : QueryImpl base m) (impl : QueryImpl Spec (OracleComp base))
    (encode : registration.SignedInitView → OracleComp base (RustM (core.option.Option Encoded)))
    (pending : registration.BeaconEd25519Signing) :
    simulateQ implementation (fromEd impl encode pending) =
      fromEd (fun query => simulateQ implementation (impl query))
        (fun view => simulateQ implementation (encode view)) pending := by
  rw [fromEd.eq_def, fromEd.eq_def]
  rw [continueWith_interpret]
  apply congrArg (continueWith pending.request)
  funext request
  rw [simulateQ_bind]
  apply bind_congr
  intro reply
  cases resumed : pending.resume reply with
  | fail error => exact simulateQ_pure _ _
  | div => exact simulateQ_pure _ _
  | ok effect =>
      cases effect with
      | Ed25519SigningRequested next => exact ed_interpret implementation impl encode next
      | FingerprintRequested next => exact fingerprint_interpret implementation impl encode next
      | _ => exact simulateQ_pure _ _
termination_by edRank pending
decreasing_by exact ed_rank pending reply next resumed

theorem begin_interpret {ι : Type} {base : OracleSpec ι}
    (implementation : QueryImpl base m) (impl : QueryImpl Spec (OracleComp base))
    (encode : registration.SignedInitView → OracleComp base (RustM (core.option.Option Encoded)))
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array Std.U8 1952#usize) :
    simulateQ implementation (begin impl encode control inputs coins pin mldsa) =
      begin (fun query => simulateQ implementation (impl query))
        (fun view => simulateQ implementation (encode view)) control inputs coins pin mldsa := by
  unfold begin
  rw [continueWith_interpret]
  apply congrArg (continueWith (registration.begin_beacon_init control inputs coins pin mldsa))
  funext effect
  cases effect <;> simp only [simulateQ_pure, ed_interpret]
end BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublication.ready_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublication.ready_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublication.ready_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublication.ready_pure
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublication.signing_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublication.signing_pure
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublication.hash_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublication.hash_pure
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublication.fingerprint_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublication.fingerprint_pure
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublication.ed_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublication.ed_pure
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublication.begin_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublication.begin_pure
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublication.ready_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublication.ready_interpret
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublication.signing_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublication.signing_interpret
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublication.hash_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublication.hash_interpret
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublication.fingerprint_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublication.fingerprint_interpret
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublication.ed_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublication.ed_interpret
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublication.begin_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublication.begin_interpret
