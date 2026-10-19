import BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds

/-!
Private Phase2 requests retain an opaque decapsulation result before the original ordered DH callbacks. The pending root carries those actual DH values and the opaque shared-secret handle; it never publishes a byte realization or a dummy root. Core control and associated data depend only on the original identity and DH checks. The same native tail starts after the private root callback, where the actual candidate root bytes have already been cleared.

A fixed handle interpretation appears only in the mathematical realization law. It is not available to a public adversary or a selected-key reduction. Concrete challenge routing and cryptographic bounds remain separate; the interface must preserve the full callback state and every optional rejection. The typed codec, native primitive and physical erasure contracts from the original Phase2 adapter remain explicit. Only live state and its authorized compromise interfaces are in scope; storage, snapshots and restoration are excluded.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open BeaconcryptCore.Refinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared
open PqxdhBeaconPhase2Preparation (Bytes Word32 Ciphertext State)
open PqxdhRefinement

structure Secrets (Shared : Type) where
  dh1 : Word32
  dh2 : Word32
  dh3 : Word32
  dh4 : Word32
  shared : Shared

def concreteSecrets {Shared : Type} (interpret : Shared → Word32) (secrets : Secrets Shared) :
    pqxdh.PqxdhSharedSecrets :=
  ⟨secrets.dh1, secrets.dh2, secrets.dh3, secrets.dh4, interpret secrets.shared⟩

structure Inputs (Response Shared : Type) where
  response : Response
  ciphertext : Ciphertext
  ephemeral : Word32
  serverIdentity : Word32
  assigned : Std.U64
  secrets : Secrets Shared

def concreteInputs {Response Shared : Type} (interpret : Shared → Word32) (inputs : Inputs Response Shared) :
    PqxdhBeaconPhase2Preparation.Inputs Response :=
  ⟨inputs.response, inputs.ciphertext, inputs.ephemeral,
    ⟨inputs.serverIdentity, inputs.assigned, concreteSecrets interpret inputs.secrets⟩⟩

/-- This private metadata contains no root bytes or shared-secret realization. -/
structure Metadata where
  binding : pqxdh.ServerBinding
  assigned : Std.U64
  associatedData : Std.Array Std.U8 153#usize

def candidateMetadata (candidate : pqxdh.BeaconRegistrationCandidate) : Metadata :=
  ⟨candidate.server_binding, candidate.assigned_key_id, candidate.associated_data⟩

def optionalMetadata (result : core.result.Result pqxdh.BeaconRegistrationCandidate pqxdh.RegistrationError) : Option Metadata :=
  match result with
  | .Err _ => none
  | .Ok candidate => some (candidateMetadata candidate)

noncomputable def associatedData (control : pqxdh.BeaconInitSent) : Std.Array Std.U8 153#usize :=
  (BeaconcryptCore.PanicFreedom.build_associated_data_ok control.expected_server_binding.identity_public_key
    control.beacon_identity_public_key).choose

def nonzero {Shared : Type} (secrets : Secrets Shared) : Prop :=
  Pqxdh.dhNonZero (absBytes secrets.dh1, absBytes secrets.dh2, absBytes secrets.dh3, absBytes secrets.dh4)

noncomputable def admitted {Response Shared : Type} (control : pqxdh.BeaconInitSent)
    (inputs : Inputs Response Shared) : Option Metadata := by
  classical
  exact if absBytes control.expected_server_binding.identity_public_key = absBytes inputs.serverIdentity then
    if nonzero inputs.secrets then
      some ⟨control.expected_server_binding, inputs.assigned, associatedData control⟩
    else none
  else none

/-- Actual core acceptance and metadata depend on identity and the four DH values, independently of the opaque shared-secret interpretation. -/
theorem admitted_exact {Response Shared : Type} (interpret : Shared → Word32)
    (control : pqxdh.BeaconInitSent) (inputs : Inputs Response Shared) :
    optionalMetadata (PqxdhBeaconPhase2Preparation.normalPrepare control (concreteInputs interpret inputs).finishInputs) =
      admitted control inputs := by
  classical
  have actual := PqxdhBeaconPhase2Preparation.normalPrepare_exact control (concreteInputs interpret inputs).finishInputs
  by_cases identity : absBytes control.expected_server_binding.identity_public_key = absBytes inputs.serverIdentity
  · by_cases dh : nonzero inputs.secrets
    · obtain ⟨root, rootEq, _⟩ := (build_root_key_input_abs (concreteSecrets interpret inputs.secrets)).1 dh
      have adEq : pqxdh.build_associated_data control.expected_server_binding.identity_public_key
          control.beacon_identity_public_key = ok (associatedData control) :=
        (BeaconcryptCore.PanicFreedom.build_associated_data_ok _ _).choose_spec
      simp [concreteInputs, pqxdh.beacon_prepare_finish, array_eq_abs, identity, rootEq, adEq] at actual
      simp only [concreteInputs, ← actual, optionalMetadata, candidateMetadata, admitted, identity, dh, ite_true]
    · have rootEq := (build_root_key_input_abs (concreteSecrets interpret inputs.secrets)).2 dh
      simp [concreteInputs, pqxdh.beacon_prepare_finish, array_eq_abs, identity, rootEq] at actual
      simp only [concreteInputs, ← actual, optionalMetadata, admitted, identity, dh, ite_true, ite_false]
  · simp [concreteInputs, pqxdh.beacon_prepare_finish, array_eq_abs, identity] at actual
    simp only [concreteInputs, ← actual, optionalMetadata, admitted, identity, ite_false]

/-- Only the decapsulation reply and temporary-secret erasure carry opaque shared values; all original request arguments are retained. -/
inductive Query (I D K X Response Shared : Type) where
  | decode : Bytes → Query I D K X Response Shared
  | ciphertext : Response → Query I D K X Response Shared
  | ephemeral : Response → Query I D K X Response Shared
  | serverIdentity : Response → Query I D K X Response Shared
  | publicConversion : Word32 → Query I D K X Response Shared
  | privateConversion : I → Query I D K X Response Shared
  | decapsulate : Ciphertext → K → Query I D K X Response Shared
  | dhPair : D → Word32 → Query I D K X Response Shared
  | dhIdentity : X → Word32 → Query I D K X Response Shared
  | assignedId : Response → Query I D K X Response Shared
  | eraseShared : Secrets Shared → Query I D K X Response Shared

abbrev Spec (I D K X Response Shared : Type) : OracleSpec (Query I D K X Response Shared)
  | .decode _ => Option Response
  | .ciphertext _ => Option Ciphertext
  | .ephemeral _ | .serverIdentity _ | .publicConversion _ => Option Word32
  | .privateConversion _ => Option X
  | .decapsulate _ _ => Option Shared
  | .dhPair _ _ | .dhIdentity _ _ => Option Word32
  | .assignedId _ => Std.U64
  | .eraseShared _ => Unit

/-- Opaque decapsulation still happens before each of the original four DH calls and the final assigned-ID getter. -/
def collect {I D K X Response Shared : Type} (identity : I) (prekey oneTime : D) (kem : K) (raw : Bytes) :
    OracleComp (Spec I D K X Response Shared) (Option (Inputs Response Shared)) := OptionT.run do
  let response ← OptionT.mk ((Spec I D K X Response Shared).query (.decode raw))
  let ciphertext ← OptionT.mk ((Spec I D K X Response Shared).query (.ciphertext response))
  let ephemeral ← OptionT.mk ((Spec I D K X Response Shared).query (.ephemeral response))
  let server ← OptionT.mk ((Spec I D K X Response Shared).query (.serverIdentity response))
  let serverConverted ← OptionT.mk ((Spec I D K X Response Shared).query (.publicConversion server))
  let identityConverted ← OptionT.mk ((Spec I D K X Response Shared).query (.privateConversion identity))
  let shared ← OptionT.mk ((Spec I D K X Response Shared).query (.decapsulate ciphertext kem))
  let dh1 ← OptionT.mk ((Spec I D K X Response Shared).query (.dhPair prekey serverConverted))
  let dh2 ← OptionT.mk ((Spec I D K X Response Shared).query (.dhIdentity identityConverted ephemeral))
  let dh3 ← OptionT.mk ((Spec I D K X Response Shared).query (.dhPair prekey ephemeral))
  let dh4 ← OptionT.mk ((Spec I D K X Response Shared).query (.dhPair oneTime ephemeral))
  let assigned ← liftM ((Spec I D K X Response Shared).query (.assignedId response))
  pure ⟨response, ciphertext, ephemeral, server, assigned, ⟨dh1, dh2, dh3, dh4, shared⟩⟩

/-- These local operational equations include all callback effects; the handle interpretation is private mathematical context. -/
structure Calls {I D K X Response Shared : Type} {m : Type → Type} [Monad m]
    (interpret : Shared → Word32)
    (native : QueryImpl (PqxdhBeaconPhase2Preparation.Spec I D K X Response) m)
    (handles : QueryImpl (Spec I D K X Response Shared) m) : Prop where
  decode : ∀ raw, native (.decode raw) = handles (.decode raw)
  ciphertext : ∀ response, native (.ciphertext response) = handles (.ciphertext response)
  ephemeral : ∀ response, native (.ephemeral response) = handles (.ephemeral response)
  serverIdentity : ∀ response, native (.serverIdentity response) = handles (.serverIdentity response)
  publicConversion : ∀ value, native (.publicConversion value) = handles (.publicConversion value)
  privateConversion : ∀ identity, native (.privateConversion identity) = handles (.privateConversion identity)
  decapsulate : ∀ ciphertext kem, native (.decapsulate ciphertext kem) = Option.map interpret <$> handles (.decapsulate ciphertext kem)
  dhPair : ∀ pair publicValue, native (.dhPair pair publicValue) = handles (.dhPair pair publicValue)
  dhIdentity : ∀ identity publicValue, native (.dhIdentity identity publicValue) = handles (.dhIdentity identity publicValue)
  assignedId : ∀ response, native (.assignedId response) = handles (.assignedId response)
  eraseShared : ∀ secrets, native (.eraseShared (concreteSecrets interpret secrets)) = handles (.eraseShared secrets)

/-- The original complete optional collection is realized without moving decapsulation or any later DH effect. -/
theorem collect_realization {I D K X Response Shared : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (interpret : Shared → Word32)
    (native : QueryImpl (PqxdhBeaconPhase2Preparation.Spec I D K X Response) m)
    (handles : QueryImpl (Spec I D K X Response Shared) m) (calls : Calls interpret native handles)
    (identity : I) (prekey oneTime : D) (kem : K) (raw : Bytes) :
    simulateQ native (PqxdhBeaconPhase2Preparation.collect identity prekey oneTime kem raw) =
      Option.map (concreteInputs interpret) <$> simulateQ handles (collect identity prekey oneTime kem raw) := by
  simp only [PqxdhBeaconPhase2Preparation.collect, collect, OptionT.run_bind, OptionT.run_mk,
    OptionT.run_pure, OptionT.run_monadLift, Option.elimM, bind_map_left,
    simulateQ_bind, simulateQ_spec_query]
  simp only [calls.decode, map_bind]
  congr 1
  funext response
  cases response <;> simp only [Option.elim_none, Option.elim_some, simulateQ_pure, map_pure, Option.map_none]
  repeat' (
    simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, map_bind, map_pure,
      bind_map_left, calls.ciphertext, calls.ephemeral, calls.serverIdentity, calls.publicConversion,
      calls.privateConversion, calls.decapsulate, calls.dhPair, calls.dhIdentity, calls.assignedId,
      Option.elim_none, Option.elim_some, Option.map_none, Option.map_some]
    first | rfl | (congr 1; funext reply; cases reply))
  all_goals simp only [Option.elim, simulateQ_pure, map_pure, Option.map]

/-- Pending root coordinates denote the copied root-input component, which survives erasure of the temporary shared outputs. -/
structure Prepared (Response Shared : Type) where
  response : Response
  ciphertext : Ciphertext
  ephemeral : Word32
  metadata : Metadata
  root : Secrets Shared

/-- No native root bytes occur in the pending public-free handle representation. -/
def prepared {Response Shared : Type} (inputs : Inputs Response Shared) (metadata : Metadata) : Prepared Response Shared :=
  ⟨inputs.response, inputs.ciphertext, inputs.ephemeral, metadata, inputs.secrets⟩

/-- The realization relation includes the actual extracted full root-input construction, not merely its metadata. -/
def ReadyRel {Response Shared : Type} (interpret : Shared → Word32)
    (native : PqxdhBeaconPhase2Preparation.Prepared Response) (handles : Prepared Response Shared) : Prop :=
  native.response = handles.response ∧ native.ciphertext = handles.ciphertext ∧ native.ephemeral = handles.ephemeral ∧
    candidateMetadata native.candidate = handles.metadata ∧
    pqxdh.build_root_key_input (concreteSecrets interpret handles.root) = ok (.Ok native.candidate.root_key_input)

/-- The actual successful core result internally supplies the full pending-root relation. -/
theorem prepared_related {Response Shared : Type} (interpret : Shared → Word32)
    (control : pqxdh.BeaconInitSent) (inputs : Inputs Response Shared) (candidate : pqxdh.BeaconRegistrationCandidate)
    (actual : PqxdhBeaconPhase2Preparation.normalPrepare control (concreteInputs interpret inputs).finishInputs = .Ok candidate) :
    ReadyRel interpret ⟨inputs.response, inputs.ciphertext, inputs.ephemeral, candidate⟩
      (prepared inputs (candidateMetadata candidate)) := by
  have shape := PqxdhSurface.beacon_prepare_finish_success_shape control (concreteInputs interpret inputs).finishInputs
    candidate ((PqxdhBeaconPhase2Preparation.normalPrepare_exact _ _).trans (congrArg ok actual))
  exact ⟨rfl, rfl, rfl, rfl, shape.2.2.2.1⟩

/-- The original admission runs before temporary-secret erasure on either outcome; only copied root coordinates enter the continuation. -/
noncomputable def afterInputs {I D K X Response Shared : Type} (control : pqxdh.BeaconInitSent)
    (inputs : Inputs Response Shared) : OracleComp (Spec I D K X Response Shared) (Option (Prepared Response Shared)) := do
  let metadata := admitted control inputs
  let _ ← (Spec I D K X Response Shared).query (.eraseShared inputs.secrets)
  pure (metadata.map (prepared inputs))

noncomputable def prepare {I D K X Response Shared : Type} (control : pqxdh.BeaconInitSent)
    (identity : I) (prekey oneTime : D) (kem : K) (raw : Bytes) :
    OracleComp (Spec I D K X Response Shared) (Option (Prepared Response Shared)) := do
  let inputs ← collect identity prekey oneTime kem raw
  match inputs with
  | none => pure none
  | some inputs => afterInputs control inputs

/-- Both optional preparation outcomes continue from the same erasure poststate; success supplies the derived full root relation. -/
theorem afterInputs_continuation {I D K X Response Shared Result : Type} {m : Type → Type}
    [Monad m] [LawfulMonad m] (interpret : Shared → Word32)
    (native : QueryImpl (PqxdhBeaconPhase2Preparation.Spec I D K X Response) m)
    (handles : QueryImpl (Spec I D K X Response Shared) m) (calls : Calls interpret native handles)
    (control : pqxdh.BeaconInitSent) (inputs : Inputs Response Shared)
    (nextNative : Option (PqxdhBeaconPhase2Preparation.Prepared Response) → m Result)
    (nextHandles : Option (Prepared Response Shared) → m Result)
    (rejected : nextNative none = nextHandles none)
    (accepted : ∀ original pending, ReadyRel interpret original pending → nextNative (some original) = nextHandles (some pending)) :
    (simulateQ native (PqxdhBeaconPhase2Preparation.afterInputs control (concreteInputs interpret inputs)) >>= nextNative) =
      (simulateQ handles (afterInputs control inputs) >>= nextHandles) := by
  simp only [PqxdhBeaconPhase2Preparation.afterInputs, afterInputs, simulateQ_bind,
    simulateQ_spec_query, simulateQ_pure, bind_assoc, pure_bind, concreteInputs]
  rw [calls.eraseShared]
  apply bind_congr
  intro erased
  have metadataEq := (admitted_exact interpret control inputs).symm
  cases actual : PqxdhBeaconPhase2Preparation.normalPrepare control (concreteInputs interpret inputs).finishInputs with
  | Err error =>
      simp only [actual, optionalMetadata] at metadataEq
      simp only [concreteInputs] at actual
      simpa only [actual, metadataEq, Option.map_none] using rejected
  | Ok candidate =>
      have related := prepared_related interpret control inputs candidate actual
      simp only [actual, optionalMetadata] at metadataEq
      simp only [concreteInputs] at actual
      simpa only [actual, metadataEq, Option.map_some] using accepted _ _ related

/-- The complete original pre-root program has the same arbitrary private continuation, with all optional failures and copied root coordinates retained. -/
theorem prepare_continuation {I D K X Response Shared Result : Type} {m : Type → Type}
    [Monad m] [LawfulMonad m] (interpret : Shared → Word32)
    (native : QueryImpl (PqxdhBeaconPhase2Preparation.Spec I D K X Response) m)
    (handles : QueryImpl (Spec I D K X Response Shared) m) (calls : Calls interpret native handles)
    (control : pqxdh.BeaconInitSent) (identity : I) (prekey oneTime : D) (kem : K) (raw : Bytes)
    (nextNative : Option (PqxdhBeaconPhase2Preparation.Prepared Response) → m Result)
    (nextHandles : Option (Prepared Response Shared) → m Result)
    (rejected : nextNative none = nextHandles none)
    (accepted : ∀ original pending, ReadyRel interpret original pending → nextNative (some original) = nextHandles (some pending)) :
    (simulateQ native (PqxdhBeaconPhase2Preparation.prepare control identity prekey oneTime kem raw) >>= nextNative) =
      (simulateQ handles (prepare control identity prekey oneTime kem raw) >>= nextHandles) := by
  simp only [PqxdhBeaconPhase2Preparation.prepare, prepare, simulateQ_bind, bind_assoc]
  rw [collect_realization interpret native handles calls, bind_map_left]
  apply bind_congr
  intro inputs
  cases inputs with
  | none => simpa only [Option.map_none, simulateQ_pure, pure_bind] using rejected
  | some inputs =>
      simpa only [Option.map_some] using
        afterInputs_continuation interpret native handles calls control inputs nextNative nextHandles rejected accepted

/-- This is the actual candidate representation after root-input clearing, containing no opaque handle or recovered shared bytes. -/
def clearedMetadata (metadata : Metadata) : pqxdh.BeaconRegistrationCandidate :=
  ⟨metadata.binding, metadata.assigned,
    ⟨⟨List.replicate 192 0#u8, by simp only [List.length_replicate]; rfl⟩⟩, metadata.associatedData⟩

/-- Once root processing has finished, the source candidate is exactly the rootless metadata with its original input bytes cleared. -/
theorem cleared_related {Response Shared : Type} (interpret : Shared → Word32)
    (original : PqxdhBeaconPhase2Preparation.Prepared Response) (pending : Prepared Response Shared)
    (related : ReadyRel interpret original pending) :
    PqxdhBeaconPhase2Publication.clearedCandidate original.candidate = clearedMetadata pending.metadata := by
  rw [← related.2.2.2.1]
  rfl

inductive AuxQuery (Response Shared : Type) where
  | root : Secrets Shared → AuxQuery Response Shared
  | initial : SymmetricRatchetKdfRequest → AuxQuery Response Shared
  | application : Response → AuxQuery Response Shared

abbrev AuxSpec (Response Shared : Type) : OracleSpec (AuxQuery Response Shared)
  | .root _ => Option Word32
  | .initial _ => pqxdh.concrete.InitialRatchetKdfResponse
  | .application _ => Option Bytes

abbrev TailSpec (Response Shared : Type) := RawCtxSourceOpen.NativeSpec + AuxSpec Response Shared

def rawLift {Response Shared : Type} : QueryImpl RawCtxSourceOpen.NativeSpec (OracleComp (TailSpec Response Shared)) :=
  fun query => liftM ((TailSpec Response Shared).query (.inl query))

/-- Only after private root processing does the ordinary typed64 initializer run, followed by app access and the unchanged actual native raw opening. -/
noncomputable def afterRoot {Response Shared : Type} (decode : RawCtxReceive.FrameDecoder)
    (pending : Prepared Response Shared) (root : Word32) :
    OracleComp (TailSpec Response Shared) (Option PqxdhBeaconPhase2Publication.Staged) := do
  let response ← (TailSpec Response Shared).query
    (.inr (.initial (PqxdhInitialRatchetComplementarity.beaconPending root).request))
  let kernel := PqxdhBeaconPhase2Publication.normalInitial (PqxdhInitialRatchetComplementarity.beaconPending root) response
  let raw ← (TailSpec Response Shared).query (.inr (.application pending.response))
  match raw with
  | none => pure none
  | some raw => do
      let result ← simulateQ rawLift (simulateQ RawCtxSourceOpen.nativeAdapter
        ((RawCtxWholeOwner.rawReceive decode raw).run (PqxdhBeaconPhase2Publication.localOwner (clearedMetadata pending.metadata) kernel)))
      pure (PqxdhBeaconPhase2Publication.afterOpening (clearedMetadata pending.metadata) result.2.owner.kernel result.1)

/-- The private root callback consumes copied coordinates once, without repeating decapsulation or exposing the opaque shared handle. -/
noncomputable def tail {Response Shared : Type} (decode : RawCtxReceive.FrameDecoder)
    (pending : Prepared Response Shared) : OracleComp (TailSpec Response Shared) (Option PqxdhBeaconPhase2Publication.Staged) := do
  let root ← (TailSpec Response Shared).query (.inr (.root pending.root))
  match root with
  | none => pure none
  | some root => afterRoot decode pending root

/-- The root equation uses the source-derived complete input relation. All other original tail effects and optional outcomes remain exact. -/
structure TailCalls {Response Shared : Type} {m : Type → Type} [Monad m]
    (interpret : Shared → Word32)
    (native : QueryImpl (PqxdhBeaconPhase2Publication.NativeTailSpec Response) m)
    (handles : QueryImpl (TailSpec Response Shared) m) : Prop where
  root : ∀ secrets rootInput, pqxdh.build_root_key_input (concreteSecrets interpret secrets) = ok (.Ok rootInput) →
    native (.inr (.root rootInput)) = handles (.inr (.root secrets))
  initial : ∀ request, native (.inr (.initial request)) = handles (.inr (.initial request))
  application : ∀ response, native (.inr (.application response)) = handles (.inr (.application response))
  raw : ∀ query, native (.inl query) = handles (.inl query)

/-- Every expanded raw callback retains the same full interpreter effect, with no chain or shared-secret inspection added. -/
theorem raw_realization {Response Shared Result : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (interpret : Shared → Word32)
    (native : QueryImpl (PqxdhBeaconPhase2Publication.NativeTailSpec Response) m)
    (handles : QueryImpl (TailSpec Response Shared) m) (calls : TailCalls interpret native handles)
    (client : OracleComp RawCtxSourceOpen.NativeSpec Result) :
    simulateQ native (simulateQ PqxdhBeaconPhase2Publication.nativeRawLift client) =
      simulateQ handles (simulateQ rawLift client) := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  exact (simulateQ_spec_query native (.inl query)).trans
    ((calls.raw query).trans (simulateQ_spec_query handles (.inl query)).symm)

/-- The same root output enters the exact native initializer and all subsequent optional opening effects, before the unchanged sequence and binding gates. -/
theorem afterRoot_realization {Response Shared : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (interpret : Shared → Word32)
    (native : QueryImpl (PqxdhBeaconPhase2Publication.NativeTailSpec Response) m)
    (handles : QueryImpl (TailSpec Response Shared) m) (calls : TailCalls interpret native handles)
    (decode : RawCtxReceive.FrameDecoder)
    (original : PqxdhBeaconPhase2Preparation.Prepared Response) (pending : Prepared Response Shared)
    (related : ReadyRel interpret original pending) (root : Word32) :
    simulateQ native (simulateQ PqxdhBeaconPhase2Publication.nativeTailAdapter
      (PqxdhBeaconPhase2Publication.afterRoot decode original root)) =
      simulateQ handles (afterRoot decode pending root) := by
  have auxiliary (query : PqxdhBeaconPhase2Publication.AuxQuery Response) :
      simulateQ native (PqxdhBeaconPhase2Publication.nativeTailAdapter (.inr query)) = native (.inr query) :=
    simulateQ_spec_query native (.inr query)
  have responseEq : original.response = pending.response := related.1
  have applicationEq : native (.inr (.application original.response)) = handles (.inr (.application pending.response)) := by
    rw [← responseEq]
    exact calls.application _

  unfold PqxdhBeaconPhase2Publication.afterRoot PqxdhBeaconPhase2Publication.initialRun afterRoot
  simp only [bind_assoc, pure_bind, simulateQ_bind, simulateQ_spec_query, auxiliary,
    calls.initial, applicationEq, cleared_related interpret original pending related]
  apply bind_congr
  intro response
  apply bind_congr
  intro raw
  cases raw with
  | none => simp only [simulateQ_pure]
  | some raw =>
      simp only [simulateQ_bind, simulateQ_pure]
      rw [PqxdhBeaconPhase2Bounds.native_raw_lift, raw_realization interpret native handles calls]

/-- The private root call uses the internally derived source coordinates exactly once, then continues with the same optional native tail. -/
theorem tail_realization {Response Shared : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (interpret : Shared → Word32)
    (native : QueryImpl (PqxdhBeaconPhase2Publication.NativeTailSpec Response) m)
    (handles : QueryImpl (TailSpec Response Shared) m) (calls : TailCalls interpret native handles)
    (decode : RawCtxReceive.FrameDecoder)
    (original : PqxdhBeaconPhase2Preparation.Prepared Response) (pending : Prepared Response Shared)
    (related : ReadyRel interpret original pending) :
    simulateQ native (simulateQ PqxdhBeaconPhase2Publication.nativeTailAdapter
      (PqxdhBeaconPhase2Publication.tail decode original)) =
      simulateQ handles (tail decode pending) := by
  have rootEq : simulateQ native (PqxdhBeaconPhase2Publication.nativeTailAdapter
      (.inr (.root original.candidate.root_key_input))) = handles (.inr (.root pending.root)) :=
    (simulateQ_spec_query native (.inr (.root original.candidate.root_key_input))).trans
      (calls.root _ _ related.2.2.2.2)
  simp only [PqxdhBeaconPhase2Publication.tail, tail, simulateQ_bind, simulateQ_spec_query, rootEq]
  apply bind_congr
  intro root
  cases root with
  | none => simp only [simulateQ_pure]
  | some root => exact afterRoot_realization interpret native handles calls decode original pending related root

abbrev FullSpec (I D K X Response Shared : Type) := Spec I D K X Response Shared + TailSpec Response Shared

def preLift {I D K X Response Shared : Type} :
    QueryImpl (Spec I D K X Response Shared) (OracleComp (FullSpec I D K X Response Shared)) :=
  fun query => liftM ((FullSpec I D K X Response Shared).query (.inl query))

def tailLift {I D K X Response Shared : Type} :
    QueryImpl (TailSpec Response Shared) (OracleComp (FullSpec I D K X Response Shared)) :=
  fun query => liftM ((FullSpec I D K X Response Shared).query (.inr query))

/-- The full live owner uses no shared-secret interpretation: preparation derives admission, the private root resolves its opaque value, and only the original native finish publishes or aborts. -/
noncomputable def owner {I D K X Response Shared : Type} (decode : RawCtxReceive.FrameDecoder)
    (raw : Bytes) (state : State I D K) : OracleComp (FullSpec I D K X Response Shared) (Option Bytes × State I D K) :=
  match state.beacon.phase with
  | .initSent control prekey oneTime kem => do
      let prepared ← simulateQ preLift (prepare control state.beacon.identity prekey oneTime kem raw)
      match prepared with
      | none => pure (PqxdhBeaconPhase2Publication.finish control state none)
      | some prepared => do
          let staged ← simulateQ tailLift (tail decode prepared)
          pure (PqxdhBeaconPhase2Publication.finish control state staged)
  | _ => pure (none, state)

/-- All operational obligations refer to the same private effect monad, preserving its complete state across decapsulation, root processing and publication. -/
structure FullCalls {I D K X Response Shared : Type} {m : Type → Type} [Monad m]
    (interpret : Shared → Word32)
    (native : QueryImpl (PqxdhBeaconPhase2Publication.NativeSpec I D K X Response) m)
    (handles : QueryImpl (FullSpec I D K X Response Shared) m) : Prop where
  preparation : Calls interpret (fun query => native (.inl query)) (fun query => handles (.inl query))
  tail : TailCalls interpret (fun query => native (.inr query)) (fun query => handles (.inr query))

/-- The complete original native owner equals its opaque-shared implementation under exact private callback realization, for every lawful monad and every optional failure. -/
theorem owner_realization {I D K X Response Shared : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (interpret : Shared → Word32)
    (native : QueryImpl (PqxdhBeaconPhase2Publication.NativeSpec I D K X Response) m)
    (handles : QueryImpl (FullSpec I D K X Response Shared) m) (calls : FullCalls interpret native handles)
    (decode : RawCtxReceive.FrameDecoder) (raw : Bytes) (state : State I D K) :
    simulateQ native (PqxdhBeaconPhase2Publication.nativeOwner decode raw state) =
      simulateQ handles (owner decode raw state) := by
  have nPre : (native ∘ₛ PqxdhBeaconPhase2Publication.nativeAdapter) ∘ₛ PqxdhBeaconPhase2Publication.preLift =
      fun query => native (.inl query) := by
    funext query
    exact (simulateQ_spec_query (native ∘ₛ PqxdhBeaconPhase2Publication.nativeAdapter) (.inl query)).trans
      (simulateQ_spec_query native (.inl query))
  have nTailLift : native ∘ₛ PqxdhBeaconPhase2Publication.nativeTailLift = fun query => native (.inr query) := by
    funext query
    exact simulateQ_spec_query native (.inr query)
  have nTail : (native ∘ₛ PqxdhBeaconPhase2Publication.nativeAdapter) ∘ₛ PqxdhBeaconPhase2Publication.tailLift =
      (fun query => native (.inr query)) ∘ₛ PqxdhBeaconPhase2Publication.nativeTailAdapter := by
    funext query
    refine (simulateQ_spec_query (native ∘ₛ PqxdhBeaconPhase2Publication.nativeAdapter) (.inr query)).trans ?_
    change simulateQ native (simulateQ PqxdhBeaconPhase2Publication.nativeTailLift
      (PqxdhBeaconPhase2Publication.nativeTailAdapter query)) = _
    rw [← QueryImpl.simulateQ_compose, nTailLift]
    rfl
  have hPre : handles ∘ₛ preLift = fun query => handles (.inl query) := by
    funext query
    exact simulateQ_spec_query handles (.inl query)
  have hTail : handles ∘ₛ tailLift = fun query => handles (.inr query) := by
    funext query
    exact simulateQ_spec_query handles (.inr query)
  unfold PqxdhBeaconPhase2Publication.nativeOwner
  rw [← QueryImpl.simulateQ_compose]
  cases active : state.beacon.phase with
  | initSent control prekey oneTime kem =>
      simp only [PqxdhBeaconPhase2Publication.owner, owner, active, simulateQ_bind,
        ← QueryImpl.simulateQ_compose, nPre, hPre]
      apply prepare_continuation interpret _ _ calls.preparation control state.beacon.identity prekey oneTime kem raw
      · simp only [simulateQ_pure]
      · intro original pending related
        simp only [simulateQ_bind, simulateQ_pure, ← QueryImpl.simulateQ_compose, nTail, hTail]
        rw [QueryImpl.simulateQ_compose]
        exact congrArg (fun (computation : m (Option PqxdhBeaconPhase2Publication.Staged)) =>
          computation >>= fun staged => pure (PqxdhBeaconPhase2Publication.finish control state staged))
          (tail_realization interpret _ _ calls.tail decode original pending related)
  | _ => simp only [PqxdhBeaconPhase2Publication.owner, owner, active, simulateQ_pure]

/-- Any continued experiment retains the same optional API result, complete owner and full private interpreter state. -/
theorem owner_continuation {I D K X Response Shared Auxiliary Result : Type}
    (interpret : Shared → Word32)
    (native : QueryImpl (PqxdhBeaconPhase2Publication.NativeSpec I D K X Response) (StateT Auxiliary ProbComp))
    (handles : QueryImpl (FullSpec I D K X Response Shared) (StateT Auxiliary ProbComp))
    (calls : FullCalls interpret native handles) (decode : RawCtxReceive.FrameDecoder)
    (raw : Bytes) (state : State I D K) (auxiliary : Auxiliary)
    (next : (Option Bytes × State I D K) × Auxiliary → ProbComp Result) :
    (simulateQ native (PqxdhBeaconPhase2Publication.nativeOwner decode raw state)).run auxiliary >>= next =
      (simulateQ handles (owner decode raw state)).run auxiliary >>= next := by
  rw [owner_realization interpret native handles calls]

/-- Exact program equality transfers every underlying selective query budget without discarding callback effects or recomputation work. -/
theorem owner_query_bounds {I D K X Response Shared Auxiliary ι : Type} {spec : OracleSpec ι}
    (interpret : Shared → Word32)
    (native : QueryImpl (PqxdhBeaconPhase2Publication.NativeSpec I D K X Response) (StateT Auxiliary (OracleComp spec)))
    (handles : QueryImpl (FullSpec I D K X Response Shared) (StateT Auxiliary (OracleComp spec)))
    (calls : FullCalls interpret native handles) (decode : RawCtxReceive.FrameDecoder)
    (raw : Bytes) (state : State I D K) (auxiliary : Auxiliary)
    (predicate : spec.Domain → Prop) [DecidablePred predicate] (budget : Nat) :
    ((simulateQ native (PqxdhBeaconPhase2Publication.nativeOwner decode raw state)).run auxiliary).IsQueryBoundP predicate budget ↔
      ((simulateQ handles (owner decode raw state)).run auxiliary).IsQueryBoundP predicate budget := by
  rw [owner_realization interpret native handles calls]

/-- Successful opaque-shared execution derives the original sequence-one gate, binding length and exact native kernel publication from the same supported run. -/
theorem owner_success {I D K X Response Shared Auxiliary : Type}
    (interpret : Shared → Word32)
    (native : QueryImpl (PqxdhBeaconPhase2Publication.NativeSpec I D K X Response) (StateT Auxiliary ProbComp))
    (handles : QueryImpl (FullSpec I D K X Response Shared) (StateT Auxiliary ProbComp))
    (calls : FullCalls interpret native handles) (decode : RawCtxReceive.FrameDecoder)
    (raw plaintext : Bytes) (state next : State I D K) (auxiliary final : Auxiliary)
    (supported : ((some plaintext, next), final) ∈ support ((simulateQ handles (owner decode raw state)).run auxiliary)) :
    ∃ staged, staged.opened.sequence = 1#u64 ∧ 8 < staged.opened.plaintext.length ∧
      PqxdhBeaconPhase2Publication.publish state staged = (plaintext, next) := by
  rw [← owner_realization interpret native handles calls] at supported
  exact PqxdhBeaconPhase2Publication.native_success native decode raw plaintext state next auxiliary final supported

/-- Failed active execution retains the same terminal abort and complete primitive effects; inactive execution changes neither state. -/
theorem owner_failure {I D K X Response Shared Auxiliary : Type}
    (interpret : Shared → Word32)
    (native : QueryImpl (PqxdhBeaconPhase2Publication.NativeSpec I D K X Response) (StateT Auxiliary ProbComp))
    (handles : QueryImpl (FullSpec I D K X Response Shared) (StateT Auxiliary ProbComp))
    (calls : FullCalls interpret native handles) (decode : RawCtxReceive.FrameDecoder)
    (raw : Bytes) (state next : State I D K) (auxiliary final : Auxiliary)
    (supported : ((none, next), final) ∈ support ((simulateQ handles (owner decode raw state)).run auxiliary)) :
    match state.beacon.phase with
    | .initSent control _ _ _ => next = PqxdhBeaconPhase2Preparation.abort control state
    | _ => next = state ∧ final = auxiliary := by
  rw [← owner_realization interpret native handles calls] at supported
  exact PqxdhBeaconPhase2Publication.native_failure native decode raw state next auxiliary final supported

end BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared.admitted_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared.admitted_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared.collect_realization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared.collect_realization

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared.prepared_related' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared.prepared_related

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared.afterInputs_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared.afterInputs_continuation

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared.prepare_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared.prepare_continuation

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared.cleared_related' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared.cleared_related

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared.raw_realization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared.raw_realization

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared.afterRoot_realization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared.afterRoot_realization

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared.tail_realization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared.tail_realization

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared.owner_realization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared.owner_realization

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared.owner_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared.owner_continuation

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared.owner_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared.owner_query_bounds

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared.owner_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared.owner_success

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared.owner_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared.owner_failure
