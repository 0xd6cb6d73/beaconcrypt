import BeaconcryptCore.Computational.PqxdhBeaconPhase2Preparation
import BeaconcryptCore.Computational.PqxdhRootTableInitialization
import BeaconcryptCore.Refinement.ProtocolComposition

/-!
The private native Phase2 tail retains the prepared response until root derivation and the actual initial ratchet request have completed, then fetches the application ciphertext and invokes the existing full raw receive wrapper. The authenticated returned sequence is checked for one before plaintext length, binding authentication and final pinned-Server checks. Every failure discards the local candidate kernel and terminally aborts InitSent; success installs the actual returned kernel and assigned outer key ID. All optional primitive/codec effects remain in the shared interpreter state.

The root callback models the ordinary optional extract/expand call together with its unconditional input-erasure effect. Its native implementation and physical erasure remain explicit contracts. Initial KDF replies retain the actual fixed 64-byte type; no independent output or correctness law is assumed. The private core candidate reflects root-input clearing before later authentication. Frame decoding is the existing explicit codec function. No successful opening, challenge-secret routing, freshness, library implementation or global security premise is introduced by this operational interface.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open BeaconcryptCore.Refinement
open PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication
open PqxdhBeaconPhase2Preparation (Bytes Word32 State Prepared)
open PqxdhInitialRatchetComplementarity (beaconPending)

inductive AuxQuery (Response : Type) where
  | root : pqxdh.RootKeyInput → AuxQuery Response
  | initial : SymmetricRatchetKdfRequest → AuxQuery Response
  | application : Response → AuxQuery Response

abbrev AuxSpec (Response : Type) : OracleSpec (AuxQuery Response)
  | .root _ => Option Word32
  | .initial _ => pqxdh.concrete.InitialRatchetKdfResponse
  | .application _ => Option Bytes

abbrev TailSpec (Response : Type) := RawCtxWholeOwner.PrimitiveSpec + AuxSpec Response
abbrev FullSpec (I D K X Response : Type) := PqxdhBeaconPhase2Preparation.Spec I D K X Response + TailSpec Response

/-- The native root helper unconditionally clears all 192 candidate input bytes before returning its optional result. -/
def clearedCandidate (candidate : pqxdh.BeaconRegistrationCandidate) : pqxdh.BeaconRegistrationCandidate :=
  { candidate with root_key_input := ⟨⟨List.replicate 192 0#u8, by simp only [List.length_replicate]; rfl⟩⟩ }

noncomputable def normalInitial (pending : pqxdh.concrete.InitialRatchetKdfPending)
    (response : pqxdh.concrete.InitialRatchetKdfResponse) : ConcreteRatchetKernel :=
  (BeaconcryptCore.PanicFreedom.resume_initial_ratchet_kdf_ok pending response).choose

/-- The normalized initial kernel is the exact extracted result for every typed response. -/
theorem normalInitial_exact (pending : pqxdh.concrete.InitialRatchetKdfPending)
    (response : pqxdh.concrete.InitialRatchetKdfResponse) :
    pqxdh.concrete.resume_initial_ratchet_kdf pending response = ok (normalInitial pending response) :=
  (BeaconcryptCore.PanicFreedom.resume_initial_ratchet_kdf_ok pending response).choose_spec

noncomputable def initialRun {Response : Type} (root : Word32) : OracleComp (TailSpec Response) ConcreteRatchetKernel := do
  let response ← (TailSpec Response).query (.inr (.initial (beaconPending root).request))
  pure (normalInitial (beaconPending root) response)

noncomputable def normalAuthenticate (candidate : pqxdh.BeaconRegistrationCandidate)
    (sender : Std.U64) (binding : Std.Array Std.U8 8#usize) :
    core.result.Result pqxdh.AuthenticatedBeaconRegistration pqxdh.RegistrationError :=
  (BeaconcryptCore.PanicFreedom.authenticate_registration_key_id_binding_ok candidate sender binding).choose

/-- Binding authentication is the actual extracted optional result, without a correct-plaintext assumption. -/
theorem normalAuthenticate_exact (candidate : pqxdh.BeaconRegistrationCandidate)
    (sender : Std.U64) (binding : Std.Array Std.U8 8#usize) :
    pqxdh.authenticate_registration_key_id_binding candidate sender binding =
      ok (normalAuthenticate candidate sender binding) :=
  (BeaconcryptCore.PanicFreedom.authenticate_registration_key_id_binding_ok candidate sender binding).choose_spec

/-- Staged registration data remains private until both final native pin checks pass. -/
structure Staged where
  authenticated : pqxdh.AuthenticatedBeaconRegistration
  associatedData : Std.Array Std.U8 153#usize
  kernel : ConcreteRatchetKernel
  opened : RawCtxWholeOwner.Decrypted

/-- The post-opening sequence-one gate precedes both binding parsing and extracted authentication. -/
noncomputable def afterOpening (candidate : pqxdh.BeaconRegistrationCandidate) (kernel : ConcreteRatchetKernel)
    (reply : core.option.Option RawCtxWholeOwner.Decrypted) : Option Staged :=
  match reply with
  | .None => none
  | .Some opened =>
      if opened.sequence ≠ 1#u64 then none
      else if length : 8 < opened.plaintext.length then
        match normalAuthenticate candidate opened.keyId (ProtocolComposition.plaintextBinding opened.plaintext length) with
        | .Err _ => none
        | .Ok authenticated => some ⟨authenticated, candidate.associated_data, kernel, opened⟩
      else none

/-- The local raw owner uses the actual candidate pin/AD and both directions of the initial kernel. Its ghost attempt count is not a native Phase2 field. -/
def localOwner (candidate : pqxdh.BeaconRegistrationCandidate) (kernel : ConcreteRatchetKernel) :
    RawCtxWholeOwner.OwnerState Unit :=
  ⟨⟨kernel, candidate.server_binding.identity_key_id, absBytes candidate.associated_data, ()⟩, 0⟩

def rawLift {Response : Type} : QueryImpl RawCtxWholeOwner.PrimitiveSpec (OracleComp (TailSpec Response)) :=
  fun query => liftM ((TailSpec Response).query (.inl query))

/-- Actual initial KDF execution precedes the app getter and complete raw receive, including every failing opening effect. -/
noncomputable def afterRoot {Response : Type} (decode : RawCtxReceive.FrameDecoder)
    (prepared : Prepared Response) (root : Word32) : OracleComp (TailSpec Response) (Option Staged) := do
  let candidate := clearedCandidate prepared.candidate
  let kernel ← initialRun root
  let raw ← (TailSpec Response).query (.inr (.application prepared.response))
  match raw with
  | none => pure none
  | some raw => do
      let result ← simulateQ rawLift ((RawCtxWholeOwner.rawReceive decode raw).run (localOwner candidate kernel))
      pure (afterOpening candidate result.2.owner.kernel result.1)

/-- Root processing retains its actual optional result and interpreter effects before any initial KDF or app parsing. -/
noncomputable def tail {Response : Type} (decode : RawCtxReceive.FrameDecoder)
    (prepared : Prepared Response) : OracleComp (TailSpec Response) (Option Staged) := do
  let root ← (TailSpec Response).query (.inr (.root prepared.candidate.root_key_input))
  match root with
  | none => pure none
  | some root => afterRoot decode prepared root

/-- Exact extracted commit fields are installed only after both original outer pin checks. -/
def publish {I D K : Type} (state : State I D K) (staged : Staged) : Bytes × State I D K :=
  (staged.opened.plaintext.drop 8,
    { state with beacon := { state.beacon with
        identityKeyId := staged.authenticated.candidate.assigned_key_id
        phase := .established
          ⟨staged.authenticated.candidate.server_binding, staged.authenticated.candidate.assigned_key_id⟩
          staged.associatedData staged.kernel } })

noncomputable def finish {I D K : Type} (control : pqxdh.BeaconInitSent) (state : State I D K)
    (staged : Option Staged) : Option Bytes × State I D K :=
  match staged with
  | none => (none, PqxdhBeaconPhase2Preparation.abort control state)
  | some staged =>
      if control.expected_server_binding.identity_key_id ≠ staged.authenticated.candidate.server_binding.identity_key_id then
        (none, PqxdhBeaconPhase2Preparation.abort control state)
      else if absBytes state.beacon.serverIdentity ≠ absBytes staged.authenticated.candidate.server_binding.identity_public_key then
        (none, PqxdhBeaconPhase2Preparation.abort control state)
      else let result := publish state staged; (some result.1, result.2)

def preLift {I D K X Response : Type} :
    QueryImpl (PqxdhBeaconPhase2Preparation.Spec I D K X Response) (OracleComp (FullSpec I D K X Response)) :=
  fun query => liftM ((FullSpec I D K X Response).query (.inl query))

def tailLift {I D K X Response : Type} : QueryImpl (TailSpec Response) (OracleComp (FullSpec I D K X Response)) :=
  fun query => liftM ((FullSpec I D K X Response).query (.inr query))

/-- Every original active branch shares one complete primitive state across preparation, root, initialization, opening and publication. -/
noncomputable def owner {I D K X Response : Type} (decode : RawCtxReceive.FrameDecoder)
    (raw : Bytes) (state : State I D K) : OracleComp (FullSpec I D K X Response) (Option Bytes × State I D K) :=
  match state.beacon.phase with
  | .initSent control prekey oneTime kem => do
      let prepared ← simulateQ preLift
        (PqxdhBeaconPhase2Preparation.prepare control state.beacon.identity prekey oneTime kem raw)
      match prepared with
      | none => pure (finish control state none)
      | some prepared => do
          let staged ← simulateQ tailLift (tail decode prepared)
          pure (finish control state staged)
  | _ => pure (none, state)

/-- The callback request comes from the actual candidate initializer and retains its exact source label/input. -/
theorem initial_request (candidate : pqxdh.BeaconRegistrationCandidate) (root : Word32) :
    pqxdh.concrete.start_beacon_candidate_ratchet_kdf candidate root = ok (beaconPending root) ∧
    (beaconPending root).request = ⟨root, SYM_RATCHET_INFO⟩ := by
  exact ⟨pqxdh.concrete.start_beacon_ratchet_kdf_exact root, rfl⟩

/-- Clearing the private root input preserves the candidate's complete binding and session AD. -/
theorem clearedCandidate_fields (candidate : pqxdh.BeaconRegistrationCandidate) :
    (clearedCandidate candidate).server_binding = candidate.server_binding ∧
    (clearedCandidate candidate).assigned_key_id = candidate.assigned_key_id ∧
    (clearedCandidate candidate).associated_data = candidate.associated_data ∧
    (clearedCandidate candidate).root_key_input.bytes.val = List.replicate 192 0#u8 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Any authenticated non-one sequence is rejected before the plaintext binding is inspected. -/
theorem afterOpening_wrong_sequence (candidate : pqxdh.BeaconRegistrationCandidate)
    (kernel : ConcreteRatchetKernel) (opened : RawCtxWholeOwner.Decrypted)
    (wrong : opened.sequence ≠ 1#u64) : afterOpening candidate kernel (.Some opened) = none := by
  change (if opened.sequence ≠ 1#u64 then none else _) = none
  exact if_pos wrong

/-- Every staged success retains the actual raw result/kernel and derives sequence one plus the extracted plaintext-binding acceptance. -/
theorem afterOpening_success (candidate : pqxdh.BeaconRegistrationCandidate)
    (kernel : ConcreteRatchetKernel) (reply : core.option.Option RawCtxWholeOwner.Decrypted)
    (staged : Staged) (success : afterOpening candidate kernel reply = some staged) :
    reply = .Some staged.opened ∧ staged.opened.sequence = 1#u64 ∧
    staged.kernel = kernel ∧ staged.associatedData = candidate.associated_data ∧
    ∃ length : 8 < staged.opened.plaintext.length,
      pqxdh.authenticate_registration_key_id_binding candidate staged.opened.keyId
        (ProtocolComposition.plaintextBinding staged.opened.plaintext length) = ok (.Ok staged.authenticated) := by
  cases reply with
  | none => cases success
  | some opened =>
      by_cases sequence : opened.sequence = 1#u64
      · by_cases length : 8 < opened.plaintext.length
        · simp only [afterOpening, sequence, ne_eq, not_true_eq_false, if_false, length, _root_.dite_true] at success
          cases actual : normalAuthenticate candidate opened.keyId
              (ProtocolComposition.plaintextBinding opened.plaintext length) with
          | Err error => simp only [actual] at success; cases success
          | Ok authenticated =>
              simp only [actual, Option.some.injEq] at success
              subst staged
              exact ⟨rfl, sequence, rfl, rfl, length,
                (normalAuthenticate_exact candidate opened.keyId _).trans (congrArg ok actual)⟩
        · simp only [afterOpening, sequence, ne_eq, not_true_eq_false, if_false, length, _root_.dite_false] at success
          cases success
      · simp only [afterOpening, sequence, ne_eq, not_false_eq_true, if_true] at success
        cases success

/-- Publication uses the actual extracted commitment and keeps every unrelated native field. -/
theorem publish_fields {I D K : Type} (state : State I D K) (staged : Staged) :
    (publish state staged).1 = staged.opened.plaintext.drop 8 ∧
    (publish state staged).2.beacon.identity = state.beacon.identity ∧
    (publish state staged).2.beacon.serverIdentity = state.beacon.serverIdentity ∧
    (publish state staged).2.rawAttempts = state.rawAttempts ∧
    (publish state staged).2.beacon.identityKeyId = staged.authenticated.candidate.assigned_key_id ∧
    (publish state staged).2.beacon.phase = .established
      ⟨staged.authenticated.candidate.server_binding, staged.authenticated.candidate.assigned_key_id⟩
      staged.associatedData staged.kernel ∧
    pqxdh.beacon_commit staged.authenticated = ok
      ⟨staged.authenticated.candidate.server_binding, staged.authenticated.candidate.assigned_key_id⟩ :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The complete raw/primitive poststate passes to the next private continuation after the actual initial request and deferred app getter. -/
theorem afterRoot_complete {Response A Result : Type}
    (handler : QueryImpl (TailSpec Response) (StateT A ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (prepared : Prepared Response) (root : Word32) (auxiliary : A)
    (next : Option Staged × A → ProbComp Result) :
    (simulateQ handler (afterRoot decode prepared root)).run auxiliary >>= next =
      (handler (.inr (.initial (beaconPending root).request))).run auxiliary >>= fun initial =>
        (handler (.inr (.application prepared.response))).run initial.2 >>= fun application =>
          match application.1 with
          | none => next (none, application.2)
          | some raw =>
              RawCtxWholeOwner.rawGame (fun query => handler (.inl query)) decode raw
                (localOwner (clearedCandidate prepared.candidate) (normalInitial (beaconPending root) initial.1))
                application.2 >>= fun received =>
                next (afterOpening (clearedCandidate prepared.candidate) received.1.2.owner.kernel received.1.1,
                  received.2) := by
  simp only [afterRoot, initialRun, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    bind_assoc, pure_bind]
  apply bind_congr
  intro initial
  apply bind_congr
  intro application
  cases application.1 with
  | none => simp only [simulateQ_pure, StateT.run_pure, pure_bind]
  | some raw =>
      simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure, bind_assoc, pure_bind]
      have adapter : handler ∘ₛ (rawLift (Response := Response)) = fun query => handler (.inl query) := by
        funext query
        exact simulateQ_spec_query handler (.inl query)
      rw [← QueryImpl.simulateQ_compose, adapter]
      rfl

/-- Root rejection keeps its actual primitive poststate; root success supplies only its actual private output to the remaining source tail. -/
theorem tail_complete {Response A Result : Type}
    (handler : QueryImpl (TailSpec Response) (StateT A ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (prepared : Prepared Response) (auxiliary : A)
    (next : Option Staged × A → ProbComp Result) :
    (simulateQ handler (tail decode prepared)).run auxiliary >>= next =
      (handler (.inr (.root prepared.candidate.root_key_input))).run auxiliary >>= fun derived =>
        match derived.1 with
        | none => next (none, derived.2)
        | some root => (simulateQ handler (afterRoot decode prepared root)).run derived.2 >>= next := by
  simp only [tail, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
  apply bind_congr
  intro derived
  cases derived.1 <;> simp only [simulateQ_pure, StateT.run_pure, pure_bind]

/-- Any final native pin mismatch and every earlier tail failure have exactly the same terminal abort projection. -/
theorem finish_failure {I D K : Type} (control : pqxdh.BeaconInitSent) (state : State I D K)
    (staged : Option Staged) (failed : (finish control state staged).1 = none) :
    (finish control state staged).2 = PqxdhBeaconPhase2Preparation.abort control state := by
  cases staged with
  | none => rfl
  | some staged =>
      simp only [finish] at failed ⊢
      split_ifs <;> simp_all

/-- Successful publication derives both native outer pin checks and the complete exact committed state. -/
theorem finish_success {I D K : Type} (control : pqxdh.BeaconInitSent) (state next : State I D K)
    (candidate : Option Staged) (plaintext : Bytes)
    (success : finish control state candidate = (some plaintext, next)) :
    ∃ staged, candidate = some staged ∧
      control.expected_server_binding.identity_key_id = staged.authenticated.candidate.server_binding.identity_key_id ∧
      absBytes state.beacon.serverIdentity = absBytes staged.authenticated.candidate.server_binding.identity_public_key ∧
      publish state staged = (plaintext, next) := by
  cases candidate with
  | none => cases success
  | some staged =>
      simp only [finish] at success
      split_ifs at success with key identity
      · cases success
      · cases success
      · have result := Prod.mk.inj success
        exact ⟨staged, rfl, not_ne_iff.mp key, not_ne_iff.mp identity,
          Prod.ext (Option.some.inj result.1) result.2⟩

/-- The full Phase2 API rejects every non-InitSent phase without parsing or any primitive callback. -/
theorem owner_inactive {I D K X Response : Type} (decode : RawCtxReceive.FrameDecoder)
    (raw : Bytes) (state : State I D K)
    (inactive : ∀ control prekey oneTime kem, state.beacon.phase ≠ .initSent control prekey oneTime kem) :
    owner (X := X) (Response := Response) decode raw state = pure (none, state) := by
  cases active : state.beacon.phase with
  | initSent control prekey oneTime kem => exact False.elim (inactive _ _ _ _ active)
  | _ => simp only [owner, active]

/-- A supported staged success contains the actual initial response, deferred app bytes and complete raw receive result, including every intermediate primitive state. -/
theorem afterRoot_supported {Response A : Type}
    (handler : QueryImpl (TailSpec Response) (StateT A ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (prepared : Prepared Response) (root : Word32)
    (auxiliary final : A) (staged : Staged)
    (supported : (some staged, final) ∈ support ((simulateQ handler (afterRoot decode prepared root)).run auxiliary)) :
    ∃ initial initialState raw appState received,
      (initial, initialState) ∈ support ((handler (.inr (.initial (beaconPending root).request))).run auxiliary) ∧
      (some raw, appState) ∈ support ((handler (.inr (.application prepared.response))).run initialState) ∧
      received ∈ support (RawCtxWholeOwner.rawGame (fun query => handler (.inl query)) decode raw
        (localOwner (clearedCandidate prepared.candidate) (normalInitial (beaconPending root) initial)) appState) ∧
      received.2 = final ∧
      afterOpening (clearedCandidate prepared.candidate) received.1.2.owner.kernel received.1.1 = some staged := by
  have equation := afterRoot_complete handler decode prepared root auxiliary (fun result => pure result)
  simp only [bind_pure] at equation
  rw [equation, mem_support_bind_iff] at supported
  obtain ⟨⟨initial, initialState⟩, initialSupport, supported⟩ := supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨⟨application, appState⟩, appSupport, supported⟩ := supported
  cases application with
  | none =>
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq, Option.some_ne_none, false_and] at supported
  | some raw =>
      rw [mem_support_bind_iff] at supported
      obtain ⟨received, rawSupport, supported⟩ := supported
      have equal := eq_of_mem_support_pure _ supported
      exact ⟨initial, initialState, raw, appState, received, initialSupport, appSupport, rawSupport,
        (congrArg Prod.snd equal).symm, (congrArg Prod.fst equal).symm⟩

/-- The successful root value is the actual private optional callback output, with its full poststate retained into raw processing. -/
theorem tail_supported {Response A : Type}
    (handler : QueryImpl (TailSpec Response) (StateT A ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (prepared : Prepared Response) (auxiliary final : A) (staged : Staged)
    (supported : (some staged, final) ∈ support ((simulateQ handler (tail decode prepared)).run auxiliary)) :
    ∃ root intermediate,
      (some root, intermediate) ∈ support ((handler (.inr (.root prepared.candidate.root_key_input))).run auxiliary) ∧
      (some staged, final) ∈ support ((simulateQ handler (afterRoot decode prepared root)).run intermediate) := by
  have equation := tail_complete handler decode prepared auxiliary (fun result => pure result)
  simp only [bind_pure] at equation
  rw [equation, mem_support_bind_iff] at supported
  obtain ⟨⟨root, intermediate⟩, rootSupport, supported⟩ := supported
  cases root with
  | none =>
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq, Option.some_ne_none, false_and] at supported
  | some root => exact ⟨root, intermediate, rootSupport, supported⟩

/-- Every actual tail success proves the authenticated sequence-one gate from its raw result, without decryption correctness or source honesty. -/
theorem tail_sequence_one {Response A : Type}
    (handler : QueryImpl (TailSpec Response) (StateT A ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (prepared : Prepared Response) (auxiliary final : A) (staged : Staged)
    (supported : (some staged, final) ∈ support ((simulateQ handler (tail decode prepared)).run auxiliary)) :
    staged.opened.sequence = 1#u64 ∧ 8 < staged.opened.plaintext.length := by
  obtain ⟨root, intermediate, _, after⟩ := tail_supported handler decode prepared auxiliary final staged supported
  obtain ⟨initial, initialState, raw, appState, received, _, _, _, _, opening⟩ :=
    afterRoot_supported handler decode prepared root intermediate final staged after
  obtain ⟨_, sequence, _, _, length, _⟩ := afterOpening_success _ _ _ staged opening
  exact ⟨sequence, length⟩

/-- All active Phase2 callbacks execute in one interpreter state before the exact original finish/abort projection and arbitrary continuation. -/
theorem owner_complete {I D K X Response A Result : Type}
    (handler : QueryImpl (FullSpec I D K X Response) (StateT A ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (raw : Bytes) (state : State I D K)
    (control : pqxdh.BeaconInitSent) (prekey oneTime : D) (kem : K)
    (active : state.beacon.phase = .initSent control prekey oneTime kem) (auxiliary : A)
    (next : (Option Bytes × State I D K) × A → ProbComp Result) :
    (simulateQ handler (owner decode raw state)).run auxiliary >>= next =
      (simulateQ (fun query => handler (.inl query))
        (PqxdhBeaconPhase2Preparation.prepare control state.beacon.identity prekey oneTime kem raw)).run auxiliary >>=
        fun prepared => match prepared.1 with
        | none => next (finish control state none, prepared.2)
        | some preparedValue =>
            (simulateQ (fun query => handler (.inr query)) (tail decode preparedValue)).run prepared.2 >>= fun staged =>
              next (finish control state staged.1, staged.2) := by
  have preAdapter : handler ∘ₛ preLift = fun query => handler (.inl query) := by
    funext query
    exact simulateQ_spec_query handler (.inl query)
  have tailAdapter : handler ∘ₛ tailLift = fun query => handler (.inr query) := by
    funext query
    exact simulateQ_spec_query handler (.inr query)
  simp only [owner, active, simulateQ_bind, StateT.run_bind, ← QueryImpl.simulateQ_compose,
    preAdapter, bind_assoc]
  apply bind_congr
  intro prepared
  cases prepared.1 with
  | none => simp only [simulateQ_pure, StateT.run_pure, pure_bind]
  | some preparedValue =>
      simp only [simulateQ_bind, StateT.run_bind, ← QueryImpl.simulateQ_compose,
        tailAdapter, simulateQ_pure, StateT.run_pure, bind_assoc, pure_bind]

/-- Every successful original API call derives its active phase, actual prepared candidate, full private tail, authenticated sequence one and exact final publication from the same supported execution. -/
theorem owner_success {I D K X Response A : Type}
    (handler : QueryImpl (FullSpec I D K X Response) (StateT A ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (raw plaintext : Bytes) (state next : State I D K)
    (auxiliary final : A)
    (supported : ((some plaintext, next), final) ∈ support ((simulateQ handler (owner decode raw state)).run auxiliary)) :
    ∃ control prekey oneTime kem prepared intermediate staged,
      state.beacon.phase = .initSent control prekey oneTime kem ∧
      (some prepared, intermediate) ∈ support ((simulateQ (fun query => handler (.inl query))
        (PqxdhBeaconPhase2Preparation.prepare control state.beacon.identity prekey oneTime kem raw)).run auxiliary) ∧
      (some staged, final) ∈ support ((simulateQ (fun query => handler (.inr query)) (tail decode prepared)).run intermediate) ∧
      finish control state (some staged) = (some plaintext, next) ∧
      staged.opened.sequence = 1#u64 ∧ 8 < staged.opened.plaintext.length ∧
      publish state staged = (plaintext, next) := by
  cases active : state.beacon.phase with
  | initSent control prekey oneTime kem =>
      have equation := owner_complete handler decode raw state control prekey oneTime kem active auxiliary
        (fun result => pure result)
      simp only [bind_pure] at equation
      rw [equation, mem_support_bind_iff] at supported
      obtain ⟨⟨prepared, intermediate⟩, preSupport, supported⟩ := supported
      cases prepared with
      | none =>
          simp only [finish, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
            Option.some_ne_none, false_and] at supported
      | some prepared =>
          rw [mem_support_bind_iff] at supported
          obtain ⟨⟨staged, after⟩, tailSupport, supported⟩ := supported
          have equal := eq_of_mem_support_pure _ supported
          have finalEq : final = after := congrArg Prod.snd equal
          subst after
          have finished : (some plaintext, next) = finish control state staged := congrArg Prod.fst equal
          obtain ⟨actualStaged, same, _, _, published⟩ := finish_success control state next staged plaintext finished.symm
          subst staged
          have gates := tail_sequence_one (fun query => handler (.inr query)) decode prepared intermediate final actualStaged tailSupport
          exact ⟨control, prekey, oneTime, kem, prepared, intermediate, actualStaged,
            rfl, preSupport, tailSupport, finished.symm, gates.1, gates.2, published⟩
  | _ =>
      simp only [owner, active, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq, Option.some_ne_none, false_and] at supported

/-- Every failed active API call returns the terminal native abort state, retaining the full actual primitive poststate; inactive calls preserve both states. -/
theorem owner_failure {I D K X Response A : Type}
    (handler : QueryImpl (FullSpec I D K X Response) (StateT A ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (raw : Bytes) (state next : State I D K) (auxiliary final : A)
    (supported : ((none, next), final) ∈ support ((simulateQ handler (owner decode raw state)).run auxiliary)) :
    match state.beacon.phase with
    | .initSent control _ _ _ => next = PqxdhBeaconPhase2Preparation.abort control state
    | _ => next = state ∧ final = auxiliary := by
  cases active : state.beacon.phase with
  | initSent control prekey oneTime kem =>
      have equation := owner_complete handler decode raw state control prekey oneTime kem active auxiliary
        (fun result => pure result)
      simp only [bind_pure] at equation
      rw [equation, mem_support_bind_iff] at supported
      obtain ⟨⟨prepared, intermediate⟩, _, supported⟩ := supported
      cases prepared with
      | none =>
          have equal := eq_of_mem_support_pure _ supported
          exact congrArg (fun result => result.1.2) equal
      | some prepared =>
          rw [mem_support_bind_iff] at supported
          obtain ⟨⟨staged, after⟩, _, supported⟩ := supported
          have equal := eq_of_mem_support_pure _ supported
          have failed := (congrArg (fun result => result.1.1) equal).symm
          exact (congrArg (fun result => result.1.2) equal).trans (finish_failure control state staged failed)
  | _ =>
      simp only [owner, active, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq, true_and] at supported
      exact supported

abbrev NativeTailSpec (Response : Type) := RawCtxSourceOpen.NativeSpec + AuxSpec Response
abbrev NativeSpec (I D K X Response : Type) :=
  PqxdhBeaconPhase2Preparation.Spec I D K X Response + NativeTailSpec Response

def nativeRawLift {Response : Type} : QueryImpl RawCtxSourceOpen.NativeSpec (OracleComp (NativeTailSpec Response)) :=
  fun query => liftM ((NativeTailSpec Response).query (.inl query))

/-- The actual selected CTX opening expands into its retained hash and combined-ciphertext AEAD callbacks. -/
def nativeTailAdapter {Response : Type} : QueryImpl (TailSpec Response) (OracleComp (NativeTailSpec Response))
  | .inl query => simulateQ nativeRawLift (RawCtxSourceOpen.nativeAdapter query)
  | .inr query => liftM ((NativeTailSpec Response).query (.inr query))

def nativeTailLift {I D K X Response : Type} : QueryImpl (NativeTailSpec Response) (OracleComp (NativeSpec I D K X Response)) :=
  fun query => liftM ((NativeSpec I D K X Response).query (.inr query))

def nativeAdapter {I D K X Response : Type} : QueryImpl (FullSpec I D K X Response) (OracleComp (NativeSpec I D K X Response))
  | .inl query => liftM ((NativeSpec I D K X Response).query (.inl query))
  | .inr query => simulateQ nativeTailLift (nativeTailAdapter query)

/-- This is the whole native-shaped Phase2 program, with optional hash and AEAD effects rather than an assumed CTX success. -/
noncomputable def nativeOwner {I D K X Response : Type} (decode : RawCtxReceive.FrameDecoder)
    (raw : Bytes) (state : State I D K) : OracleComp (NativeSpec I D K X Response) (Option Bytes × State I D K) :=
  simulateQ nativeAdapter (owner decode raw state)

/-- Native hash/AEAD expansion preserves every original codec, root and initial callback argument and keeps the complete interpreter state. -/
theorem native_complete {I D K X Response A Result : Type}
    (handler : QueryImpl (NativeSpec I D K X Response) (StateT A ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (raw : Bytes) (state : State I D K) (auxiliary : A)
    (next : (Option Bytes × State I D K) × A → ProbComp Result) :
    (simulateQ handler (nativeOwner decode raw state)).run auxiliary >>= next =
      (simulateQ (handler ∘ₛ nativeAdapter) (owner decode raw state)).run auxiliary >>= next := by
  rw [nativeOwner, ← QueryImpl.simulateQ_compose]

/-- The complete native primitive expansion still derives authenticated sequence-one publication from actual supported outcomes. -/
theorem native_success {I D K X Response A : Type}
    (handler : QueryImpl (NativeSpec I D K X Response) (StateT A ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (raw plaintext : Bytes) (state next : State I D K) (auxiliary final : A)
    (supported : ((some plaintext, next), final) ∈ support ((simulateQ handler (nativeOwner decode raw state)).run auxiliary)) :
    ∃ staged, staged.opened.sequence = 1#u64 ∧ 8 < staged.opened.plaintext.length ∧
      publish state staged = (plaintext, next) := by
  rw [nativeOwner, ← QueryImpl.simulateQ_compose] at supported
  obtain ⟨control, prekey, oneTime, kem, prepared, intermediate, staged, _, _, _, _, sequence, length, published⟩ :=
    owner_success (handler ∘ₛ nativeAdapter) decode raw plaintext state next auxiliary final supported
  exact ⟨staged, sequence, length, published⟩

/-- Hash rejection, commitment mismatch and AEAD failure retain their actual effects and terminally abort active Phase2. -/
theorem native_failure {I D K X Response A : Type}
    (handler : QueryImpl (NativeSpec I D K X Response) (StateT A ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (raw : Bytes) (state next : State I D K) (auxiliary final : A)
    (supported : ((none, next), final) ∈ support ((simulateQ handler (nativeOwner decode raw state)).run auxiliary)) :
    match state.beacon.phase with
    | .initSent control _ _ _ => next = PqxdhBeaconPhase2Preparation.abort control state
    | _ => next = state ∧ final = auxiliary := by
  rw [nativeOwner, ← QueryImpl.simulateQ_compose] at supported
  exact owner_failure (handler ∘ₛ nativeAdapter) decode raw state next auxiliary final supported

end BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.normalInitial_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.normalInitial_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.normalAuthenticate_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.normalAuthenticate_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.initial_request' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.initial_request

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.clearedCandidate_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.clearedCandidate_fields

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.afterOpening_wrong_sequence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.afterOpening_wrong_sequence

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.afterOpening_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.afterOpening_success

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.publish_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.publish_fields

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.afterRoot_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.afterRoot_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.tail_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.tail_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.finish_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.finish_failure

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.finish_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.finish_success

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.owner_inactive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.owner_inactive

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.afterRoot_supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.afterRoot_supported

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.tail_supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.tail_supported

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.tail_sequence_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.tail_sequence_one

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.owner_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.owner_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.owner_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.owner_success

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.owner_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.owner_failure

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.native_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.native_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.native_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.native_success

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.native_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication.native_failure
