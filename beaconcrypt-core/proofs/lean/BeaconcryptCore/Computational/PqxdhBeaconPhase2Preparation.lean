import BeaconcryptCore.Computational.RawCtxBeaconLifecycle
import BeaconcryptCore.PanicFreedom.Pqxdh
import BeaconcryptCore.Computational.FinitePartitionQueryBounds

/-!
This private adapter follows the native InitSent Phase2 path up to the root-derivation continuation. Optional packed decoding and typed field conversions precede the two identity conversions, actual optional decapsulation and four ordered DH calls. The assigned-ID getter follows those calls. The extracted beacon_prepare_finish runs before the explicit shared-secret erasure callback, including its rejection branch. The application ciphertext getter is deliberately deferred until after root derivation and initial ratchet construction, as in the native adapter.

All callback arguments, optional replies and complete interpreter state remain in this private computation. Identity, KEM and converted-identity secret representations are arbitrary handles; no secret is an adversarial oracle reply. Ordinary preparation failure terminally aborts InitSent and resets the outer identity key ID to the pinned Server ID. Inactive phases reject unchanged. This stage supplies no authentication, successful plaintext, codec, library, memory-erasure or challenge-routing assumption. Its subsequent private continuation must still implement root processing, exact raw sequence-one reception, binding and native publication.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhBeaconPhase2Preparation

abbrev Bytes := Pqxdh.Bytes
abbrev Word32 := Std.Array Std.U8 32#usize
abbrev Ciphertext := Std.Array Std.U8 1088#usize
abbrev State (I D K : Type) := RawCtxBeaconLifecycle.State I D K

/-- Each callback is private; field callbacks combine the native getter and its exact typed conversion. -/
inductive Query (I D K X Response : Type) where
  | decode : Bytes → Query I D K X Response
  | ciphertext : Response → Query I D K X Response
  | ephemeral : Response → Query I D K X Response
  | serverIdentity : Response → Query I D K X Response
  | publicConversion : Word32 → Query I D K X Response
  | privateConversion : I → Query I D K X Response
  | decapsulate : Ciphertext → K → Query I D K X Response
  | dhPair : D → Word32 → Query I D K X Response
  | dhIdentity : X → Word32 → Query I D K X Response
  | assignedId : Response → Query I D K X Response
  | eraseShared : pqxdh.PqxdhSharedSecrets → Query I D K X Response

abbrev Spec (I D K X Response : Type) : OracleSpec (Query I D K X Response) := fun query =>
  match query with
  | .decode _ => Option Response
  | .ciphertext _ => Option Ciphertext
  | .ephemeral _ | .serverIdentity _ | .publicConversion _ => Option Word32
  | .privateConversion _ => Option X
  | .decapsulate _ _ | .dhPair _ _ | .dhIdentity _ _ => Option Word32
  | .assignedId _ => Std.U64
  | .eraseShared _ => Unit

/-- Native typed parsing and primitive outputs, before the core preparation and erasure boundary. -/
structure Inputs (Response : Type) where
  response : Response
  ciphertext : Ciphertext
  ephemeral : Word32
  finishInputs : pqxdh.BeaconFinishInputs

/-- Full private root input and original response handle retained for the next native stage. -/
structure Prepared (Response : Type) where
  response : Response
  ciphertext : Ciphertext
  ephemeral : Word32
  candidate : pqxdh.BeaconRegistrationCandidate

variable {I D K X Response : Type}

/-- Original optional order, including DH1(prekey,Server), DH2(identity,ephemeral), DH3(prekey,ephemeral), and DH4(one-time,ephemeral). -/
def collect (identity : I) (prekey oneTime : D) (kem : K) (raw : Bytes) :
    OracleComp (Spec I D K X Response) (Option (Inputs Response)) := OptionT.run do
  let response ← OptionT.mk ((Spec I D K X Response).query (.decode raw))
  let ciphertext ← OptionT.mk ((Spec I D K X Response).query (.ciphertext response))
  let ephemeral ← OptionT.mk ((Spec I D K X Response).query (.ephemeral response))
  let server ← OptionT.mk ((Spec I D K X Response).query (.serverIdentity response))
  let serverConverted ← OptionT.mk ((Spec I D K X Response).query (.publicConversion server))
  let identityConverted ← OptionT.mk ((Spec I D K X Response).query (.privateConversion identity))
  let shared ← OptionT.mk ((Spec I D K X Response).query (.decapsulate ciphertext kem))
  let dh1 ← OptionT.mk ((Spec I D K X Response).query (.dhPair prekey serverConverted))
  let dh2 ← OptionT.mk ((Spec I D K X Response).query (.dhIdentity identityConverted ephemeral))
  let dh3 ← OptionT.mk ((Spec I D K X Response).query (.dhPair prekey ephemeral))
  let dh4 ← OptionT.mk ((Spec I D K X Response).query (.dhPair oneTime ephemeral))
  let assigned ← liftM ((Spec I D K X Response).query (.assignedId response))
  pure ⟨response, ciphertext, ephemeral, ⟨server, assigned, ⟨dh1, dh2, dh3, dh4, shared⟩⟩⟩

/-- Totality supplies the actual extracted result, including all identity and zero-DH errors. -/
noncomputable def normalPrepare (control : pqxdh.BeaconInitSent) (inputs : pqxdh.BeaconFinishInputs) :
    core.result.Result pqxdh.BeaconRegistrationCandidate pqxdh.RegistrationError :=
  (BeaconcryptCore.PanicFreedom.beacon_prepare_finish_ok control inputs).choose

theorem normalPrepare_exact (control : pqxdh.BeaconInitSent) (inputs : pqxdh.BeaconFinishInputs) :
    pqxdh.beacon_prepare_finish control inputs = ok (normalPrepare control inputs) :=
  (BeaconcryptCore.PanicFreedom.beacon_prepare_finish_ok control inputs).choose_spec

/-- Shared-secret erasure runs on both core preparation outcomes before any root continuation. -/
noncomputable def afterInputs (control : pqxdh.BeaconInitSent) (inputs : Inputs Response) :
    OracleComp (Spec I D K X Response) (Option (Prepared Response)) := do
  let prepared := normalPrepare control inputs.finishInputs
  let _ ← (Spec I D K X Response).query (.eraseShared inputs.finishInputs.shared_secrets)
  pure (match prepared with
    | .Err _ => none
    | .Ok candidate => some ⟨inputs.response, inputs.ciphertext, inputs.ephemeral, candidate⟩)

/-- The private pre-root stage executes only the source-selected callbacks and original extracted preparation. -/
noncomputable def prepare (control : pqxdh.BeaconInitSent) (identity : I) (prekey oneTime : D)
    (kem : K) (raw : Bytes) : OracleComp (Spec I D K X Response) (Option (Prepared Response)) := do
  let inputs ← collect identity prekey oneTime kem raw
  match inputs with
  | none => pure none
  | some inputs => afterInputs control inputs

/-- Native abort resets the outer key ID as well as discarding the InitSent private phase fields. -/
def abort (control : pqxdh.BeaconInitSent) (state : State I D K) : State I D K :=
  { state with beacon := { state.beacon with
      identityKeyId := control.expected_server_binding.identity_key_id
      phase := .aborted ⟨control.expected_server_binding.identity_key_id⟩ } }

/-- Private owner preparation preserves inactive states and terminally aborts every ordinary InitSent failure. -/
noncomputable def owner (raw : Bytes) (state : State I D K) :
    OracleComp (Spec I D K X Response) (Option (Prepared Response) × State I D K) :=
  match state.beacon.phase with
  | .initSent control prekey oneTime kem => do
      let prepared ← prepare control state.beacon.identity prekey oneTime kem raw
      pure (prepared, if prepared.isSome then state else abort control state)
  | _ => pure (none, state)

/-- The remaining private native stage receives the actual prepared input and complete owner/interpreter poststate. -/
noncomputable def continueWith {Result : Type} (raw : Bytes) (state : State I D K)
    (next : Option (Prepared Response) → State I D K → OracleComp (Spec I D K X Response) Result) :
    OracleComp (Spec I D K X Response) Result := do
  let result ← owner raw state
  next result.1 result.2

/-- Native abort changes exactly the phase and outer key ID, using the extracted abort control. -/
theorem abort_fields (control : pqxdh.BeaconInitSent) (state : State I D K) :
    (abort control state).beacon.identity = state.beacon.identity ∧
    (abort control state).beacon.serverIdentity = state.beacon.serverIdentity ∧
    (abort control state).rawAttempts = state.rawAttempts ∧
    (abort control state).beacon.identityKeyId = control.expected_server_binding.identity_key_id ∧
    (abort control state).beacon.phase = .aborted ⟨control.expected_server_binding.identity_key_id⟩ ∧
    pqxdh.beacon_abort_init control = ok ⟨control.expected_server_binding.identity_key_id⟩ :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Every inactive phase returns before a codec or primitive callback. -/
theorem owner_inactive (raw : Bytes) (state : State I D K)
    (inactive : ∀ control prekey oneTime kem,
      state.beacon.phase ≠ .initSent control prekey oneTime kem) :
    owner (X := X) (Response := Response) raw state = pure (none, state) := by
  cases phase : state.beacon.phase with
  | initSent control prekey oneTime kem => exact False.elim (inactive _ _ _ _ phase)
  | _ => simp only [owner, phase]

/-- Full interpreter state survives the core preparation and shared-secret erasure callback on both outcomes. -/
theorem afterInputs_complete {A Result : Type}
    (handler : QueryImpl (Spec I D K X Response) (StateT A ProbComp))
    (control : pqxdh.BeaconInitSent) (inputs : Inputs Response) (auxiliary : A)
    (next : Option (Prepared Response) × A → ProbComp Result) :
    (simulateQ handler (afterInputs control inputs)).run auxiliary >>= next =
      (handler (.eraseShared inputs.finishInputs.shared_secrets)).run auxiliary >>= fun result =>
        next ((match normalPrepare control inputs.finishInputs with
          | .Err _ => none
          | .Ok candidate => some ⟨inputs.response, inputs.ciphertext, inputs.ephemeral, candidate⟩), result.2) := by
  simp only [afterInputs, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    simulateQ_pure, StateT.run_pure, bind_assoc, pure_bind]

/-- The exact native owner update follows all ordinary preparation callbacks before the next private continuation. -/
theorem owner_complete {A Result : Type}
    (handler : QueryImpl (Spec I D K X Response) (StateT A ProbComp))
    (raw : Bytes) (state : State I D K) (control : pqxdh.BeaconInitSent)
    (prekey oneTime : D) (kem : K)
    (active : state.beacon.phase = .initSent control prekey oneTime kem) (auxiliary : A)
    (next : (Option (Prepared Response) × State I D K) × A → ProbComp Result) :
    (simulateQ handler (owner raw state)).run auxiliary >>= next =
      (simulateQ handler (prepare control state.beacon.identity prekey oneTime kem raw)).run auxiliary >>=
        fun result => next ((result.1, if result.1.isSome then state else abort control state), result.2) := by
  simp only [owner, active, simulateQ_bind, simulateQ_pure, StateT.run_bind,
    StateT.run_pure, bind_assoc, pure_bind]

/-- The continued private stage receives the original result and the complete actual callback poststate. -/
theorem continueWith_complete {A Result : Type}
    (handler : QueryImpl (Spec I D K X Response) (StateT A ProbComp))
    (raw : Bytes) (state : State I D K) (auxiliary : A)
    (next : Option (Prepared Response) → State I D K → OracleComp (Spec I D K X Response) Result) :
    (simulateQ handler (continueWith raw state next)).run auxiliary =
      (simulateQ handler (owner raw state)).run auxiliary >>= fun result =>
        (simulateQ handler (next result.1.1 result.1.2)).run result.2 := by
  simp only [continueWith, simulateQ_bind, StateT.run_bind]

/-- A prepared candidate is obtained from the actual extracted core result, never an independent success premise. -/
theorem afterInputs_origin {A : Type}
    (handler : QueryImpl (Spec I D K X Response) (StateT A ProbComp))
    (control : pqxdh.BeaconInitSent) (inputs : Inputs Response) (auxiliary final : A)
    (prepared : Prepared Response)
    (supported : (some prepared, final) ∈ support ((simulateQ handler (afterInputs control inputs)).run auxiliary)) :
    pqxdh.beacon_prepare_finish control inputs.finishInputs = ok (.Ok prepared.candidate) ∧
    prepared.response = inputs.response ∧ prepared.ciphertext = inputs.ciphertext ∧
    prepared.ephemeral = inputs.ephemeral := by
  simp only [afterInputs, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    simulateQ_pure, StateT.run_pure, mem_support_bind_iff] at supported
  obtain ⟨result, _, finished⟩ := supported
  have equal := eq_of_mem_support_pure _ finished
  cases actual : normalPrepare control inputs.finishInputs with
  | Err error => simp only [actual] at equal; cases equal
  | Ok candidate =>
      simp only [actual, Prod.mk.injEq, Option.some.injEq] at equal
      rcases equal with ⟨rfl, rfl⟩
      exact ⟨(normalPrepare_exact control inputs.finishInputs).trans (congrArg ok actual), rfl, rfl, rfl⟩

/-- Every supported pre-root success originates in the actual ordered parsing/primitive prefix and extracted preparation, with both intermediate and final interpreter states retained. -/
theorem prepare_origin {A : Type}
    (handler : QueryImpl (Spec I D K X Response) (StateT A ProbComp))
    (control : pqxdh.BeaconInitSent) (identity : I) (prekey oneTime : D) (kem : K) (raw : Bytes)
    (auxiliary final : A) (prepared : Prepared Response)
    (supported : (some prepared, final) ∈ support
      ((simulateQ handler (prepare control identity prekey oneTime kem raw)).run auxiliary)) :
    ∃ inputs intermediate,
      (some inputs, intermediate) ∈ support
        ((simulateQ handler (collect identity prekey oneTime kem raw)).run auxiliary) ∧
      (some prepared, final) ∈ support ((simulateQ handler (afterInputs control inputs)).run intermediate) ∧
      pqxdh.beacon_prepare_finish control inputs.finishInputs = ok (.Ok prepared.candidate) ∧
      prepared.response = inputs.response ∧ prepared.ciphertext = inputs.ciphertext ∧
      prepared.ephemeral = inputs.ephemeral := by
  simp only [prepare, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨inputs, intermediate⟩, collected, finished⟩ := supported
  cases inputs with
  | none =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, Option.some_ne_none, false_and] at finished
  | some inputs =>
      exact ⟨inputs, intermediate, collected, finished,
        afterInputs_origin handler control inputs intermediate final prepared finished⟩

/-- A successful owner preparation keeps the complete original InitSent owner and the actual private callback result. -/
theorem owner_success {A : Type}
    (handler : QueryImpl (Spec I D K X Response) (StateT A ProbComp))
    (raw : Bytes) (state next : State I D K) (auxiliary final : A) (prepared : Prepared Response)
    (supported : ((some prepared, next), final) ∈ support ((simulateQ handler (owner raw state)).run auxiliary)) :
    next = state ∧ ∃ control prekey oneTime kem,
      state.beacon.phase = .initSent control prekey oneTime kem ∧
      (some prepared, final) ∈ support
        ((simulateQ handler (prepare control state.beacon.identity prekey oneTime kem raw)).run auxiliary) := by
  cases active : state.beacon.phase with
  | initSent control prekey oneTime kem =>
      simp only [owner, active, simulateQ_bind, StateT.run_bind, mem_support_bind_iff,
        simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      obtain ⟨⟨reply, result⟩, reached, equal⟩ := supported
      have replyEq : some prepared = reply := congrArg (fun value => value.1.1) equal
      have finalEq : final = result := congrArg Prod.snd equal
      subst reply
      subst result
      have nextEq := congrArg (fun value => value.1.2) equal
      exact ⟨nextEq, control, prekey, oneTime, kem, rfl, reached⟩
  | _ => simp only [owner, active, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq, Option.some_ne_none, false_and] at supported

/-- At most twelve original typed callbacks precede core preparation, with every optional reply branch counted. -/
theorem collect_bound (identity : I) (prekey oneTime : D) (kem : K) (raw : Bytes) :
    (collect (X := X) (Response := Response) identity prekey oneTime kem raw).IsTotalQueryBound 12 := by
  unfold collect
  simp only [OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, OptionT.run_monadLift, Option.elimM, bind_map_left]
  repeat' first
    | trivial
    | rw [isTotalQueryBound_query_bind_iff]
    | constructor
    | intro reply; cases reply

/-- Every failed active attempt terminally aborts the original owner after retaining the actual preparation poststate; inactive failure has no callback effects. -/
theorem owner_failure {A : Type}
    (handler : QueryImpl (Spec I D K X Response) (StateT A ProbComp))
    (raw : Bytes) (state next : State I D K) (auxiliary final : A)
    (supported : ((none, next), final) ∈ support ((simulateQ handler (owner raw state)).run auxiliary)) :
    match state.beacon.phase with
    | .initSent control prekey oneTime kem =>
        next = abort control state ∧ (none, final) ∈ support
          ((simulateQ handler (prepare control state.beacon.identity prekey oneTime kem raw)).run auxiliary)
    | _ => next = state ∧ final = auxiliary := by
  cases active : state.beacon.phase with
  | initSent control prekey oneTime kem =>
      simp only [owner, active, simulateQ_bind, StateT.run_bind, mem_support_bind_iff,
        simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      obtain ⟨⟨reply, result⟩, reached, equal⟩ := supported
      have replyEq : none = reply := congrArg (fun value => value.1.1) equal
      have finalEq : final = result := congrArg Prod.snd equal
      subst reply
      subst result
      exact ⟨congrArg (fun value => value.1.2) equal, reached⟩
  | _ =>
      simp only [owner, active, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq, true_and] at supported
      exact supported

/-- The core-result stage performs exactly one ordinary shared-secret erasure callback on either outcome. -/
theorem afterInputs_bound (control : pqxdh.BeaconInitSent) (inputs : Inputs Response) :
    (afterInputs (I := I) (D := D) (K := K) (X := X) control inputs).IsTotalQueryBound 1 := by
  unfold afterInputs
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨by decide, fun _ => by trivial⟩

/-- Thirteen typed callbacks suffice for the original pre-root branch, including the erasure after preparation errors. -/
theorem prepare_bound (control : pqxdh.BeaconInitSent) (identity : I) (prekey oneTime : D)
    (kem : K) (raw : Bytes) :
    (prepare (X := X) (Response := Response) control identity prekey oneTime kem raw).IsTotalQueryBound 13 := by
  unfold prepare
  apply isTotalQueryBound_bind (collect_bound identity prekey oneTime kem raw) (n₂ := 1)
  intro result
  cases result with
  | none => trivial
  | some inputs => exact afterInputs_bound control inputs

/-- The outer inactive/abort/publication dispatch adds no primitive callback to the same thirteen-call allowance. -/
theorem owner_bound (raw : Bytes) (state : State I D K) :
    (owner (X := X) (Response := Response) raw state).IsTotalQueryBound 13 := by
  cases active : state.beacon.phase with
  | initSent control prekey oneTime kem =>
      simp only [owner, active, bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
      exact prepare_bound control state.beacon.identity prekey oneTime kem raw
  | _ => simp only [owner, active]; trivial

/-- Any complete private continuation pays its own allowance after the original pre-root work and actual owner update. -/
theorem continueWith_bound {Result : Type} (raw : Bytes) (state : State I D K)
    (next : Option (Prepared Response) → State I D K → OracleComp (Spec I D K X Response) Result)
    (qNext : Nat) (bounded : ∀ prepared nextState, (next prepared nextState).IsTotalQueryBound qNext) :
    (continueWith raw state next).IsTotalQueryBound (13 + qNext) := by
  exact isTotalQueryBound_bind (owner_bound raw state) (fun result => bounded result.1 result.2)

/-- Actual private callback work is charged in the same stateful execution, with no resource transport through evaluated equality. -/
theorem owner_interpreted_bound {A ι : Type} {base : OracleSpec ι}
    (handler : QueryImpl (Spec I D K X Response) (StateT A (OracleComp base)))
    (predicate : base.Domain → Prop) [DecidablePred predicate]
    (qCall : Nat) (bounded : ∀ query auxiliary, ((handler query).run auxiliary).IsQueryBoundP predicate qCall)
    (raw : Bytes) (state : State I D K) (auxiliary : A) :
    ((simulateQ handler (owner raw state)).run auxiliary).IsQueryBoundP predicate (13 * qCall) := by
  have bound := FinitePartitionQueryBounds.weighted_bound (fun (_ : (Spec I D K X Response).Domain) => ())
    (fun _ => qCall) (fun _ => 13) handler predicate (owner raw state)
    (fun kind => by cases kind; simpa only [IsTotalQueryBound, IsQueryBoundP, not_true_eq_false,
      false_or, ite_true] using owner_bound (X := X) (Response := Response) raw state)
    (fun query current => bounded query current) auxiliary
  simpa only [Finset.univ_unique, Finset.sum_singleton, Nat.mul_comm] using bound

end BeaconcryptCore.Computational.PqxdhBeaconPhase2Preparation

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Preparation.normalPrepare_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Preparation.normalPrepare_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Preparation.abort_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Preparation.abort_fields

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Preparation.owner_inactive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Preparation.owner_inactive

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Preparation.afterInputs_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Preparation.afterInputs_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Preparation.owner_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Preparation.owner_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Preparation.continueWith_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Preparation.continueWith_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Preparation.afterInputs_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Preparation.afterInputs_origin

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Preparation.prepare_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Preparation.prepare_origin

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Preparation.owner_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Preparation.owner_success

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Preparation.collect_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Preparation.collect_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Preparation.owner_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Preparation.owner_failure

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Preparation.afterInputs_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Preparation.afterInputs_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Preparation.prepare_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Preparation.prepare_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Preparation.owner_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Preparation.owner_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Preparation.continueWith_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Preparation.continueWith_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPhase2Preparation.owner_interpreted_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPhase2Preparation.owner_interpreted_bound
