import BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeletonTools
import BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconOpaqueFinishRouter

/-!
# The grouped Beacon finish (item 2, stage S1b, first part)

This module restates the router-free branch `PqxdhRegistrationJointBeaconOpaqueFinishRouter.freeRouterBranch` (stage S0b) so that every Beacon finish reaches the native layer as one request for its private root and the whole continuation after it. In the router-free branch the marked Beacon owner sends its private root request (DH coordinates and decapsulation handle) and then, one by one, the requests of the continuation after the root (initial ratchet derivation, application reply, raw opening). The grouped branch sends one request carrying the prepared state of the finish (`Pending`); the native layer answers it by the private root interpreter followed by the native continuation on the shared commitment cache (`groupNative`). This is the form in which the services skeleton of stage S1b can hand the continuation after a hidden root to the service `hiddenAfter`.

Two further program equalities are folded in. The encapsulation-hiding wrapper `hide` of the resumed client is dropped, because the outer actual encapsulator interprets the same requests in place (`PqxdhRegistrationJointKemEncapsulation.forward_actual`). The main theorem `opaqueBranch_grouped` states that the opaque raw-ordinal branch of theorem T6 equals `groupedBranch`. These are program equalities; they charge nothing. The candidate is still an argument of the Server's private resumption interpreter and of the private Beacon root interpreter `markedRoot`, and still the 32-byte suffix of the Extract-table cache keys that both read; stage S1b moves these reads below the interpreter stack, and stage S1c removes the candidate from the cache keys.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton

open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhRegistrationJointKemObserverFree PqxdhRegistrationJointBeaconOpaqueFinish

/-! ### The grouped Beacon owner and client -/

section Client

open PqxdhRegistrationJointBundle (Identity Key)
open PqxdhJointGapDh (ScalarBytes)
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The prepared state of a Beacon finish at its private root: the response, ciphertext, ephemeral value, metadata, and the root's DH coordinates with the decapsulation handle. -/
abbrev Pending (Response : Type) := PqxdhBeaconPhase2Shared.Prepared Response Shared

/-- One request per prepared Beacon finish: the private root and the whole continuation after it. -/
abbrev GroupSpec (Response : Type) : OracleSpec (Pending Response) :=
  fun _ => Option PqxdhBeaconPhase2Publication.Staged

/-- The native-layer interface of the grouped client: the source's command interface and the grouped finish request. -/
abbrev GSpec (KemSK Response : Type) := PqxdhRegistrationJointServiceSchedule.Spec KemSK Response + GroupSpec Response

/-- The Beacon preparation interface with the opaque decapsulation handle. -/
abbrev PreSpec (Response : Type) := PqxdhBeaconPhase2Shared.Spec Identity ScalarBytes Key Nat Response Shared

/-- The grouped owner's interface: preparation requests and the grouped finish request. -/
abbrev OwnerSpec (Response : Type) := PreSpec Response + GroupSpec Response

/-- The opaque-handle Beacon owner `PqxdhBeaconPhase2Shared.owner` with its private root request and the continuation after it sent as one grouped request. The preparation, the phase check, every rejection and the final publication are those of the owner. -/
noncomputable def groupedOwner (raw : Pqxdh.Bytes) (state : PqxdhRegistrationJointBundle.Owner) :
    OracleComp (OwnerSpec Response) (Option Pqxdh.Bytes × PqxdhRegistrationJointBundle.Owner) :=
  match state.beacon.phase with
  | .initSent control prekey oneTime kem => do
      let prepared ← simulateQ (fun query => ((OwnerSpec Response).query (.inl query) : OracleComp (OwnerSpec Response) _) :
          QueryImpl (PreSpec Response) (OracleComp (OwnerSpec Response)))
        (PqxdhBeaconPhase2Shared.prepare control state.beacon.identity prekey oneTime kem raw)
      match prepared with
      | none => pure (PqxdhBeaconPhase2Publication.finish control state none)
      | some prepared => do
          let staged ← ((OwnerSpec Response).query (.inr prepared) : OracleComp (OwnerSpec Response) _)
          pure (PqxdhBeaconPhase2Publication.finish control state staged)
  | _ => pure (none, state)

/-- Forward a private-pool request to the grouped interface. -/
def groupedPoolLift : QueryImpl (PqxdhLiveKemBirth.Spec KemSK) (OracleComp (GSpec KemSK Response)) :=
  fun query => (GSpec KemSK Response).query (.inl (.inl (.inl query)))

/-- The grouped owner's callbacks: the marked preparation through the private pool, and the grouped request unchanged. -/
noncomputable def groupedCompiler (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (selected : Nat)
    (challenge : MlKem768Ciphertext) : QueryImpl (OwnerSpec Response) (OracleComp (GSpec KemSK Response))
  | .inl query => simulateQ groupedPoolLift (markedPreparation setup codec selected challenge query)
  | .inr pending => (GSpec KemSK Response).query (.inr pending)

/-- The grouped Beacon finish: the grouped owner in place of the opaque-handle owner, with the same owner lookup and reinstallation. -/
noncomputable def groupedFinish (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (selected : Nat)
    (challenge : MlKem768Ciphertext) (address : Nat) (raw : Pqxdh.Bytes) :
    StateT (List EncodedEntry) (OracleComp (GSpec KemSK Response)) (Option Pqxdh.Bytes) := fun owners =>
  match owners[address]? with
  | none => pure (none, owners)
  | some entry =>
    (fun result => (result.1, owners.set address (entry.1, entry.2.1, result.2))) <$>
      simulateQ (groupedCompiler setup codec selected challenge) (groupedOwner raw entry.2.2)

/-- Lift a source client step to the grouped interface. -/
def groupedLift : QueryImpl (PqxdhRegistrationJointServiceSchedule.Spec KemSK Response)
    (OracleComp (GSpec KemSK Response)) :=
  fun query => (GSpec KemSK Response).query (.inl query)

/-- A source client step on the grouped interface. -/
def liftGrouped {α : Type} (work : PqxdhRegistrationJointServiceSchedule.Client KemSK Response α) :
    StateT (List EncodedEntry) (OracleComp (GSpec KemSK Response)) α :=
  fun owners => simulateQ groupedLift (work.run owners)

/-- The source client with the grouped Beacon finish; every other request is the source's. -/
noncomputable def groupedClient (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (selected : Nat)
    (challenge : MlKem768Ciphertext) :
    QueryImpl (PqxdhRegistrationJointRevealSchedule.Spec KemSK)
      (StateT (List EncodedEntry) (OracleComp (GSpec KemSK Response)))
  | .inl (.inr (.finish address raw)) => groupedFinish setup codec selected challenge address raw
  | query => liftGrouped (PqxdhRegistrationJointRevealSchedule.client setup codec query)

end Client

/-! ### The grouped native finish -/

section Native

open PqxdhServerAuthNative (NativeGame NativeState eraseObservers)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- A computation on the shared commitment cache, run by the native layer (`PqxdhServerAuthNative.nativeCtx`). -/
def ctxClient {α : Type} (work : StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp α) :
    PqxdhRegistrationJointKemEncapsulation.Client KemSK α :=
  PqxdhRegistrationJointKemEncapsulation.lift (PqxdhRegistrationJointOpenBackend.native
    (PqxdhServerAuthNative.nativeCtx work))

/-- The Beacon tail callbacks after the root, on the shared commitment cache: the native Beacon callbacks of the source (`PqxdhServerAuthExperiment.beaconNative`); a root request, which the continuation never sends, has no reply. -/
noncomputable def tailNative (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    QueryImpl (PqxdhBeaconPhase2Shared.TailSpec Response Shared)
      (StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp)
  | .inl query => beaconNative setup codec (.inl query)
  | .inr (.root _) => pure none
  | .inr (.initial request) => beaconNative setup codec (.inr (.initial request))
  | .inr (.application response) => beaconNative setup codec (.inr (.application response))

/-- The native answer to a grouped finish request: the private root interpreter, then the native continuation after the root on the shared commitment cache. -/
noncomputable def groupNative (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (candidate : MlKemSharedSecret) (pending : Pending Response) :
    PqxdhRegistrationJointKemEncapsulation.Client KemSK (Option PqxdhBeaconPhase2Publication.Staged) := do
  let root ← PqxdhRegistrationJointKemEncapsulation.lift (PqxdhRegistrationJointOpenBackend.native
    (markedRoot setup.hmac candidate pending.root))
  match root with
  | none => pure none
  | some root => ctxClient (simulateQ (tailNative setup codec)
      (PqxdhBeaconPhase2Shared.afterRoot codec.frameRead pending root))

/-- The native backend of the grouped interface: the source backend, and the grouped finish. -/
noncomputable def groupedImpl (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (candidate : MlKemSharedSecret) :
    QueryImpl (GSpec KemSK Response) (PqxdhRegistrationJointKemEncapsulation.Client KemSK) :=
  PqxdhRegistrationJointKemEncapsulation.impl setup codec checks identityIndex publicIdentity +
    groupNative setup codec candidate

theorem ctxClient_run {α : Type} (work : StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp α)
    (state : NativeState KemSK) :
    (ctxClient (KemSK := KemSK) work).run state =
      simulateQ PqxdhRegistrationJointKemEncapsulation.forward (PqxdhLiveKemBirth.coins
        ((fun result => (result.1, (state.1, { state.2 with ctx := result.2.2 }))) <$>
          work.run ((), state.2.ctx))) :=
  rfl

theorem ctxClient_pure {α : Type} (value : α) :
    ctxClient (KemSK := KemSK) (pure value : StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp α) = pure value := by
  apply StateT.ext
  intro state
  simp [ctxClient_run, PqxdhLiveKemBirth.coins]

theorem ctxClient_bind {α β : Type} (work : StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp α)
    (next : α → StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp β) :
    ctxClient (KemSK := KemSK) (work >>= next) = ctxClient work >>= fun value => ctxClient (next value) := by
  apply StateT.ext
  intro state
  simp only [StateT.run_bind, ctxClient_run, PqxdhLiveKemBirth.coins, simulateQ_map, simulateQ_bind, map_bind,
    bind_map_left]

/-- The native layer runs a simulated shared-cache program as the simulation of its native steps. -/
theorem simulate_ctxClient {ι' α : Type} {spec : OracleSpec ι'}
    (handler : QueryImpl spec (StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp)) (work : OracleComp spec α) :
    simulateQ (fun query => ctxClient (KemSK := KemSK) (handler query)) work = ctxClient (simulateQ handler work) := by
  induction work using OracleComp.inductionOn with
  | pure value => simp [ctxClient_pure]
  | query_bind query next ih => simp only [simulateQ_bind, simulateQ_spec_query, ctxClient_bind, ih]

/-- Two tail handlers that agree on every request other than the root give the same continuation after the root. -/
theorem afterRoot_congr {m : Type → Type} [Monad m] [LawfulMonad m]
    (first second : QueryImpl (PqxdhBeaconPhase2Shared.TailSpec Response Shared) m)
    (raw : ∀ query, first (.inl query) = second (.inl query))
    (initial : ∀ request, first (.inr (.initial request)) = second (.inr (.initial request)))
    (application : ∀ response, first (.inr (.application response)) = second (.inr (.application response)))
    (decode : RawCtxReceive.FrameDecoder) (pending : Pending Response) (root : PqxdhBeaconPhase2Preparation.Word32) :
    simulateQ first (PqxdhBeaconPhase2Shared.afterRoot decode pending root) =
      simulateQ second (PqxdhBeaconPhase2Shared.afterRoot decode pending root) := by
  have rawEq : ∀ {β : Type} (work : OracleComp RawCtxSourceOpen.NativeSpec β),
      simulateQ first (simulateQ PqxdhBeaconPhase2Shared.rawLift work) =
        simulateQ second (simulateQ PqxdhBeaconPhase2Shared.rawLift work) := by
    intro _ work
    rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
    congr 1
    funext query
    simp only [QueryImpl.apply_compose, PqxdhBeaconPhase2Shared.rawLift, simulateQ_spec_query]
    exact raw query
  unfold PqxdhBeaconPhase2Shared.afterRoot
  simp only [simulateQ_bind, simulateQ_spec_query, initial, application]
  refine bind_congr fun response => bind_congr fun reply => ?_
  cases reply with
  | none => rfl
  | some bytes =>
      simp only [simulateQ_bind, simulateQ_pure]
      rw [rawEq]

/-- The marked native backend never reads the analysis observers. -/
theorem markedImpl_neverRead (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (candidate : MlKemSharedSecret) :
    NeverRead eraseObservers (markedImpl setup codec checks identityIndex publicIdentity candidate) := by
  intro query state
  rcases query with query | secrets
  · exact impl_neverRead setup codec checks identityIndex publicIdentity query state
  · refine lift_native_neverRead ?_ state
    unfold markedRoot
    split
    · exact oblivious_sourceRoot _ _
    · exact oblivious_pure _

/-- The marked backend answers the compiled continuation after a root by the native continuation on the shared commitment cache. -/
theorem after_native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (candidate : MlKemSharedSecret) (selected : Nat)
    (challenge : MlKem768Ciphertext) (pending : Pending Response) (root : PqxdhBeaconPhase2Preparation.Word32) :
    simulateQ (markedImpl setup codec checks identityIndex publicIdentity candidate)
        (simulateQ (markedCompiler setup codec selected challenge)
          (simulateQ PqxdhBeaconPhase2Shared.tailLift (PqxdhBeaconPhase2Shared.afterRoot codec.frameRead pending root))) =
      ctxClient (simulateQ (tailNative setup codec) (PqxdhBeaconPhase2Shared.afterRoot codec.frameRead pending root)) := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose, ← simulate_ctxClient]
  apply afterRoot_congr
  · intro query
    simp only [QueryImpl.apply_compose, PqxdhBeaconPhase2Shared.tailLift, simulateQ_spec_query, markedCompiler]
    rfl
  · intro request
    simp only [QueryImpl.apply_compose, PqxdhBeaconPhase2Shared.tailLift, simulateQ_spec_query, markedCompiler]
    rfl
  · intro response
    simp only [QueryImpl.apply_compose, PqxdhBeaconPhase2Shared.tailLift, simulateQ_spec_query, markedCompiler]
    rfl

/-- The compiled tail of a prepared finish: the private root request, then the compiled continuation. -/
theorem compiled_tail (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (selected : Nat)
    (challenge : MlKem768Ciphertext) (pending : Pending Response) :
    simulateQ (markedCompiler setup codec selected challenge)
        (simulateQ PqxdhBeaconPhase2Shared.tailLift (PqxdhBeaconPhase2Shared.tail codec.frameRead pending)) =
      ((MarkedSpec KemSK Response).query (.inr pending.root) : OracleComp (MarkedSpec KemSK Response) _) >>=
        fun root => match root with
          | none => pure none
          | some root => simulateQ (markedCompiler setup codec selected challenge)
              (simulateQ PqxdhBeaconPhase2Shared.tailLift (PqxdhBeaconPhase2Shared.afterRoot codec.frameRead pending root)) := by
  unfold PqxdhBeaconPhase2Shared.tail
  simp only [simulateQ_bind, simulateQ_spec_query, PqxdhBeaconPhase2Shared.tailLift]
  refine bind_congr fun root => ?_
  cases root <;> rfl

/-- The erased marked backend on the compiled tail of a prepared finish is the erased grouped finish. -/
theorem tail_grouped (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (candidate : MlKemSharedSecret) (selected : Nat)
    (challenge : MlKem768Ciphertext) (pending : Pending Response) :
    simulateQ (eraseImpl eraseObservers (markedImpl setup codec checks identityIndex publicIdentity candidate))
        (simulateQ (markedCompiler setup codec selected challenge)
          (simulateQ PqxdhBeaconPhase2Shared.tailLift (PqxdhBeaconPhase2Shared.tail codec.frameRead pending))) =
      eraseImpl eraseObservers (groupedImpl setup codec checks identityIndex publicIdentity candidate) (.inr pending) := by
  apply StateT.ext
  intro state
  have first : (eraseImpl eraseObservers (markedImpl setup codec checks identityIndex publicIdentity candidate)
      (.inr pending.root)).run state = Prod.map id eraseObservers <$> (PqxdhRegistrationJointKemEncapsulation.lift
        (PqxdhRegistrationJointOpenBackend.native (markedRoot setup.hmac candidate pending.root))).run
          (eraseObservers state) := rfl
  have second : (eraseImpl eraseObservers (groupedImpl setup codec checks identityIndex publicIdentity candidate)
      (.inr pending)).run state =
      Prod.map id eraseObservers <$> (groupNative setup codec candidate pending).run (eraseObservers state) := rfl
  rw [compiled_tail, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, first, second, groupNative,
    StateT.run_bind]
  simp only [bind_map_left, map_bind]
  refine bind_congr fun result => ?_
  rcases result with ⟨_ | root, after⟩
  · simp
  · dsimp only [Prod.map_apply, id_eq]
    rw [← run_erase eraseObservers eraseObservers_idem _
      (markedImpl_neverRead setup codec checks identityIndex publicIdentity candidate),
      after_native setup codec checks identityIndex publicIdentity candidate selected challenge pending root]

/-- The erased marked backend on the compiled opaque-handle owner equals the erased grouped backend on the compiled grouped owner. -/
theorem owner_grouped (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (candidate : MlKemSharedSecret) (selected : Nat)
    (challenge : MlKem768Ciphertext) (raw : Pqxdh.Bytes) (state : PqxdhRegistrationJointBundle.Owner) :
    simulateQ (eraseImpl eraseObservers (markedImpl setup codec checks identityIndex publicIdentity candidate))
        (simulateQ (markedCompiler setup codec selected challenge)
          (PqxdhBeaconPhase2Shared.owner codec.frameRead raw state)) =
      simulateQ (eraseImpl eraseObservers (groupedImpl setup codec checks identityIndex publicIdentity candidate))
        (simulateQ (groupedCompiler setup codec selected challenge) (groupedOwner raw state)) := by
  have pool : ∀ {α : Type} (work : OracleComp (PqxdhLiveKemBirth.Spec KemSK) α),
      simulateQ (eraseImpl eraseObservers (markedImpl setup codec checks identityIndex publicIdentity candidate))
          (simulateQ (markedPoolLift (Response := Response)) work) =
        simulateQ (eraseImpl eraseObservers (groupedImpl setup codec checks identityIndex publicIdentity candidate))
          (simulateQ (groupedPoolLift (Response := Response)) work) := by
    intro _ work
    rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
    congr 1
  have prep : ∀ {α : Type} (work : OracleComp (PreSpec Response) α),
      simulateQ (eraseImpl eraseObservers (markedImpl setup codec checks identityIndex publicIdentity candidate))
          (simulateQ (markedCompiler setup codec selected challenge) (simulateQ PqxdhBeaconPhase2Shared.preLift work)) =
        simulateQ (eraseImpl eraseObservers (groupedImpl setup codec checks identityIndex publicIdentity candidate))
          (simulateQ (groupedCompiler setup codec selected challenge)
            (simulateQ (fun query => ((OwnerSpec Response).query (.inl query) : OracleComp (OwnerSpec Response) _) :
              QueryImpl (PreSpec Response) (OracleComp (OwnerSpec Response))) work)) := by
    intro _ work
    rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose,
      ← QueryImpl.simulateQ_compose]
    congr 1
    funext query
    simp only [QueryImpl.apply_compose, PqxdhBeaconPhase2Shared.preLift, simulateQ_spec_query, markedCompiler,
      groupedCompiler]
    exact pool _
  unfold PqxdhBeaconPhase2Shared.owner groupedOwner
  rcases phase : state.beacon.phase with _ | _ | ⟨control, prekey, oneTime, kem⟩ | _ | _
  all_goals try simp only [simulateQ_pure]
  simp only [simulateQ_bind, prep]
  refine bind_congr fun prepared => ?_
  cases prepared with
  | none => simp only [simulateQ_pure]
  | some pending =>
      simp only [simulateQ_bind, simulateQ_pure, tail_grouped setup codec checks identityIndex publicIdentity
        candidate selected challenge pending, simulateQ_spec_query, groupedCompiler]
      rfl

/-- The marked Beacon finish and the grouped Beacon finish have the same erased interpretation. -/
theorem finish_grouped (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (candidate : MlKemSharedSecret) (selected : Nat)
    (challenge : MlKem768Ciphertext) (address : Nat) (raw : Pqxdh.Bytes)
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) :
    simulateQ (eraseImpl eraseObservers (markedImpl setup codec checks identityIndex publicIdentity candidate))
        ((markedFinish setup codec selected challenge address raw).run owners) =
      simulateQ (eraseImpl eraseObservers (groupedImpl setup codec checks identityIndex publicIdentity candidate))
        ((groupedFinish setup codec selected challenge address raw).run owners) := by
  simp only [markedFinish, groupedFinish, StateT.run]
  cases owners[address]? with
  | none => simp
  | some entry =>
      simp only [simulateQ_map]
      rw [owner_grouped]

/-- Every step of the marked client and of the grouped client has the same erased interpretation. -/
theorem client_grouped (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (candidate : MlKemSharedSecret) (selected : Nat)
    (challenge : MlKem768Ciphertext) (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) :
    simulateQ (eraseImpl eraseObservers (markedImpl setup codec checks identityIndex publicIdentity candidate))
        ((markedClient setup codec selected challenge query).run owners) =
      simulateQ (eraseImpl eraseObservers (groupedImpl setup codec checks identityIndex publicIdentity candidate))
        ((groupedClient setup codec selected challenge query).run owners) := by
  have lifted : ∀ {α : Type} (work : PqxdhRegistrationJointServiceSchedule.Client KemSK Response α),
      simulateQ (eraseImpl eraseObservers (markedImpl setup codec checks identityIndex publicIdentity candidate))
          ((liftClient work).run owners) =
        simulateQ (eraseImpl eraseObservers (groupedImpl setup codec checks identityIndex publicIdentity candidate))
          ((liftGrouped work).run owners) := by
    intro _ work
    change simulateQ _ (simulateQ markedLift (work.run owners)) = simulateQ _ (simulateQ groupedLift (work.run owners))
    rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
    congr 1
  rcases query with (coin | request) | read
  · exact lifted _
  · cases request with
    | finish address raw =>
        exact finish_grouped setup codec checks identityIndex publicIdentity candidate selected challenge address raw
          owners
    | _ => exact lifted _
  · exact lifted _

end Native

/-! ### The grouped branch -/

section Assembly

open PqxdhServerAuthNative (NativeState eraseObservers)
open PqxdhRegistrationJointKemEncapsulation (actual)
open PqxdhRegistrationJointKemCommands (SourceSpec Outcome)
open PqxdhRegistrationJointKemResume (ResultState)
open PqxdhRegistrationJointAcceptCutTag (Tag decideTag)
open PqxdhRegistrationJointAcceptKemCut (tagged hide)
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry)
open PqxdhRegistrationJointKemOpaqueResume (liftImpl clientNative forwardClient)
open PqxdhRegistrationJointKemRawOpaque (OpaqueContext toContext sourcePreOpaque opaqueBranch)
open PqxdhRegistrationJointBeaconOpaqueFinishRouter (placeholder freeRouterPost freeRouterBranch)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X R : Type}

/-- The grouped resumption: the Server's private resumption, then the rest of the tagged client under the grouped client and the grouped native backend, without the encapsulation-hiding wrapper. -/
noncomputable def groupedResume (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (consumed : List Pqxdh.Bytes) (native : NativeState KemSK) (owners : List EncodedEntry)
    (next : Option Nat → OracleComp (SourceSpec KemSK) X) (selected : Nat)
    (ciphertext : MlKem768Ciphertext) (candidate : MlKemSharedSecret) :
    OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) (Outcome KemSK R) := do
  let answer ← (simulateQ (eraseImpl eraseObservers (liftImpl clientNative setup native.2.sessions candidate forwardClient))
    (PqxdhRegistrationJointKemOpaqueResume.resume setup codec checks identityIndex publicIdentity raw value ephemeral
      (PqxdhAcceptedRegistration.ciphertextArray ciphertext) .challenge native.2 consumed)).run (eraseObservers native)
  (simulateQ (eraseImpl eraseObservers (groupedImpl setup codec checks identityIndex publicIdentity candidate))
    ((simulateQ (groupedClient setup codec selected ciphertext) (tagged observe raw next answer.1)).run owners)).run
      answer.2

/-- Under the actual encapsulator, the marked resumption equals the grouped resumption. -/
theorem resume_grouped (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (consumed : List Pqxdh.Bytes) (native : NativeState KemSK) (owners : List EncodedEntry)
    (next : Option Nat → OracleComp (SourceSpec KemSK) X) (selected : Nat)
    (ciphertext : MlKem768Ciphertext) (candidate : MlKemSharedSecret) :
    simulateQ (actual setup) (markedResume setup codec checks identityIndex publicIdentity observe raw value ephemeral
        consumed native owners next selected ciphertext candidate) =
      simulateQ (actual setup) (groupedResume setup codec checks identityIndex publicIdentity observe raw value
        ephemeral consumed native owners next selected ciphertext candidate) := by
  unfold markedResume groupedResume
  simp only [simulateQ_bind]
  refine bind_congr fun answer => ?_
  rw [hide, PqxdhRegistrationJointKemEncapsulation.forward_actual]
  congr 1
  exact congrArg (fun work => StateT.run work answer.2)
    (layered _ _ _ _ (client_grouped setup codec checks identityIndex publicIdentity candidate selected ciphertext)
      _ owners)

/-- The grouped postchallenge step: the router-free postchallenge step with the grouped resumption. -/
noncomputable def groupedPost (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (count : Nat) (selected : Fin (count + 1))
    (transcript : MlKemChallengeTranscript (OpaqueContext Reader KemSK A X count)) (candidate : MlKemSharedSecret) :
    OracleComp (MlKemCCAOracleSpec baseSpec) (ResultState KemSK A Bool count) := do
  match transcript.context with
  | .ready created others (some (.pending raw value ephemeral consumed native owners next)) state _ =>
    if value.keys.pqKey = transcript.publicKey then
      let reached ← (((simulateQ (eraseOptionImpl eraseJoint
          (PqxdhDynamicKemJointRouter.post setup.joint setup.kem selected.val
            (PqxdhDynamicKemRouter.selectedReservation selected transcript.publicKey others)
            transcript.ciphertext placeholder))
        (simulateQ (actual setup) (groupedResume setup codec checks created.server.server.metadata.identityIndex
          created.publicIdentity (decideTag decision) raw value ephemeral consumed native owners next selected.val
          transcript.ciphertext candidate))).run).run (eraseJoint state))
      pure (toContext setup codec checks decision transcript.context, some reached)
    else pure (toContext setup codec checks decision transcript.context, none)
  | _ => pure (toContext setup codec checks decision transcript.context, none)

/-- The router-free postchallenge step equals the grouped postchallenge step. -/
theorem post_grouped (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (count : Nat) (selected : Fin (count + 1))
    (transcript : MlKemChallengeTranscript (OpaqueContext Reader KemSK A X count)) (candidate : MlKemSharedSecret) :
    freeRouterPost setup codec checks decision count selected transcript candidate =
      groupedPost setup codec checks decision count selected transcript candidate := by
  obtain ⟨publicKey, ciphertext, context⟩ := transcript
  cases context with
  | failed state => rfl
  | ready created others cut state runtime =>
    cases cut with
    | none => rfl
    | some cut =>
      cases cut with
      | complete outcome => rfl
      | pending raw value ephemeral consumed native owners next =>
        by_cases active : value.keys.pqKey = publicKey
        · simp only [freeRouterPost, groupedPost, active, ↓reduceIte, resume_grouped]
        · simp only [freeRouterPost, groupedPost, active, ↓reduceIte]

/-- The grouped branch: the router-free branch with the grouped postchallenge step. -/
noncomputable def groupedBranch (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (real : Bool) : ProbComp Bool := do
  let chosen ← simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen
  let context ← sourcePreOpaque (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
    selected index chosen
  let encapsulated ← simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps chosen.1)
  let uniform ← $ᵗ MlKemSharedSecret
  PqxdhRegistrationJointKemGame.decision <$> PqxdhDynamicKemPost.evaluate setup.baseImpl setup.kem chosen.2
    encapsulated.1 (groupedPost setup codec checks decision count selected ⟨chosen.1, encapsulated.1, context⟩
      (if real then encapsulated.2 else uniform))

/-- Stage S1b, first part. The opaque raw-ordinal branch (theorem T6) equals the grouped branch, as programs and for both values of the branch bit: every Beacon finish reaches the native layer as one request for its private root and the continuation after it, and the encapsulation-hiding wrapper of the resumed client is dropped. -/
theorem opaqueBranch_grouped (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (real : Bool) :
    opaqueBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        real =
      groupedBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
        index real := by
  rw [PqxdhRegistrationJointBeaconOpaqueFinishRouter.opaqueBranch_freeRouter]
  unfold freeRouterBranch groupedBranch
  simp only [post_grouped]

end Assembly

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.ctxClient_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.ctxClient_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.ctxClient_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.ctxClient_pure

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.ctxClient_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.ctxClient_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.simulate_ctxClient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.simulate_ctxClient

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.afterRoot_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.afterRoot_congr

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.markedImpl_neverRead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.markedImpl_neverRead

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.after_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.after_native

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.compiled_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.compiled_tail

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.tail_grouped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.tail_grouped

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.owner_grouped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.owner_grouped

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.finish_grouped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.finish_grouped

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.client_grouped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.client_grouped

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.resume_grouped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.resume_grouped

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.post_grouped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.post_grouped

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.opaqueBranch_grouped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.opaqueBranch_grouped
