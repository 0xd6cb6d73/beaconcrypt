import BeaconcryptCore.Computational.PqxdhInitialSourceRandom
import BeaconcryptCore.Computational.PqxdhSelectedPostDisclosure
import BeaconcryptCore.Computational.PqxdhSelectedMessageBuilder
import BeaconcryptCore.Computational.PqxdhSelectedMessageBeacon
import BeaconcryptCore.Computational.RawCtxSelectedMessageKdf
import BeaconcryptCore.Computational.PqxdhSelectedMessageSourceFreshness
import BeaconcryptCore.Computational.PqxdhPreparedPrefixCallbacks
import BeaconcryptCore.Computational.PqxdhSourceSharedPreparation
/-!
The first selected record (number one, no parent entry) of the randomized stage-one source is simulated exactly by a selected-material world. The native run uses the fixed private patch of the production stream at the actual selected directional root with the explicit full76 response `(key, nonce, next)`. The selected run executes the same first Server builder with opaque selected-message kernels, followed by the stopped-source post interpreter `PqxdhSelectedPostDisclosure.normal`, extended only by the original private origin and publication transcript. `nativeView` is an explicit projection: the post bit, the displayed native front (kernel and history interpretation under `key`), the transcript, and the retained shared, identity and root-cache state; the added source-local store, input list and audit are dropped.

The per-request bridges are exact for every state: record and reveal requests use `RawCtxSelectedMessageStopping.native_schedule` and the generic native family step; selector and external callbacks use the source-local lifting; Beacon finishes keep their installation marker through the kernel map; the builder uses the native and selected Ready-builder realizations. The only change of state space is a pure projection, first between auxiliary types of the functional backend (which never inspects its auxiliary component) and then from the selected local state to the retained native state. The generic theorem assumes only that the native external callbacks are the lifted source-local callbacks; for the actual prepared source this equation is proved, so the prepared corollary has no premise. No probability bound, freshness premise or secrecy assumption is introduced; the selected key appears only in the mathematical source interpreter and in the explicit projection.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhSelectedFirstRecord
open PqxdhJointKdfGame RawCtxSelectedParentTable

/-- Mapping a state-passing computation maps only its returned value. -/
theorem state_map_apply {σ α β : Type} (f : α → β) (work : StateT σ ProbComp α) (state : σ) :
    (f <$> work) state = (fun result => (f result.1, result.2)) <$> work state :=
  StateT.run_map f work state

/-- A total interpreter lifted to the optional-reply interface returns every reply and the final result in `some`. -/
theorem optional_total {ι σ Result : Type} {spec : OracleSpec ι} (impl : QueryImpl spec (StateT σ ProbComp))
    (client : OracleComp spec Result) :
    simulateQ ((fun query => some <$> impl query) : QueryImpl (RawCtxSelectedFamilyNonceCoupling.Optional spec) (StateT σ ProbComp))
      (RawCtxSelectedFamilyNonceCoupling.optionalClient client) = some <$> simulateQ impl client := by
  have handler : ((fun query => some <$> impl query) : QueryImpl (RawCtxSelectedFamilyNonceCoupling.Optional spec) (StateT σ ProbComp)) =
      fun query => ((OptionT.lift (impl query) : OptionT (StateT σ ProbComp) _)).run := by
    funext query
    simp only [OptionT.run_lift, bind_pure_comp]
  rw [handler, RawCtxSelectedFamilyNonceCoupling.optional_client]
  induction client using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, OptionT.run_pure, map_pure]
  | query_bind query continuation ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, OptionT.run_lift, Option.elimM, map_bind,
      bind_assoc, pure_bind]
    exact bind_congr fun reply => ih reply

/-- Apply a function to the auxiliary component of the shared primitive state. -/
def auxMap {X Y : Type} (f : X → Y) (state : RawCtxSharedPrimitive.SharedState X) :
    RawCtxSharedPrimitive.SharedState Y := (f state.1, state.2)

/-- The shared opening service never inspects its auxiliary component. -/
theorem native_aux {X Y : Type} (c : Pqxdh.Crypto) (f : X → Y)
    (query : RawCtxSourceOpen.NativeSpec.Domain) (state : RawCtxSharedPrimitive.SharedState X) :
    Prod.map id (auxMap f) <$> (RawCtxSharedPrimitive.nativeImpl c (fun request => pure (RawCtxSourceHkdf.response c request)) query).run state =
      (RawCtxSharedPrimitive.nativeImpl c (fun request => pure (RawCtxSourceHkdf.response c request)) query).run (auxMap f state) := by
  rcases query with request | (bytes | input)
  · rfl
  · simp [RawCtxSharedPrimitive.nativeImpl, RawCtxSharedPrimitive.openingImpl, auxMap, StateT.run]
  · simp [RawCtxSharedPrimitive.nativeImpl, RawCtxSharedPrimitive.openingImpl, auxMap, StateT.run]

/-- The fixed-source protocol backend never inspects or changes its auxiliary component. -/
theorem protocol_aux {X Y : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (f : X → Y)
    (query : RawCtxServerServices.BackendSpec.Domain) (state : RawCtxSharedPrimitive.SharedState X) :
    Prod.map id (auxMap f) <$> (RawCtxProtocolBackend.backend source writer query).run state =
      (RawCtxProtocolBackend.backend source writer query).run (auxMap f state) := by
  rcases query with coin | (request | view)
  · simp [RawCtxProtocolBackend.backend, RawCtxServerServices.backendImpl, auxMap, StateT.run]
  · simp only [RawCtxProtocolBackend.backend, RawCtxServerServices.backendImpl, RawCtxMixedShared.sharedImpl,
      QueryImpl.compose, StateT.run]
    exact map_run_simulateQ_eq_of_query_map_eq _ _ (auxMap f) (native_aux source.crypto f) _ state
  · simp [RawCtxProtocolBackend.backend, RawCtxServerServices.backendImpl, auxMap, StateT.run]

/-- The retained-table functional backend commutes with every auxiliary projection. -/
theorem backend_aux {X Y : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (f : X → Y)
    (query : RawCtxServerServices.BackendSpec.Domain) (state : RawCtxSharedPrimitive.SharedState X) :
    Prod.map id (auxMap f) <$> (RawCtxFunctionalFamily.backend (A := X) source writer prior query).run state =
      (RawCtxFunctionalFamily.backend (A := Y) source writer prior query).run (auxMap f state) := by
  simp only [RawCtxFunctionalFamily.backend, QueryImpl.compose]
  refine map_run_simulateQ_eq_of_query_map_eq _ _ (auxMap f) (fun request before => ?_) _ state
  rcases request with request | request
  · exact protocol_aux source writer f request before
  · change Prod.map id (auxMap f) <$> (pure (prior request, before) : ProbComp _) = pure (prior request, auxMap f before)
    simp only [map_pure, Prod.map_apply, id_eq]

/-- Every backend program commutes with every auxiliary projection. -/
theorem backend_program_aux {X Y Result : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (f : X → Y)
    (work : OracleComp RawCtxServerServices.BackendSpec Result) (state : RawCtxSharedPrimitive.SharedState X) :
    Prod.map id (auxMap f) <$> (simulateQ (RawCtxFunctionalFamily.backend (A := X) source writer prior) work).run state =
      (simulateQ (RawCtxFunctionalFamily.backend (A := Y) source writer prior) work).run (auxMap f state) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ (auxMap f) (backend_aux source writer prior f) work state

/-- The retained pending family interpreter commutes with every auxiliary projection. -/
theorem retained_aux {X Y : Type} {S B : Nat} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (f : X → Y)
    (query : (RawCtxPendingFamilyLiveQueries.Spec RatchetChain S B).Domain) (state : RawCtxSharedPrimitive.SharedState X) :
    Prod.map id (auxMap f) <$> (RawCtxPendingRetainedExecution.retained (A := X) source writer prior query).run state =
      (RawCtxPendingRetainedExecution.retained (A := Y) source writer prior query).run (auxMap f state) := by
  have identity : ∀ Z : Type, (RawCtxFunctionalFamily.backend (A := Z) source writer prior ∘ₛ
      fun request => (RawCtxServerServices.BackendSpec.query request : OracleComp RawCtxServerServices.BackendSpec _)) =
      RawCtxFunctionalFamily.backend (A := Z) source writer prior := by
    intro Z
    funext request
    exact simulateQ_spec_query _ request
  have split : ∀ Z : Type, RawCtxPendingRetainedExecution.retained (A := Z) (S := S) (B := B) source writer prior =
      RawCtxFunctionalFamily.backend (A := Z) source writer prior ∘ₛ
        RawCtxPendingFamilyNative.handler (serverCount := S) (beaconCount := B)
          (fun request => (RawCtxServerServices.BackendSpec.query request : OracleComp RawCtxServerServices.BackendSpec _)) := by
    intro Z
    rw [RawCtxPendingBackendInterpretation.family_compose, identity Z]
    rfl
  rw [split X, split Y]
  exact backend_program_aux source writer prior f _ state

/-- A retained family callback carries every auxiliary value through unchanged. -/
theorem retained_frame {X : Type} {S B : Nat} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (query : (RawCtxPendingFamilyLiveQueries.Spec RatchetChain S B).Domain)
    (auxiliary : X) (cache : CtxRomAuth.CtxRO.QueryCache) :
    (RawCtxPendingRetainedExecution.retained (A := X) source writer prior query).run (auxiliary, cache) =
      (fun result => (result.1, (auxiliary, result.2.2))) <$>
        (RawCtxPendingRetainedExecution.retained (A := Unit) source writer prior query).run ((), cache) := by
  have lifted := retained_aux source writer prior (fun _ : Unit => auxiliary) query ((), cache)
  simpa only [auxMap, Prod.map_def, id_eq] using lifted.symm

section Low
open PqxdhNativeSharedPrefix PqxdhInitialBeaconAmbient
variable {ι I D K X Response Shared A N C : Type} {extra : OracleSpec ι} {S B : Nat}
variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))

/-- The native low-level pending interface interpreted over the selected source-local state. -/
noncomputable def lowered (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior) :
    QueryImpl (PqxdhInitialPendingPost.Spec extra RatchetChain I D K X Response Shared S B)
      (StateT (RawCtxSharedPrimitive.SharedState (Local A N C)) ProbComp)
  | .inl query => RawCtxPendingRetainedExecution.retained (A := Local A N C) source writer prior query
  | .inr query => PqxdhSelectedInitialOwnerCompiler.sourceExternal pre application initial selector aux query

/-- The native retained state read from the selected local state: shared auxiliary and hash cache, private identity state and root cache. -/
def retainedOf (state : RawCtxSharedPrimitive.SharedState (Local A N C)) :
    PqxdhInitialNativeRetained.RetainedState A N C :=
  ((state.1.shared, state.2), (state.1.privateState, state.1.roots))

/-- The native external callbacks obtained by lifting the source-local callbacks, with the audited initializer. -/
noncomputable def lifted : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response Shared) (Ambient A N C) :=
  PqxdhInitialNativeAudit.external (fun request => localLift (pre request)) (fun reply => localLift (application reply))
    (fun secrets => localLift (initial secrets)) (fun request => localLift (selector request)) (fun request => localLift (aux request))

/-- Each low-level callback over the selected local state projects to the retained native callback. -/
theorem low_step (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (query : (PqxdhInitialPendingPost.Spec extra RatchetChain I D K X Response Shared S B).Domain)
    (state : RawCtxSharedPrimitive.SharedState (Local A N C)) :
    Prod.map id retainedOf <$> (lowered pre application initial selector aux source writer prior query).run state =
      (PqxdhInitialNativeRetained.retained source writer prior (lifted pre application initial selector aux) query).run
        (retainedOf state) := by
  rcases query with query | query
  · rcases state with ⟨current, cache⟩
    change Prod.map id retainedOf <$> (RawCtxPendingRetainedExecution.retained (A := Local A N C) source writer prior query).run (current, cache) =
      (fun result => (result.1, (result.2, (current.privateState, current.roots)))) <$>
        (RawCtxPendingRetainedExecution.retained (A := A) source writer prior query).run (current.shared, cache)
    rw [retained_frame source writer prior query current cache,
      retained_frame source writer prior query current.shared cache]
    simp only [Functor.map_map, Prod.map_def, id_eq, retainedOf]
  · have native := PqxdhSelectedInitialOwnerCompiler.external_native pre application initial selector aux source writer 0 S B query state
    have erased := PqxdhInitialNativeAudit.query_erase (S := S) (B := B) source writer 0 (fun request => localLift (pre request))
      (fun reply => localLift (application reply)) (fun secrets => localLift (initial secrets))
      (fun request => localLift (selector request)) (fun request => localLift (aux request)) (.inr query) (attach state.1 state.2)
    rw [← native, Functor.map_map] at erased
    have projected := congrArg (fun work => Prod.map id PqxdhInitialNativeRetained.project <$> work) erased
    rw [PqxdhInitialNativeLog.external_handler, Functor.map_map, Functor.map_map] at projected
    simp only [PqxdhInitialNativeRetained.project, attach, Prod.map_def, id_eq, StateT.run] at projected
    simp only [lowered, PqxdhInitialNativeRetained.retained, retainedOf, lifted, Prod.map_def, id_eq, StateT.run]
    exact projected

/-- The whole low-level program over the selected local state projects to the retained native execution. -/
theorem low_program {Result : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (work : OracleComp (PqxdhInitialPendingPost.Spec extra RatchetChain I D K X Response Shared S B) Result)
    (state : RawCtxSharedPrimitive.SharedState (Local A N C)) :
    Prod.map id retainedOf <$> (simulateQ (lowered pre application initial selector aux source writer prior) work).run state =
      (simulateQ (PqxdhInitialNativeRetained.retained source writer prior (lifted pre application initial selector aux)) work).run
        (retainedOf state) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ retainedOf (low_step pre application initial selector aux source writer prior) work state

/-- Interpreting the forwarded pending owner calls gives the native calls over the selected local state. -/
theorem lowered_calls (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior) :
    RawCtxGenericOwnerInterpretation.interpretedCalls
        (lowered (S := S) (B := B) pre application initial selector aux source writer prior) PqxdhInitialPendingPost.calls =
      RawCtxGenericNativeCalls.calls (RawCtxFunctionalFamily.native (A := Local A N C) source writer prior) := by
  have forward : (lowered (S := S) (B := B) pre application initial selector aux source writer prior ∘ₛ
      PqxdhInitialPendingPost.primitiveForward) =
      RawCtxPendingNativeCalls.pending (RawCtxFunctionalFamily.native (A := Local A N C) source writer prior)
        (RawCtxFunctionalFamily.backend source writer prior ∘ₛ RawCtxServerServices.publicLift) := by
    funext query
    simp only [QueryImpl.compose, PqxdhInitialPendingPost.primitiveForward, simulateQ_spec_query]
    rfl
  rw [← RawCtxPendingNativeCalls.calls_interpretation _ (RawCtxFunctionalFamily.backend source writer prior ∘ₛ RawCtxServerServices.publicLift),
    ← forward]
  simp only [PqxdhInitialPendingPost.calls, RawCtxGenericOwnerInterpretation.interpretedCalls, QueryImpl.simulateQ_compose]

end Low

section Front
variable {M P I D K : Type} {S B : Nat}
open PqxdhSecretInputKdf

/-- Refined native kernels representing a concrete protocol state. -/
def fromNative (state : RawCtxProtocolReveals.State M P I D K S B) :
    RawCtxGenericFamilyLive.State (PqxdhInitialPendingPost.KernelOf RatchetChain) M P I D K S B :=
  (RawCtxGenericRoleFamily.fromRoles ConcreteRatchetKernel.refined state.1, state.2)

/-- The native pending role family displayed by a selected-material role family. -/
def rolesOf (key : RootOutput) (state : RawCtxSelectedMessageReveals.State M P I D K S B) :
    RawCtxGenericFamilyLive.State (PqxdhInitialPendingPost.KernelOf RatchetChain) M P I D K S B :=
  fromNative (RawCtxSelectedMessageReveals.nativeState key state)

/-- The refined representation reconstructs every concrete native kernel. -/
theorem native_fromNative (state : RawCtxProtocolReveals.State M P I D K S B) :
    RawCtxGenericFamilyLive.nativeState ConcreteRatchetKernel.mk (fromNative state) = state :=
  Prod.ext (RawCtxGenericRoleFamily.roundtrip ConcreteRatchetKernel.refined ConcreteRatchetKernel.mk
    (fun kernel => by cases kernel; rfl) state.1) rfl

/-- Concrete projection followed by refined representation is the identity on refined role families. -/
theorem fromNative_native
    (state : RawCtxGenericFamilyLive.State (PqxdhInitialPendingPost.KernelOf RatchetChain) M P I D K S B) :
    fromNative (RawCtxGenericFamilyLive.nativeState ConcreteRatchetKernel.mk state) = state := by
  have phase : ∀ {DhPair KemPair : Type} (value : RawCtxBeaconLifecycle.Phase DhPair KemPair (PqxdhInitialPendingPost.KernelOf RatchetChain)),
      RawCtxGenericRoleStorage.mapPhase ConcreteRatchetKernel.refined (RawCtxGenericRoleStorage.mapPhase ConcreteRatchetKernel.mk value) = value := by
    intro DhPair KemPair value
    cases value <;> rfl
  rcases state with ⟨⟨servers, beacons⟩, history⟩
  simp only [fromNative, RawCtxGenericFamilyLive.nativeState, RawCtxGenericRoleFamily.fromRoles,
    RawCtxGenericRoleFamily.nativeRoles, RawCtxGenericRoleStorage.fromServer, RawCtxGenericRoleStorage.nativeServer,
    RawCtxGenericRoleStorage.fromBeacon, RawCtxGenericRoleStorage.nativeBeacon, phase, Option.map_map, Function.comp_def]
  simp

/-- The native pending front displayed by a selected-material front. -/
def frontOf (key : RootOutput) (front : PqxdhSelectedPostCompiler.Front M P I D K S B) : PqxdhInitialOriginPostPath.Front M P I D K S B :=
  ⟨rolesOf key front.roles, front.controls, front.consumed⟩

/-- Every displayed role is the selected role under the explicit kernel interpretation. -/
theorem rolesOf_roles (key : RootOutput) (state : RawCtxSelectedMessageReveals.State M P I D K S B) :
    (rolesOf key state).1 = RawCtxGenericRoleFamily.mapRoles (PqxdhSelectedMessageBeacon.interpretKernel key) state.1 := by
  have phase : ∀ {DhPair KemPair : Type} (value : RawCtxBeaconLifecycle.Phase DhPair KemPair RawCtxSelectedMessageReveals.Kernel),
      RawCtxGenericRoleStorage.mapPhase ConcreteRatchetKernel.refined
        (RawCtxGenericRoleStorage.mapPhase (RawCtxSelectedMessageReveals.nativeKernel key) value) =
      RawCtxGenericRoleStorage.mapPhase (PqxdhSelectedMessageBeacon.interpretKernel key) value := by
    intro DhPair KemPair value
    cases value <;> rfl
  simp only [rolesOf, fromNative, RawCtxSelectedMessageReveals.nativeState, RawCtxGenericRoleFamily.fromRoles,
    RawCtxGenericRoleFamily.nativeRoles, RawCtxGenericRoleFamily.mapRoles, RawCtxGenericRoleStorage.fromServer,
    RawCtxGenericRoleStorage.nativeServer, RawCtxGenericRoleStorage.mapServer,
    RawCtxGenericRoleStorage.fromBeacon, RawCtxGenericRoleStorage.nativeBeacon, RawCtxGenericRoleStorage.mapBeacon,
    phase, Option.map_map, Function.comp_def]
  rfl

/-- The displayed native history is the interpreted selected history. -/
theorem rolesOf_history (key : RootOutput) (state : RawCtxSelectedMessageReveals.State M P I D K S B) :
    (rolesOf key state).2 = RawCtxSelectedMessageFreshness.interpretHistory key state.2 := rfl

/-- Installing an interpreted Beacon commutes with the displayed front, including the timestamp tick. -/
theorem frontOf_install (key : RootOutput) (index : Fin B) (front : PqxdhSelectedPostCompiler.Front M P I D K S B)
    (updated : PqxdhSelectedInitialOwnerCompiler.Beacon I D K) :
    frontOf key (PqxdhSelectedPostCompiler.install index front updated) =
      PqxdhInitialPendingPost.install index (frontOf key front)
        (RawCtxGenericRoleStorage.mapBeacon (PqxdhSelectedMessageBeacon.interpretKernel key) updated) := by
  simp only [frontOf, PqxdhInitialPendingPost.install, PqxdhSelectedPostCompiler.install]
  congr 1
  apply Prod.ext
  · rw [rolesOf_roles, rolesOf_roles]
    simp only [RawCtxGenericRoleFamily.mapRoles]
    congr 1
    funext beacon
    by_cases same : beacon = index
    · subst beacon
      simp only [Function.update_self]
    · simp only [Function.update_of_ne same]
  · rfl

/-- Kernel interpretation of a generic registration-publication state. -/
def pubMap {Kernel Other Consumed : Type} (interpret : Kernel → Other)
    (state : PqxdhInitialGenericPublication.State Kernel M P Consumed) : PqxdhInitialGenericPublication.State Other M P Consumed :=
  ⟨(RawCtxGenericRoleStorage.mapServer interpret ⟨state.server, 0⟩).server, state.identityKeyId, state.control, state.consumed⟩

/-- Record the consumed registration identifier of the Ready input in the selected front. -/
def consumeFront (index : Fin S) (ready : PqxdhPrivateAcceptedRoot.Ready) (before : PqxdhSelectedPostCompiler.Front M P I D K S B) :
    PqxdhSelectedPostCompiler.Front M P I D K S B :=
  { before with consumed := Function.update before.consumed index ready.consumed.consumed }

/-- The selected Server's generic publication state read from the selected front. -/
def selectedServer (sender : M → Std.U64) (index : Fin S) (before : PqxdhSelectedPostCompiler.Front M P I D K S B) :
    PqxdhInitialGenericPublication.State RawCtxSelectedMessageReveals.Kernel M P (List Pqxdh.Bytes) :=
  ⟨(before.roles.1.1 index).server, sender (before.roles.1.1 index).server.metadata, before.controls index, before.consumed index⟩

/-- Install an updated Server publication state in the selected front. -/
def installServer (index : Fin S) (before : PqxdhSelectedPostCompiler.Front M P I D K S B)
    (updated : PqxdhInitialGenericPublication.State RawCtxSelectedMessageReveals.Kernel M P (List Pqxdh.Bytes)) :
    PqxdhSelectedPostCompiler.Front M P I D K S B :=
  { roles := ((Function.update before.roles.1.1 index { before.roles.1.1 index with server := updated.server }, before.roles.1.2), before.roles.2)
    controls := Function.update before.controls index updated.control
    consumed := Function.update before.consumed index updated.consumed }

/-- Reinstall a builder result in the selected front; failures keep the consumed front. -/
def reinstallServer (index : Fin S) (before : PqxdhSelectedPostCompiler.Front M P I D K S B)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhInitialGenericPublication.State RawCtxSelectedMessageReveals.Kernel M P (List Pqxdh.Bytes))) :
    RustM (Option PqxdhServerRegistrationPublication.Response) × PqxdhSelectedPostCompiler.Front M P I D K S B :=
  match result with
  | .ok value => (.ok value.1, installServer index before value.2)
  | .fail error => (.fail error, before)
  | .div => (.div, before)

/-- Consuming the registration identifier commutes with the displayed front. -/
theorem frontOf_consume (key : RootOutput) (index : Fin S) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (before : PqxdhSelectedPostCompiler.Front M P I D K S B) :
    PqxdhInitialPendingBuilder.consume index ready (frontOf key before) = frontOf key (consumeFront index ready before) := rfl

/-- Reading the Server publication state commutes with kernel interpretation. -/
theorem frontOf_selected (key : RootOutput) (sender : M → Std.U64) (index : Fin S)
    (before : PqxdhSelectedPostCompiler.Front M P I D K S B) :
    PqxdhInitialPendingBuilder.selected sender index (frontOf key before) =
      pubMap (PqxdhSelectedMessageBeacon.interpretKernel key) (selectedServer sender index before) := by
  simp only [PqxdhInitialPendingBuilder.selected, frontOf, rolesOf_roles, selectedServer, pubMap]
  rfl

/-- Installing an interpreted Server state commutes with the displayed front. -/
theorem frontOf_installServer (key : RootOutput) (index : Fin S) (before : PqxdhSelectedPostCompiler.Front M P I D K S B)
    (updated : PqxdhInitialGenericPublication.State RawCtxSelectedMessageReveals.Kernel M P (List Pqxdh.Bytes)) :
    PqxdhInitialPendingBuilder.install index (frontOf key before) (pubMap (PqxdhSelectedMessageBeacon.interpretKernel key) updated) =
      frontOf key (installServer index before updated) := by
  simp only [PqxdhInitialPendingBuilder.install, frontOf, installServer]
  congr 1
  apply Prod.ext
  · rw [rolesOf_roles, rolesOf_roles]
    simp only [RawCtxGenericRoleFamily.mapRoles]
    congr 1
    funext server
    by_cases same : server = index
    · subst server
      simp only [Function.update_self, pubMap, RawCtxGenericRoleStorage.mapServer]
    · simp only [Function.update_of_ne same]
  · rfl

end Front

section Steps
open PqxdhNativeSharedPrefix PqxdhInitialBeaconAmbient PqxdhSecretInputKdf PqxdhFullSecretInputKdf RawCtxSelectedParentEntry
variable {ι M P I D K X Response Shared A N C : Type} {extra : OracleSpec ι} {S B : Nat}
variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)

local notation "table" => RawCtxSelectedMessageDriver.privateTable prior parent target (RawCtxSelectedMessageKdf.response key nonce next)

/-- Forwarded live requests are the retained native family interpreter over the selected local state. -/
theorem live_forward :
    (lowered (extra := extra) (X := X) (Response := Response) (S := S) (B := B) pre application initial selector aux source writer table ∘ₛ
      PqxdhInitialPendingPost.liveForward) =
      RawCtxPendingFamilyNative.handler (RawCtxFunctionalFamily.backend (A := Local A N C) source writer table) := by
  funext query
  simp only [QueryImpl.compose, PqxdhInitialPendingPost.liveForward, simulateQ_spec_query]
  rfl

/-- One selected-material record or reveal request is the native pending record request after the explicit kernel and history interpretation. -/
theorem record_step (request : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (roles : RawCtxSelectedMessageReveals.State M P I D K S B) (shared : RawCtxSharedPrimitive.SharedState (Local A N C)) :
    (simulateQ (lowered (extra := extra) (X := X) (Response := Response) pre application initial selector aux source writer table)
      (simulateQ PqxdhInitialPendingPost.liveForward
        ((RawCtxPendingFamilyLiveQueries.compiler sender route decode request).run (rolesOf key roles)))).run shared =
      (fun result => ((result.1, rolesOf key result.2.1), result.2.2)) <$>
        (RawCtxSelectedMessageStopping.normal
          (RawCtxSelectedMessageStopping.sourceRecord source writer prior parent key target nonce next sender route decode) key request).run
            (roles, shared) := by
  rw [← QueryImpl.simulateQ_compose, live_forward]
  have interpreted := RawCtxPendingFamilyLiveQueries.step_interpretation
    (RawCtxPendingNativeCalls.pending (RawCtxFunctionalFamily.native (A := Local A N C) source writer table)
      (RawCtxFunctionalFamily.backend source writer table ∘ₛ RawCtxServerServices.publicLift))
    (RawCtxGenericFamilyRead.nativeReader ConcreteRatchetKernel.mk) sender route decode request (rolesOf key roles)
  rw [RawCtxPendingNativeCalls.calls_interpretation, RawCtxPendingNativeCalls.public_interpretation] at interpreted
  have live := RawCtxGenericFamilyNative.live_step ConcreteRatchetKernel.mk
    (RawCtxGenericNativeCalls.calls (RawCtxFunctionalFamily.native (A := Local A N C) source writer table))
    (RawCtxFunctionalFamily.backend source writer table)
    (RawCtxGenericNativeCalls.receive_realized _) (RawCtxGenericNativeCalls.send_realized _)
    sender route decode request (rolesOf key roles)
  rw [rolesOf, native_fromNative] at live
  have schedule := RawCtxSelectedMessageStopping.native_schedule source writer prior parent key target nonce next sender route decode
    (((RawCtxProtocolReveals.SourceSpec S B).query request) : OracleComp (RawCtxProtocolReveals.SourceSpec S B) _) (roles, shared)
  simp only [simulateQ_spec_query] at schedule
  change (simulateQ (RawCtxPendingFamilyLiveQueries.handler
      (RawCtxPendingNativeCalls.pending (RawCtxFunctionalFamily.native (A := Local A N C) source writer table)
        (RawCtxFunctionalFamily.backend source writer table ∘ₛ RawCtxServerServices.publicLift))
      (RawCtxGenericFamilyRead.nativeReader ConcreteRatchetKernel.mk))
    ((RawCtxPendingFamilyLiveQueries.compiler sender route decode request).run (rolesOf key roles))).run shared = _
  rw [interpreted]
  have restore : (RawCtxGenericFamilyLive.impl (RawCtxGenericNativeCalls.calls (RawCtxFunctionalFamily.native (A := Local A N C) source writer table))
      (RawCtxFunctionalFamily.backend source writer table ∘ₛ RawCtxServerServices.publicLift)
      (RawCtxGenericFamilyRead.nativeReader ConcreteRatchetKernel.mk) sender route decode request).run (rolesOf key roles) =
      Prod.map id fromNative <$> (Prod.map id (RawCtxGenericFamilyLive.nativeState ConcreteRatchetKernel.mk) <$>
        (RawCtxGenericFamilyLive.impl (RawCtxGenericNativeCalls.calls (RawCtxFunctionalFamily.native (A := Local A N C) source writer table))
          (RawCtxFunctionalFamily.backend source writer table ∘ₛ RawCtxServerServices.publicLift)
          (RawCtxGenericFamilyRead.nativeReader ConcreteRatchetKernel.mk) sender route decode request).run (rolesOf key roles)) := by
    simp only [Functor.map_map, Prod.map_def, id_eq, fromNative_native, Prod.mk.eta, id_map']
  rw [restore, rolesOf, ← live, StateT.run_map, schedule]
  simp only [Functor.map_map, RawCtxSelectedMessageStopping.nativeOutput, Prod.map_def, id_eq, rolesOf]

/-- The selected-material Beacon finish with its private installation marker. -/
noncomputable def selectedFinish {Origin : Type} (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (raw : Pqxdh.Bytes)
    (beacon : PqxdhSelectedInitialOwnerCompiler.Beacon I D K) :
    StateT (RawCtxSharedPrimitive.SharedState (Local A N C)) ProbComp
      (PqxdhInitialFinishOrigin.Result RawCtxSelectedMessageReveals.Kernel Origin I D K) :=
  PqxdhInitialFinishOrigin.owner mark
    (fun query => PqxdhSelectedInitialOwnerCompiler.sourceExternal (extra := extra) pre application initial selector aux (.inl query))
    (PqxdhSelectedMessageBeacon.materialCalls source writer prior parent key target nonce next)
    (fun reply => PqxdhSelectedInitialOwnerCompiler.sourceExternal (extra := extra) pre application initial selector aux (.inr (.inl reply)))
    (fun secrets => Option.map PqxdhSelectedMessageBeacon.knownKernel <$>
      PqxdhSelectedInitialOwnerCompiler.sourceExternal (extra := extra) pre application initial selector aux (.inr (.inr (.inl secrets))))
    decode raw beacon

/-- The native pending finish, interpreted over the selected local state, is the selected-material finish after kernel interpretation, including its installation marker. -/
theorem finish_step {Origin : Type} (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (raw : Pqxdh.Bytes)
    (beacon : PqxdhSelectedInitialOwnerCompiler.Beacon I D K) :
    simulateQ (lowered (extra := extra) (X := X) (Response := Response) (S := S) (B := B) pre application initial selector aux source writer table)
      (PqxdhInitialFinishOrigin.owner mark PqxdhInitialPendingPost.preForward PqxdhInitialPendingPost.calls
        PqxdhInitialPendingPost.applicationForward PqxdhInitialPendingPost.initialForward decode raw
        (RawCtxGenericRoleStorage.mapBeacon (PqxdhSelectedMessageBeacon.interpretKernel key) beacon)) =
      Prod.map (Prod.map id (RawCtxGenericRoleStorage.mapBeacon (PqxdhSelectedMessageBeacon.interpretKernel key))) id <$>
        selectedFinish pre application initial selector aux source writer prior parent key target nonce next decode mark raw beacon := by
  rw [PqxdhInitialOriginPost.owner_interpretation, lowered_calls]
  have preparation : (lowered (extra := extra) (X := X) (Response := Response) (S := S) (B := B) pre application initial selector aux source writer table ∘ₛ
      PqxdhInitialPendingPost.preForward) =
      fun query => PqxdhSelectedInitialOwnerCompiler.sourceExternal (extra := extra) pre application initial selector aux (.inl query) := by
    funext query
    simp only [QueryImpl.compose, PqxdhInitialPendingPost.preForward, simulateQ_spec_query]
    rfl
  have getter : (fun reply => simulateQ (lowered (extra := extra) (X := X) (Response := Response) (S := S) (B := B) pre application initial selector aux source writer table)
      (PqxdhInitialPendingPost.applicationForward reply)) =
      fun reply => PqxdhSelectedInitialOwnerCompiler.sourceExternal (extra := extra) pre application initial selector aux (.inr (.inl reply)) := by
    funext reply
    simp only [PqxdhInitialPendingPost.applicationForward, simulateQ_spec_query]
    rfl
  have initializer : (fun secrets => simulateQ (lowered (extra := extra) (X := X) (Response := Response) (S := S) (B := B) pre application initial selector aux source writer table)
      (PqxdhInitialPendingPost.initialForward secrets)) =
      fun secrets => PqxdhSelectedInitialOwnerCompiler.sourceExternal (extra := extra) pre application initial selector aux (.inr (.inr (.inl secrets))) := by
    funext secrets
    simp only [PqxdhInitialPendingPost.initialForward, simulateQ_spec_query]
    rfl
  rw [preparation, getter, initializer]
  apply PqxdhInitialFinishOrigin.owner_map
  · exact PqxdhSelectedMessageBeacon.receive_map source writer prior parent key target nonce next
  · intro secrets
    simp only [Functor.map_map, Option.map_map, Function.comp_def, PqxdhSelectedMessageBeacon.known_roundtrip]
    change _ = Option.map id <$> _
    simp only [Option.map_id, id_map]

/-- Erasing the private installation marker gives the selected source finish used by the stopped post interpreter. -/
theorem finish_erase {Origin : Type} (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (raw : Pqxdh.Bytes)
    (beacon : PqxdhSelectedInitialOwnerCompiler.Beacon I D K) :
    Prod.fst <$> selectedFinish pre application initial selector aux source writer prior parent key target nonce next decode mark raw beacon =
      simulateQ (PqxdhSelectedInitialOwnerCompiler.source (extra := extra) pre application initial selector aux source writer prior parent key target nonce next decode)
        (PqxdhSelectedInitialOwnerCompiler.owner raw beacon) := by
  rw [selectedFinish, PqxdhInitialFinishOrigin.erase, PqxdhSelectedInitialOwnerCompiler.owner_source]

/-- Selected source state together with the private origin and publication transcript. -/
abbrev Traced (M P I D K A N C : Type) (S B : Nat) :=
  PqxdhSelectedPostCompiler.SourceState M P I D K A N C S B × PqxdhInitialOriginPost.Trace Bool S B

/-- The selected post interpreter with the original private origin and publication transcript. -/
noncomputable def tracedPlain (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool) :
    QueryImpl (PqxdhInitialGenericPost.Spec extra S B) (StateT (Traced M P I D K A N C S B) ProbComp)
  | .inl (.inl request) => fun before =>
      (fun result => (result.1, (({ before.1.1 with roles := result.2.1 }, result.2.2),
          PqxdhInitialOriginPost.record before.2 request result.1))) <$>
        (RawCtxSelectedMessageStopping.normal
          (RawCtxSelectedMessageStopping.sourceRecord source writer prior parent key target nonce next sender route decode) key request).run
            (before.1.1.roles, before.1.2)
  | .inl (.inr request) => fun before =>
      (fun result => (result.1, ((before.1.1, result.2), before.2))) <$>
        (PqxdhSelectedInitialOwnerCompiler.sourceExternal (extra := extra) pre application initial selector aux
          (.inr (.inr (.inr (.inl request))))).run before.1.2
  | .inr (.finish index raw) => fun before =>
      (fun result => (result.1.1.1, ((PqxdhSelectedPostCompiler.install index before.1.1 result.1.1.2, result.2),
          PqxdhInitialOriginPost.finish before.2 index result.1.2))) <$>
        (selectedFinish pre application initial selector aux source writer prior parent key target nonce next decode mark raw
          (before.1.1.roles.1.2 index)).run before.1.2

/-- The traced selected post interpreter over the optional-reply interface of the stopped source. -/
noncomputable def traced (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool) :
    QueryImpl (PqxdhSelectedPostCompiler.Optional (PqxdhInitialGenericPost.Spec extra S B))
      (StateT (Traced M P I D K A N C S B) ProbComp) :=
  fun query before => (fun result => (some result.1, result.2)) <$>
    (tracedPlain pre application initial selector aux source writer prior parent key target nonce next sender route decode mark query).run before

/-- Erasing only the private transcript recovers the ordinary selected post interpreter. -/
theorem traced_erase (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool)
    (query : (PqxdhSelectedPostCompiler.Optional (PqxdhInitialGenericPost.Spec extra S B)).Domain)
    (before : Traced M P I D K A N C S B) :
    Prod.map id Prod.fst <$> (traced pre application initial selector aux source writer prior parent key target nonce next sender route decode mark query).run before =
      (PqxdhSelectedPostDisclosure.normal pre application initial selector aux source writer prior parent key target nonce next sender route decode query).run before.1 := by
  rcases query with (request | request) | ⟨index, raw⟩
  · simp only [traced, tracedPlain, PqxdhSelectedPostDisclosure.normal, StateT.run, Functor.map_map, Prod.map_def, id_eq]
  · simp only [traced, tracedPlain, PqxdhSelectedPostDisclosure.normal, PqxdhSelectedPostCompiler.original, StateT.run,
      Functor.map_map, Prod.map_def, id_eq]
  · simp only [traced, tracedPlain, PqxdhSelectedPostDisclosure.normal, PqxdhSelectedPostCompiler.original, StateT.run,
      Functor.map_map, Prod.map_def, id_eq]
    rw [← finish_erase pre application initial selector aux source writer prior parent key target nonce next decode (fun secrets => mark secrets) raw,
      state_map_apply, Functor.map_map]

local notation "interp" => PqxdhSelectedMessageBeacon.interpretKernel key
/-- Source-local registration publication callbacks over the selected local state. -/
noncomputable def serverAux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec
    (StateT (RawCtxSharedPrimitive.SharedState (Local A N C)) ProbComp) :=
  fun request => PqxdhSelectedInitialOwnerCompiler.sourceExternal (extra := extra) pre application initial selector aux
    (.inr (.inr (.inr (.inr request))))

/-- The selected-material first Server builder: the same consumed input, allocation and application gates, first seal and publication. -/
noncomputable def selectedBuild (initialKernel : RustM RawCtxSelectedMessageReveals.Kernel) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) :
    StateT (PqxdhSelectedPostCompiler.Front M P I D K S B) (StateT (RawCtxSharedPrimitive.SharedState (Local A N C)) ProbComp)
      (RustM (Option PqxdhServerRegistrationPublication.Response)) := fun before =>
  let current := consumeFront index ready before
  let input := selectedServer sender index current
  reinstallServer index current <$> PqxdhInitialGenericBuilder.readyBuild source
    (PqxdhSelectedMessageBeacon.materialCalls source writer prior parent key target nonce next) (serverAux pre application initial selector aux) initialKernel
    ⟨input.server.identity, input.identityKeyId⟩ ready metadata input

/-- Successive maps of a Rust result compose. -/
theorem rust_map_map {α β γ : Type} (f : α → β) (g : β → γ) (value : RustM α) :
    g <$> (f <$> value) = (g ∘ f) <$> value := by
  cases value <;> rfl

/-- Refined native kernels representing a concrete registration-publication state. -/
def publicationOf (state : PqxdhServerRegistrationPublication.State M P (List Pqxdh.Bytes)) :
    PqxdhInitialGenericPublication.State (PqxdhInitialPendingPost.KernelOf RatchetChain) M P (List Pqxdh.Bytes) :=
  ⟨(RawCtxGenericRoleStorage.fromServer ConcreteRatchetKernel.refined ⟨state.server, 0⟩).server,
    state.identityKeyId, state.control, state.consumed⟩

/-- The refined representation inverts the native registration-publication projection. -/
theorem publication_native
    (state : PqxdhInitialGenericPublication.State (PqxdhInitialPendingPost.KernelOf RatchetChain) M P (List Pqxdh.Bytes)) :
    publicationOf (PqxdhInitialGenericPublication.native ConcreteRatchetKernel.mk state) = state := by
  simp only [publicationOf, PqxdhInitialGenericPublication.native, RawCtxGenericRoleStorage.fromServer,
    RawCtxGenericRoleStorage.nativeServer, Option.map_map, Function.comp_def]
  simp

/-- Refined representation of a selected native projection is the selected kernel interpretation. -/
theorem publication_selected (key : RootOutput)
    (state : PqxdhInitialGenericPublication.State RawCtxSelectedMessageReveals.Kernel M P (List Pqxdh.Bytes)) :
    publicationOf (PqxdhInitialGenericPublication.native (RawCtxSelectedMessageReveals.nativeKernel key) state) =
      pubMap (PqxdhSelectedMessageBeacon.interpretKernel key) state := by
  simp only [publicationOf, PqxdhInitialGenericPublication.native, RawCtxGenericRoleStorage.fromServer,
    RawCtxGenericRoleStorage.nativeServer, pubMap, RawCtxGenericRoleStorage.mapServer, Option.map_map, Function.comp_def]
  rfl

/-- The complete Ready builder with native kernels is the selected-material builder after kernel interpretation. -/
theorem ready_map (initialKernel : RustM RawCtxSelectedMessageReveals.Kernel) (binding : pqxdh.ServerBinding)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (metadata : P)
    (state : PqxdhInitialGenericPublication.State RawCtxSelectedMessageReveals.Kernel M P (List Pqxdh.Bytes)) :
    PqxdhInitialGenericBuilder.readyBuild source
      (RawCtxGenericNativeCalls.calls (RawCtxFunctionalFamily.native (A := Local A N C) source writer table))
      (serverAux pre application initial selector aux)
      (interp <$> initialKernel) binding ready metadata (pubMap interp state) =
      Functor.map (Prod.map id (pubMap interp)) <$> PqxdhInitialGenericBuilder.readyBuild source
        (PqxdhSelectedMessageBeacon.materialCalls source writer prior parent key target nonce next)
        (serverAux pre application initial selector aux) initialKernel binding ready metadata state := by
  have native := PqxdhInitialGenericBuilder.ready_native source ConcreteRatchetKernel.mk
    (RawCtxGenericNativeCalls.calls (RawCtxFunctionalFamily.native (A := Local A N C) source writer table))
    (RawCtxFunctionalFamily.native (A := Local A N C) source writer table) (serverAux pre application initial selector aux)
    (RawCtxGenericNativeCalls.send_realized _) (interp <$> initialKernel) binding ready metadata (pubMap interp state)
  have selected := PqxdhSelectedMessageBuilder.ready_source (A := Local A N C) source writer prior parent key target nonce next
    (serverAux pre application initial selector aux) initialKernel binding ready metadata state
  have kernels : ConcreteRatchetKernel.mk <$> (interp <$> initialKernel) =
      RawCtxSelectedMessageReveals.nativeKernel key <$> initialKernel := by
    rw [rust_map_map]
    rfl
  have states : PqxdhInitialGenericPublication.native ConcreteRatchetKernel.mk (pubMap interp state) =
      PqxdhInitialGenericPublication.native (RawCtxSelectedMessageReveals.nativeKernel key) state := by
    simp only [PqxdhInitialGenericPublication.native, pubMap, RawCtxGenericRoleStorage.nativeServer,
      RawCtxGenericRoleStorage.mapServer, Option.map_map, Function.comp_def]
    rfl
  rw [kernels, states, selected] at native
  have left : ∀ result : RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhInitialGenericPublication.State (PqxdhInitialPendingPost.KernelOf RatchetChain) M P (List Pqxdh.Bytes)),
      Prod.map id publicationOf <$> (Prod.map id (PqxdhInitialGenericPublication.native ConcreteRatchetKernel.mk) <$> result) = result := by
    intro result
    cases result with
    | ok value => exact congrArg RustM.ok (Prod.ext rfl (publication_native value.2))
    | fail error => rfl
    | div => rfl
  have right : ∀ result : RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhInitialGenericPublication.State RawCtxSelectedMessageReveals.Kernel M P (List Pqxdh.Bytes)),
      Prod.map id publicationOf <$> (Prod.map id (PqxdhInitialGenericPublication.native (RawCtxSelectedMessageReveals.nativeKernel key)) <$> result) =
        Prod.map id (pubMap interp) <$> result := by
    intro result
    cases result with
    | ok value => exact congrArg RustM.ok (Prod.ext rfl (publication_selected key value.2))
    | fail error => rfl
    | div => rfl
  have restored := congrArg (fun work => Functor.map (Prod.map id publicationOf) <$> work) native
  simp only [Functor.map_map, left, right, id_map'] at restored
  exact restored.symm

/-- The original first Server builder, interpreted over the selected local state, is the selected-material builder under the displayed front. -/
theorem build_step (initialKernel : RustM RawCtxSelectedMessageReveals.Kernel) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (before : PqxdhSelectedPostCompiler.Front M P I D K S B) :
    simulateQ (lowered (extra := extra) (X := X) (Response := Response) pre application initial selector aux source writer table)
      ((PqxdhInitialPendingBuilder.build source (interp <$> initialKernel) sender index metadata ready).run (frontOf key before)) =
      Prod.map id (frontOf key) <$>
        (selectedBuild pre application initial selector aux source writer prior parent key target nonce next sender
          initialKernel index metadata ready).run before := by
  have auxiliary : (lowered (extra := extra) (X := X) (Response := Response) (S := S) (B := B) pre application initial selector aux source writer table ∘ₛ
      PqxdhInitialPendingPost.auxForward) = serverAux pre application initial selector aux := by
    funext request
    simp only [QueryImpl.compose, PqxdhInitialPendingPost.auxForward, simulateQ_spec_query]
    rfl
  rw [PqxdhInitialPendingBuilder.build_interpretation]
  simp only [PqxdhInitialPendingBuilder.interpretedBuild, StateT.run]
  rw [lowered_calls, auxiliary, frontOf_consume, frontOf_selected]
  have binding : (⟨(pubMap interp (selectedServer sender index (consumeFront index ready before))).server.identity,
      (pubMap interp (selectedServer sender index (consumeFront index ready before))).identityKeyId⟩ : pqxdh.ServerBinding) =
      ⟨(selectedServer sender index (consumeFront index ready before)).server.identity,
        (selectedServer sender index (consumeFront index ready before)).identityKeyId⟩ := rfl
  rw [binding, ready_map, Functor.map_map]
  simp only [selectedBuild, Functor.map_map]
  refine congrArg (fun function => function <$> _) (funext fun result => ?_)
  cases result with
  | ok value =>
    show PqxdhInitialPendingBuilder.reinstall index (frontOf key (consumeFront index ready before))
        (RustM.ok (value.1, pubMap interp value.2)) =
      Prod.map id (frontOf key) (reinstallServer index (consumeFront index ready before) (RustM.ok value))
    simp only [PqxdhInitialPendingBuilder.reinstall, reinstallServer, Prod.map, id, frontOf_installServer]
  | fail error => rfl
  | div => rfl

/-- The original native post compiler, with its low-level requests interpreted over the selected local state. -/
noncomputable def nativeFlat (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool) :
    QueryImpl (PqxdhInitialGenericPost.Spec extra S B)
      (StateT ((PqxdhInitialOriginPostPath.Front M P I D K S B × PqxdhInitialOriginPost.Trace Bool S B) ×
        RawCtxSharedPrimitive.SharedState (Local A N C)) ProbComp) :=
  ((lowered (X := X) (Response := Response) pre application initial selector aux source writer table).mapStateTBase
    (PqxdhInitialOriginPost.compiler mark sender route decode)).flattenStateT

/-- The native displayed front, transcript and selected local state of a traced selected state. -/
def tracedProj (key : RootOutput) (state : Traced M P I D K A N C S B) :
    (PqxdhInitialOriginPostPath.Front M P I D K S B × PqxdhInitialOriginPost.Trace Bool S B) ×
      RawCtxSharedPrimitive.SharedState (Local A N C) :=
  ((frontOf key state.1.1, state.2), state.1.2)

/-- Each traced selected post request is the original native post request after the explicit state interpretation. -/
theorem post_step (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool)
    (query : (PqxdhInitialGenericPost.Spec extra S B).Domain) (before : Traced M P I D K A N C S B) :
    Prod.map id (tracedProj key) <$>
      (tracedPlain pre application initial selector aux source writer prior parent key target nonce next sender route decode mark query).run before =
      (nativeFlat pre application initial selector aux source writer prior parent key target nonce next sender route decode mark query).run
        (tracedProj key before) := by
  rcases before with ⟨⟨front, shared⟩, trace⟩
  rcases query with (request | request) | ⟨index, raw⟩
  · have step := record_step pre application initial selector aux source writer prior parent key target nonce next sender route decode
      request front.roles shared
    simp only [StateT.run] at step
    simp only [nativeFlat, tracedProj, QueryImpl.flattenStateT, QueryImpl.mapStateTBase, PqxdhInitialOriginPost.compiler,
      tracedPlain, StateT.mk, StateT.run, bind_pure_comp, simulateQ_map, frontOf, state_map_apply, step, Functor.map_map]
    rfl
  · simp only [nativeFlat, tracedProj, QueryImpl.flattenStateT, QueryImpl.mapStateTBase, PqxdhInitialOriginPost.compiler,
      tracedPlain, StateT.mk, StateT.run, bind_pure_comp, simulateQ_map, state_map_apply, Functor.map_map,
      PqxdhInitialPendingPost.selectorForward, simulateQ_spec_query]
    rfl
  · have step := finish_step (S := S) (B := B) pre application initial selector aux source writer prior parent key target nonce next decode
      mark raw (front.roles.1.2 index)
    simp only [nativeFlat, tracedProj, QueryImpl.flattenStateT, QueryImpl.mapStateTBase, PqxdhInitialOriginPost.compiler,
      tracedPlain, StateT.mk, StateT.run, bind_pure_comp, simulateQ_map, state_map_apply, Functor.map_map]
    have beacon : (frontOf key front).roles.1.2 index =
        RawCtxGenericRoleStorage.mapBeacon (PqxdhSelectedMessageBeacon.interpretKernel key) (front.roles.1.2 index) := by
      simp only [frontOf]
      rw [rolesOf_roles]
      rfl
    rw [beacon, step, state_map_apply, Functor.map_map]
    refine congrArg (fun function => function <$> _) (funext fun result => ?_)
    simp only [Prod.map, tracedProj, frontOf_install, id]

/-- Every adaptive traced selected post client is the original native post client after the state interpretation. -/
theorem post_program {Result : Type} (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool)
    (work : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result) (before : Traced M P I D K A N C S B) :
    Prod.map id (tracedProj key) <$>
      (simulateQ (tracedPlain pre application initial selector aux source writer prior parent key target nonce next sender route decode mark) work).run before =
      (simulateQ (nativeFlat pre application initial selector aux source writer prior parent key target nonce next sender route decode mark) work).run
        (tracedProj key before) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ (tracedProj key)
    (post_step pre application initial selector aux source writer prior parent key target nonce next sender route decode mark) work before

/-- The optional-reply traced interpreter always answers and is the total traced interpreter wrapped in `some`. -/
theorem traced_total {Result : Type} (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool)
    (work : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result) (before : Traced M P I D K A N C S B) :
    (simulateQ (traced pre application initial selector aux source writer prior parent key target nonce next sender route decode mark)
      (RawCtxSelectedFamilyNonceCoupling.optionalClient work)).run before =
      (fun result => (some result.1, result.2)) <$>
        (simulateQ (tracedPlain pre application initial selector aux source writer prior parent key target nonce next sender route decode mark) work).run before := by
  have lifted : traced (M := M) (P := P) (I := I) (D := D) (K := K) (S := S) (B := B)
      pre application initial selector aux source writer prior parent key target nonce next sender route decode mark =
      fun query => some <$> tracedPlain pre application initial selector aux source writer prior parent key target nonce next sender route decode mark query := by
    funext query before
    rw [state_map_apply]
    rfl
  rw [lifted, optional_total, StateT.run_map]

/-- Erasing only the private transcript from a complete traced post client gives the stopped-source post client consumed by `PqxdhSelectedPostDisclosure.event_good`. -/
theorem traced_program_erase {Result : Type} (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool)
    (work : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result) (before : Traced M P I D K A N C S B) :
    Prod.map id Prod.fst <$>
      (simulateQ (traced pre application initial selector aux source writer prior parent key target nonce next sender route decode mark)
        (RawCtxSelectedFamilyNonceCoupling.optionalClient work)).run before =
      (simulateQ (PqxdhSelectedPostDisclosure.normal pre application initial selector aux source writer prior parent key target nonce next
        sender route decode) (RawCtxSelectedFamilyNonceCoupling.optionalClient work)).run before.1 :=
  map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst
    (traced_erase pre application initial selector aux source writer prior parent key target nonce next sender route decode mark) _ before

/-- The private transcript entry for the first Server response, read from the selected front. -/
def selectedAfter (before : PqxdhInitialOriginPost.Trace Bool S B) (front : PqxdhSelectedPostCompiler.Front M P I D K S B)
    (index : Fin S) (origin : Bool) (reply : RustM (Option PqxdhServerRegistrationPublication.Response)) :
    PqxdhInitialOriginPost.Trace Bool S B :=
  match reply with
  | .ok (some response) =>
      match (front.roles.1.1 index).server.peers response.keyId with
      | none => before
      | some peer =>
          let owner := RawCtxProtocolReveals.Owner.server index response.keyId
          { installed := Function.update before.installed owner (some origin)
            published := before.published ++ [((owner, peer.kernel.control.send_sequence), origin)] }
  | _ => before

/-- The selected first-response transcript entry is the original entry on the displayed front. -/
theorem selectedAfter_native (before : PqxdhInitialOriginPost.Trace Bool S B) (front : PqxdhSelectedPostCompiler.Front M P I D K S B)
    (index : Fin S) (origin : Bool) (reply : RustM (Option PqxdhServerRegistrationPublication.Response)) :
    PqxdhInitialOriginPost.afterBuilder before (frontOf key front) index origin reply = selectedAfter before front index origin reply := by
  rcases reply with (_ | response) | error | _
  · rfl
  · simp only [PqxdhInitialOriginPost.afterBuilder, selectedAfter, frontOf, rolesOf_roles, RawCtxGenericRoleFamily.mapRoles,
      RawCtxGenericRoleStorage.mapServer]
    cases (front.roles.1.1 index).server.peers response.keyId <;> rfl
  · rfl
  · rfl

/-- The selected first-record run: selected-material Server builder, then the traced stopped-source post interpreter. -/
noncomputable def selectedRun (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool)
    (initialKernel : RustM RawCtxSelectedMessageReveals.Kernel) (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Bool)
    (front : PqxdhSelectedPostCompiler.Front M P I D K S B) (shared : RawCtxSharedPrimitive.SharedState (Local A N C)) :
    ProbComp (Option Bool × Traced M P I D K A N C S B) := do
  let built ← (selectedBuild pre application initial selector aux source writer prior parent key target nonce next sender
    initialKernel index metadata ready front).run shared
  (simulateQ (traced pre application initial selector aux source writer prior parent key target nonce next sender route decode mark)
    (RawCtxSelectedFamilyNonceCoupling.optionalClient (post built.1.1))).run
      ((built.1.2, built.2), selectedAfter PqxdhInitialSourcePublication.empty built.1.2 index true built.1.1)

/-- Erasing the private transcript from a selected run leaves the selected builder followed by the stopped-source post interpreter `PqxdhSelectedPostDisclosure.normal`. -/
theorem selectedRun_erase (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool)
    (initialKernel : RustM RawCtxSelectedMessageReveals.Kernel) (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Bool)
    (front : PqxdhSelectedPostCompiler.Front M P I D K S B) (shared : RawCtxSharedPrimitive.SharedState (Local A N C)) :
    Prod.map id Prod.fst <$> selectedRun pre application initial selector aux source writer prior parent key target nonce next sender route decode
      mark initialKernel index metadata ready post front shared =
      ((selectedBuild pre application initial selector aux source writer prior parent key target nonce next sender
        initialKernel index metadata ready front).run shared >>= fun built =>
        (simulateQ (PqxdhSelectedPostDisclosure.normal pre application initial selector aux source writer prior parent key target nonce next
          sender route decode) (RawCtxSelectedFamilyNonceCoupling.optionalClient (post built.1.1))).run (built.1.2, built.2)) := by
  simp only [selectedRun, map_bind]
  refine bind_congr fun built => ?_
  exact traced_program_erase pre application initial selector aux source writer prior parent key target nonce next sender route decode mark
    (post built.1.1) ((built.1.2, built.2), selectedAfter PqxdhInitialSourcePublication.empty built.1.2 index true built.1.1)

/-- The explicit projection from a selected run to the native retained run: reply, displayed front, transcript and retained state. -/
def nativeView (key : RootOutput) (result : Option Bool × Traced M P I D K A N C S B) :
    (Bool × PqxdhInitialOriginPostPath.Snapshot M P I D K S B) × PqxdhInitialNativeRetained.RetainedState A N C :=
  ((result.1.getD false, (frontOf key result.2.1.1, result.2.2)), retainedOf result.2.1.2)

/-- The original native first-builder and post source under the retained fixed table equals the selected run, projected by `nativeView`. -/
theorem sequence_selected (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool)
    (initialKernel : RustM RawCtxSelectedMessageReveals.Kernel) (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Bool)
    (front : PqxdhSelectedPostCompiler.Front M P I D K S B) (shared : RawCtxSharedPrimitive.SharedState (Local A N C)) :
    (simulateQ (PqxdhInitialNativeRetained.retained source writer table (lifted pre application initial selector aux))
      ((PqxdhInitialOriginPost.sequence (X := X) (Response := Response) source (interp <$> initialKernel) mark true sender route decode
        index metadata ready post).run (frontOf key front, PqxdhInitialSourcePublication.empty))).run (retainedOf shared) =
      nativeView key <$> selectedRun pre application initial selector aux source writer prior parent key target nonce next sender route decode
        mark initialKernel index metadata ready post front shared := by
  rw [← low_program]
  change Prod.map id retainedOf <$> (simulateQ (lowered pre application initial selector aux source writer table)
    ((PqxdhInitialPendingBuilder.build source (interp <$> initialKernel) sender index metadata ready).run (frontOf key front) >>= fun built =>
      (simulateQ (PqxdhInitialOriginPost.compiler (X := X) (Response := Response) mark sender route decode) (post built.1)).run
        (built.2, PqxdhInitialOriginPost.afterBuilder PqxdhInitialSourcePublication.empty built.2 index true built.1))).run shared = _
  rw [simulateQ_bind, StateT.run_bind, build_step, StateT.run_map, bind_map_left]
  have continuation : ∀ built : (RustM (Option PqxdhServerRegistrationPublication.Response) × PqxdhSelectedPostCompiler.Front M P I D K S B) ×
      RawCtxSharedPrimitive.SharedState (Local A N C),
      (simulateQ (lowered pre application initial selector aux source writer table)
        ((simulateQ (PqxdhInitialOriginPost.compiler (X := X) (Response := Response) mark sender route decode) (post built.1.1)).run
          (frontOf key built.1.2, PqxdhInitialOriginPost.afterBuilder PqxdhInitialSourcePublication.empty (frontOf key built.1.2) index true built.1.1))).run
        built.2 =
      (fun result => ((result.1, (frontOf key result.2.1.1, result.2.2)), result.2.1.2)) <$>
        (simulateQ (tracedPlain pre application initial selector aux source writer prior parent key target nonce next sender route decode mark)
          (post built.1.1)).run ((built.1.2, built.2), selectedAfter PqxdhInitialSourcePublication.empty built.1.2 index true built.1.1) := by
    intro built
    rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, selectedAfter_native]
    have program := post_program pre application initial selector aux source writer prior parent key target nonce next sender route decode mark
      (post built.1.1) ((built.1.2, built.2), selectedAfter PqxdhInitialSourcePublication.empty built.1.2 index true built.1.1)
    change (fun result => ((result.1, result.2.1), result.2.2)) <$>
      (simulateQ (nativeFlat pre application initial selector aux source writer prior parent key target nonce next sender route decode mark)
        (post built.1.1)).run (tracedProj key ((built.1.2, built.2), selectedAfter PqxdhInitialSourcePublication.empty built.1.2 index true built.1.1)) = _
    rw [← program, Functor.map_map]
    rfl
  simp only [selectedRun, map_bind, traced_total, Functor.map_map]
  refine bind_congr fun built => ?_
  simp only [Prod.map_fst, Prod.map_snd, id_eq]
  rw [continuation, Functor.map_map]
  rfl

end Steps

section Random
open PqxdhNativeSharedPrefix PqxdhInitialBeaconAmbient PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}

/-- The all-known selected representation of the actual prepared front. -/
def initialFront (before : PqxdhInitialOriginPostPath.Front M P I D K S B) : PqxdhSelectedPostCompiler.Front M P I D K S B :=
  ⟨RawCtxSelectedMessageRevealInitialization.fromState
    (RawCtxGenericFamilyLive.nativeState ConcreteRatchetKernel.mk before.roles), before.controls, before.consumed⟩

/-- The selected local state carrying the actual shared primitive state, private identity state and root cache. -/
def initialShared (shared : RawCtxSharedPrimitive.SharedState A) (privateState : N) (cache : RootOracle.QueryCache)
    (store : RawCtxSelectiveChainGame.Store) : RawCtxSharedPrimitive.SharedState (Local A N RootOracle.QueryCache) :=
  (⟨shared.1, store, [], privateState, cache, []⟩, shared.2)

/-- The all-known selected front displays the actual prepared front. -/
theorem frontOf_initial (key : RootOutput) (before : PqxdhInitialOriginPostPath.Front M P I D K S B) :
    frontOf key (initialFront before) = before := by
  have roles : rolesOf key (initialFront before).roles = before.roles := by
    simp only [rolesOf, initialFront, RawCtxSelectedMessageRevealInitialization.state_roundtrip, fromNative_native]
  cases before
  simp only [frontOf, roles]
  rfl

/-- The selected local state carries exactly the actual retained native state. -/
theorem retainedOf_initial (shared : RawCtxSharedPrimitive.SharedState A) (privateState : N) (cache : RootOracle.QueryCache)
    (store : RawCtxSelectiveChainGame.Store) :
    retainedOf (initialShared shared privateState cache store) = (shared, (privateState, cache)) := rfl

/-- The Server kernel with every cached message key marked known. -/
noncomputable def initialKernel (response64 : PqxdhInitialRootLabelService.Response) : RustM RawCtxSelectedMessageReveals.Kernel :=
  PqxdhSelectedMessageBeacon.knownKernel <$>
    (ConcreteRatchetKernel.refined <$> PqxdhInitialReplyErasure.kernelOf false response64)

/-- Interpreting the all-known Server kernel returns the actual initialized Server kernel. -/
theorem initialKernel_interpret (key : RootOutput) (response64 : PqxdhInitialRootLabelService.Response) :
    PqxdhSelectedMessageBeacon.interpretKernel key <$> initialKernel response64 =
      ConcreteRatchetKernel.refined <$> PqxdhInitialReplyErasure.kernelOf false response64 := by
  rw [initialKernel, rust_map_map]
  have identity : (PqxdhSelectedMessageBeacon.interpretKernel key ∘ PqxdhSelectedMessageBeacon.knownKernel) = id :=
    funext (PqxdhSelectedMessageBeacon.known_roundtrip key)
  rw [identity]
  cases PqxdhInitialReplyErasure.kernelOf false response64 <;> rfl

variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (application : Response → LocalCallback A N RootOracle.QueryCache (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared →
      LocalCallback A N RootOracle.QueryCache PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (selectedMessage : Message) (previousRoot : RootOutput) (response64 : PqxdhInitialRootLabelService.Response)
    (other : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (Ambient A N RootOracle.QueryCache))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Bool)
    (before : PqxdhInitialOriginPostPath.Front M P I D K S B) (selected : RawCtxProtocolReveals.Owner S B)
    (shared : RawCtxSharedPrimitive.SharedState A) (privateState : N) (cache : RootOracle.QueryCache)
    (store : RawCtxSelectiveChainGame.Store) (key : RootOutput) (nonce : NonceOutput) (next : RootOutput)

/-- The selected first-record run for the actual stage-one source input: prior production stream, no parent entry, and the actual selected directional root as target. -/
noncomputable def firstRun : ProbComp (Option Bool × Traced M P I D K A N RootOracle.QueryCache S B) :=
  selectedRun pre application initial selector aux source writer (productionStream source.crypto) none key
    (PqxdhInitialSourceExperiment.root source previousRoot response64 selected) nonce next sender route decode
    (PqxdhInitialSelectedOrigin.mark source selectedMessage) (initialKernel response64) index metadata ready post
    (initialFront before) (initialShared shared privateState cache store)

/-- The first randomized source run with the private full76 response `(key, nonce, next)` is exactly the selected-material first-record run under the explicit projection `nativeView`. The only premise identifies the native external callbacks with the source-local callbacks used by the selected run. -/
theorem randomRun_selected
    (hext : lifted pre application initial selector aux =
      PqxdhInitialOriginFinishPath.withInitial source selectedMessage previousRoot response64 other) :
    PqxdhInitialSourceRandom.randomRun source writer selectedMessage previousRoot response64 other sender route decode
      index metadata ready post before selected shared privateState cache (RawCtxSelectedMessageKdf.response key nonce next) =
      nativeView key <$> firstRun pre application initial selector aux source writer selectedMessage previousRoot response64
        sender route decode index metadata ready post before selected shared privateState cache store key nonce next := by
  have sequence := sequence_selected pre application initial selector aux source writer (productionStream source.crypto) none key
    (PqxdhInitialSourceExperiment.root source previousRoot response64 selected) nonce next sender route decode
    (PqxdhInitialSelectedOrigin.mark source selectedMessage) (initialKernel response64) index metadata ready post
    (initialFront before) (initialShared shared privateState cache store)
  rw [hext, frontOf_initial, retainedOf_initial, initialKernel_interpret] at sequence
  exact sequence

/-- The message material of the explicit first-record response is exactly its selected key and nonce. -/
theorem material_response : PqxdhOrderedChainHybrids.material (RawCtxSelectedMessageKdf.response key nonce next) = (key, nonce) := by
  have split : PqxdhOrderedChainHybrids.materialChainEquiv (RawCtxSelectedMessageKdf.response key nonce next) =
      (PqxdhOrderedChainHybrids.material (RawCtxSelectedMessageKdf.response key nonce next),
        PqxdhOrderedChainHybrids.nextChain (RawCtxSelectedMessageKdf.response key nonce next)) := rfl
  simp only [RawCtxSelectedMessageKdf.response, Equiv.apply_symm_apply] at split
  exact (Prod.mk.inj split).1.symm

/-- Every full76 output is the explicit first-record response of its own key, nonce and next-chain parts. -/
theorem response_material (output : FullOutput) :
    RawCtxSelectedMessageKdf.response (PqxdhOrderedChainHybrids.material output).1 (PqxdhOrderedChainHybrids.material output).2
      (PqxdhOrderedChainHybrids.nextChain output) = output := by
  have split : PqxdhOrderedChainHybrids.materialChainEquiv output =
      (PqxdhOrderedChainHybrids.material output, PqxdhOrderedChainHybrids.nextChain output) := rfl
  rw [RawCtxSelectedMessageKdf.response, ← split]
  exact PqxdhOrderedChainHybrids.materialChainEquiv.symm_apply_apply output

/-- The selected publication gate: the post client returned `true` and the selected-origin record was published. -/
def SelectedGate (number : Std.U64) (result : Option Bool × Traced M P I D K A N RootOracle.QueryCache S B) : Prop :=
  result.1 = some true ∧ ((selected, number), true) ∈ result.2.2.published

/-- The original first-record source decision on the projected selected run is the selected gate, absence of hidden disclosure, retained input/ancestor freshness and non-disclosure of the selected key. -/
theorem first_selected_decision (number : Std.U64) (position : number.val = 1) (ancestors disclosed : List RatchetChain)
    (result : Option Bool × Traced M P I D K A N RootOracle.QueryCache S B) :
    PqxdhInitialSourceRandom.decision source previousRoot response64 selected (RawCtxSelectedMessageKdf.response key nonce next)
      number ancestors disclosed (nativeView key result) = true ↔
      SelectedGate selected number result ∧ RawCtxSelectedMessageFreshness.hidden result.2.1.1.roles.2 = false ∧
        RawCtxLiveLineage.FreshValues
          (RawCtxFreshChainCut.concreteChain (PqxdhInitialSourceExperiment.root source previousRoot response64 selected) :: ancestors)
          (RawCtxSelectedMessageFreshness.known disclosed result.2.1.1.roles.2) ∧
        RawCtxFreshChainCut.concreteChain key ∉ RawCtxSelectedMessageFreshness.known disclosed result.2.1.1.roles.2 := by
  have characterized := PqxdhSelectedMessageSourceFreshness.first_decision (productionStream source.crypto)
    (PqxdhInitialSourceExperiment.root source previousRoot response64 selected) (RawCtxSelectedMessageKdf.response key nonce next)
    selected number position ancestors disclosed (nativeView key result).1 result.2.1.1.roles.2
    (by rw [material_response]; rfl)
  rw [material_response] at characterized
  have gate : PqxdhInitialPublishedEvent.Gate selected number (nativeView key result).1 ↔ SelectedGate selected number result := by
    simp only [PqxdhInitialPublishedEvent.Gate, SelectedGate, nativeView]
    cases result.1 with
    | none => simp
    | some value => simp
  rw [← gate]
  exact characterized

/-- The first randomized source decision distribution is the explicit decision of the projected selected first-record run. -/
theorem decision_selected (number : Std.U64) (ancestors disclosed : List RatchetChain)
    (hext : lifted pre application initial selector aux =
      PqxdhInitialOriginFinishPath.withInitial source selectedMessage previousRoot response64 other) :
    PqxdhInitialSourceRandom.decision source previousRoot response64 selected (RawCtxSelectedMessageKdf.response key nonce next)
        number ancestors disclosed <$>
      PqxdhInitialSourceRandom.randomRun source writer selectedMessage previousRoot response64 other sender route decode
        index metadata ready post before selected shared privateState cache (RawCtxSelectedMessageKdf.response key nonce next) =
      (fun result => PqxdhInitialSourceRandom.decision source previousRoot response64 selected
          (RawCtxSelectedMessageKdf.response key nonce next) number ancestors disclosed (nativeView key result)) <$>
        firstRun pre application initial selector aux source writer selectedMessage previousRoot response64
          sender route decode index metadata ready post before selected shared privateState cache store key nonce next := by
  rw [randomRun_selected pre application initial selector aux source writer selectedMessage previousRoot response64 other
    sender route decode index metadata ready post before selected shared privateState cache store key nonce next hext, Functor.map_map]

end Random

section Prepared
open PqxdhNativeSharedPrefix PqxdhInitialBeaconAmbient PqxdhSecretInputKdf PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A) (hashCache : CtxRomAuth.CtxRO.QueryCache)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (secret : KemSK) (challenge : MlKem768Ciphertext)
    (selectedMessage : Message) (previousRoot : RootOutput) (response64 : PqxdhInitialRootLabelService.Response)

local notation "sharedEnv" => PqxdhSourceSharedPreparation.environment setup env callbacks hashCache

/-- The prepared source's native external callbacks are exactly the lifted source-local callbacks of the selected run: preparation, application getter, retained initializer, private selector and source auxiliary services. -/
theorem prepared_lifted :
    lifted
      (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (sharedEnv).source (sharedEnv).localImpl baseImpl kem secret challenge)
      (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (sharedEnv).source (sharedEnv).localImpl baseImpl kem secret challenge)
      (initialLocal (A := A) (N := PqxdhPhase1AcceptanceOracle.BareState 1) (sharedEnv).source selectedMessage previousRoot response64)
      (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A)
        (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem secret challenge))
      (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks) =
      PqxdhInitialOriginFinishPath.withInitial (sharedEnv).source selectedMessage previousRoot response64
        (PqxdhInitialPreparedSourceInput.other sharedEnv baseImpl kem attachedVerify primitives secret challenge) := by
  funext query
  rcases query with query | (reply | (secrets | (query | query)))
  · exact PqxdhPreparedPrefixCallbacks.preparation_source attachedVerify primitives 1 _ _ baseImpl kem secret challenge query
  · exact PqxdhPreparedPrefixCallbacks.application_source attachedVerify primitives 1 _ _ baseImpl kem secret challenge reply
  · change Prod.snd <$> localLift (initialLocal _ selectedMessage previousRoot response64 secrets) = _
    rw [initial_source]
    rfl
  · exact PqxdhPreparedPrefixCallbacks.selector_source _ query
  · exact PqxdhPreparedPrefixCallbacks.auxiliary_source callbacks query

variable (writer : RawCtxMixedShared.Writer) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (post : RustM (Option PqxdhServerRegistrationPublication.Response) →
      OracleComp (PqxdhInitialGenericPost.Spec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (before : PqxdhInitialOriginPostPath.Front M P (IdentityHandle I) (DhPair setup) (KemHandle K) S (B + 1))
    (selected : RawCtxProtocolReveals.Owner S (B + 1))
    (shared : RawCtxSharedPrimitive.SharedState A) (privateState : PqxdhPhase1AcceptanceOracle.BareState 1)
    (cache : RootOracle.QueryCache) (store : RawCtxSelectiveChainGame.Store)
    (key : RootOutput) (nonce : PqxdhFullSecretInputKdf.NonceOutput) (next : RootOutput)

/-- For the actual prepared source callbacks, the first randomized source run is the selected first-record run under `nativeView`, with no callback premise. -/
theorem randomRun_prepared :
    PqxdhInitialSourceRandom.randomRun (sharedEnv).source writer selectedMessage previousRoot response64
      (PqxdhInitialPreparedSourceInput.other sharedEnv baseImpl kem attachedVerify primitives secret challenge)
      sender route decode index metadata ready post before selected shared privateState cache
      (RawCtxSelectedMessageKdf.response key nonce next) =
      nativeView key <$> firstRun
        (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (sharedEnv).source (sharedEnv).localImpl baseImpl kem secret challenge)
        (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (sharedEnv).source (sharedEnv).localImpl baseImpl kem secret challenge)
        (initialLocal (A := A) (N := PqxdhPhase1AcceptanceOracle.BareState 1) (sharedEnv).source selectedMessage previousRoot response64)
        (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A)
          (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem secret challenge))
        (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks)
        (sharedEnv).source writer selectedMessage previousRoot response64 sender route decode index metadata ready post before selected
        shared privateState cache store key nonce next :=
  randomRun_selected _ _ _ _ _ _ writer selectedMessage previousRoot response64 _ sender route decode index metadata ready post before
    selected shared privateState cache store key nonce next
    (prepared_lifted setup env callbacks hashCache baseImpl kem attachedVerify primitives secret challenge selectedMessage previousRoot response64)

end Prepared

end BeaconcryptCore.Computational.PqxdhSelectedFirstRecord

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.state_map_apply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.state_map_apply

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.optional_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.optional_total

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.native_aux' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.native_aux

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.protocol_aux' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.protocol_aux

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.backend_aux' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.backend_aux

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.backend_program_aux' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.backend_program_aux

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.retained_aux' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.retained_aux

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.retained_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.retained_frame

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.low_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.low_step

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.low_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.low_program

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.lowered_calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.lowered_calls

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.native_fromNative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.native_fromNative

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.fromNative_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.fromNative_native

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.rolesOf_roles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.rolesOf_roles

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.rolesOf_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.rolesOf_history

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.frontOf_install' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.frontOf_install

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.frontOf_consume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.frontOf_consume

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.frontOf_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.frontOf_selected

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.frontOf_installServer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.frontOf_installServer

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.live_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.live_forward

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.record_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.record_step

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.finish_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.finish_step

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.finish_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.finish_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.traced_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.traced_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.rust_map_map' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.rust_map_map

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.publication_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.publication_native

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.publication_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.publication_selected

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.ready_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.ready_map

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.build_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.build_step

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.post_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.post_step

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.post_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.post_program

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.traced_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.traced_total

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.traced_program_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.traced_program_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.selectedAfter_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.selectedAfter_native

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.selectedRun_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.selectedRun_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.sequence_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.sequence_selected

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.frontOf_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.frontOf_initial

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.retainedOf_initial' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.retainedOf_initial

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.initialKernel_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.initialKernel_interpret

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.randomRun_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.randomRun_selected

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.material_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.material_response

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.response_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.response_material

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.first_selected_decision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.first_selected_decision

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.decision_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.decision_selected

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.prepared_lifted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.prepared_lifted

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.randomRun_prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.randomRun_prepared
