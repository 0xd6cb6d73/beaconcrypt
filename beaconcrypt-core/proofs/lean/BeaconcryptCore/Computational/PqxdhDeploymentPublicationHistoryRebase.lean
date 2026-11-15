-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppressionTrace
import BeaconcryptCore.Computational.PqxdhRegistrationJointOpenBackend

/-! Private identity histories are append-only observations, not inputs to source decisions. Prefix equivariance retains every old observation and every new current-call observation, while leaving seeds, KEM state, native state and replies unchanged. Replacing a prefix never filters past signing calls according to a later selected message. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase
open PqxdhJointIdentity PqxdhServerAuthExperiment
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result Local : Type}

abbrev History := List PqxdhDynamicIdentityPool.Observation

/-- Add an arbitrary earlier identity-service observation prefix, preserving the entire existing state. -/
def prependIdentity (earlier : History) (state : PqxdhDynamicIdentityPool.SourceState) :
    PqxdhDynamicIdentityPool.SourceState := ⟨state.seeds, earlier ++ state.transcript⟩

def prependPool (earlier : History) (pool : PqxdhRegistrationJointPreparation.Pool KemSK) :
    PqxdhRegistrationJointPreparation.Pool KemSK := (prependIdentity earlier pool.1, pool.2)

def prependContext (earlier : History) (state : PqxdhRegistrationJointPreparation.Pool KemSK × Local) :
    PqxdhRegistrationJointPreparation.Pool KemSK × Local := (prependPool earlier state.1, state.2)

def prependSchedule (earlier : History) (state : PqxdhRegistrationJointSchedule.State KemSK) :
    PqxdhRegistrationJointSchedule.State KemSK := { state with pool := prependPool earlier state.pool }

/-- Local handler equivariance composes through every adaptive oracle continuation and full intermediate state. -/
theorem simulate_naturality {κ κ' σ Value : Type} {source : OracleSpec κ} {target : OracleSpec κ'}
    (impl : QueryImpl source (StateT σ (OracleComp target))) (shift : σ → σ)
    (step : ∀ query state, (fun result => (result.1, shift result.2)) <$> (impl query).run state =
      (impl query).run (shift state))
    (program : OracleComp source Value) (state : σ) :
    (fun result => (result.1, shift result.2)) <$> (simulateQ impl program).run state =
      (simulateQ impl program).run (shift state) := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rw [← step query state, bind_map_left]
    apply bind_congr
    intro outcome
    exact ih outcome.1 outcome.2

/-- Every actual lazy identity request appends its new observation after the unchanged prior prefix. -/
theorem lazy_prefix (joint : Primitives) (query : PqxdhDynamicIdentityPool.DynamicSpec.Domain)
    (earlier : History) (state : PqxdhDynamicIdentityPool.SourceState) :
    (fun result => (result.1, prependIdentity earlier result.2)) <$>
        (PqxdhDynamicIdentityPool.lazyImpl joint query).run state =
      (PqxdhDynamicIdentityPool.lazyImpl joint query).run (prependIdentity earlier state) := by
  rcases query with coin | query
  · simp [PqxdhDynamicIdentityPool.lazyImpl, PqxdhDynamicIdentityPool.poolImpl,
      PqxdhDynamicIdentityPool.record, prependIdentity, StateT.run, List.append_assoc]
  · cases query
    case create =>
      rw [PqxdhDynamicIdentityPool.lazyImpl_create, PqxdhDynamicIdentityPool.lazyImpl_create]
      simp only [Functor.map_map]
      congr 1
      funext seed
      simp [PqxdhDynamicIdentityPool.createdReply, PqxdhDynamicIdentityPool.record,
        prependIdentity, List.append_assoc]
    all_goals
      simp [PqxdhDynamicIdentityPool.lazyImpl, PqxdhDynamicIdentityPool.poolImpl,
        PqxdhDynamicIdentityPool.record, prependIdentity, StateT.run, List.append_assoc]

/-- The full indexed identity/KEM service keeps KEM state and all local draws while rebasing only the old identity prefix. -/
theorem pool_prefix (setup : Setup baseSpec KemSK) (query : (PqxdhLiveKemBirth.Spec KemSK).Domain)
    (earlier : History) (state : PqxdhRegistrationJointPreparation.Pool KemSK) :
    (fun result => (result.1, prependPool earlier result.2)) <$>
        (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem query).run state =
      (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem query).run (prependPool earlier state) := by
  rcases query with identity | coin | kem
  · simp only [PqxdhLiveKemBirth.impl, StateT.run, Functor.map_map]
    have shifted := congrArg (fun work => (fun result => (result.1, (result.2, state.2))) <$> work)
      (lazy_prefix setup.joint identity earlier state.1)
    simpa only [prependPool, StateT.run, Functor.map_map] using shifted
  · simp [PqxdhLiveKemBirth.impl, StateT.run, prependPool, Functor.map_map]
  · simp [PqxdhLiveKemBirth.impl, StateT.run, prependPool, Functor.map_map]

/-- Every adaptive indexed service program respects the same exact old-prefix transformation. -/
theorem pool_program_prefix (setup : Setup baseSpec KemSK) (earlier : History)
    (program : OracleComp (PqxdhLiveKemBirth.Spec KemSK) Result)
    (state : PqxdhRegistrationJointPreparation.Pool KemSK) :
    (fun result => (result.1, prependPool earlier result.2)) <$>
        (simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem) program).run state =
      (simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem) program).run (prependPool earlier state) :=
  simulate_naturality _ _ (fun query before => pool_prefix setup query earlier before) program state

/-- Exact state-transformer equivariance also composes through an ordinary monadic continuation. -/
theorem bind_naturality {State Value Output : Type} (shift : State → State)
    (first : StateT State ProbComp Value) (next : Value → StateT State ProbComp Output)
    (firstLaw : ∀ state, (fun result => (result.1, shift result.2)) <$> first.run state = first.run (shift state))
    (nextLaw : ∀ value state, (fun result => (result.1, shift result.2)) <$> (next value).run state =
      (next value).run (shift state)) (state : State) :
    (fun result => (result.1, shift result.2)) <$> (first >>= next).run state =
      (first >>= next).run (shift state) := by
  simp only [StateT.run_bind, map_bind]
  rw [← firstLaw state, bind_map_left]
  apply bind_congr
  intro result
  exact nextLaw result.1 result.2

/-- Native auxiliary work sees none of the old private identity observations. -/
theorem auxiliary_prefix (earlier : History) (work : StateT Local ProbComp Result)
    (state : PqxdhRegistrationJointPreparation.Pool KemSK × Local) :
    (fun result => (result.1, prependContext earlier result.2)) <$>
        (PqxdhRegistrationJointServerPrefix.onAux work).run state =
      (PqxdhRegistrationJointServerPrefix.onAux work).run (prependContext earlier state) := by
  simp only [PqxdhRegistrationJointServerPrefix.onAux, StateT.run, Functor.map_map]
  rfl

/-- The actual Server-prefix annotation only appends its current static-DH observation to the preserved prefix. -/
theorem server_prefix_query (joint : Primitives) (seed : IdentitySeed) (serverIndex : Nat)
    (aux : QueryImpl (PqxdhRegistrationJointServerPrefix.AuxSpec Reader) (StateT Local ProbComp))
    (query : (PqxdhRegistrationJointServerPrefix.NativeSpec Reader).Domain) (earlier : History)
    (state : PqxdhRegistrationJointPreparation.Pool KemSK × Local) :
    (fun result => (result.1, prependContext earlier result.2)) <$>
        (PqxdhRegistrationJointServerPrefix.annotated joint seed serverIndex aux query).run state =
      (PqxdhRegistrationJointServerPrefix.annotated joint seed serverIndex aux query).run (prependContext earlier state) := by
  cases query
  case staticDh point =>
    simp only [PqxdhRegistrationJointServerPrefix.annotated, PqxdhServerStaticDhSource.nativeImpl,
      bind_pure_comp, StateT.run_map, Functor.map_map]
    simp [PqxdhRegistrationJointServerPrefix.visit, StateT.run,
      prependContext, prependPool, prependIdentity, PqxdhDynamicIdentityPool.record, List.append_assoc]
  all_goals exact auxiliary_prefix earlier _ state

/-- All real collector callbacks, including failures, retain the same current-call history suffix and consumed-registration state. -/
theorem server_prefix_program (joint : Primitives) (seed : IdentitySeed) (serverIndex : Nat)
    (aux : QueryImpl (PqxdhRegistrationJointServerPrefix.AuxSpec Reader) (StateT Local ProbComp))
    (program : OracleComp (PqxdhRegistrationJointServerPrefix.NativeSpec Reader) Result) (earlier : History)
    (state : PqxdhRegistrationJointPreparation.Pool KemSK × Local) :
    (fun result => (result.1, prependContext earlier result.2)) <$>
        (simulateQ (PqxdhRegistrationJointServerPrefix.annotated joint seed serverIndex aux) program).run state =
      (simulateQ (PqxdhRegistrationJointServerPrefix.annotated joint seed serverIndex aux) program).run
        (prependContext earlier state) :=
  simulate_naturality _ _ (fun query before => server_prefix_query joint seed serverIndex aux query earlier before)
    program state

/-- The actual Beacon preparation keeps native replies and KEM observations while appending only its current identity-DH observations. -/
theorem preparation_prefix (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex kemIndex : Nat) (query : (PqxdhRegistrationJointPreparation.NativeSpec KemSK Response).Domain)
    (earlier : History) (state : PqxdhRegistrationJointPreparation.Pool KemSK) :
    (fun result => (result.1, prependPool earlier result.2)) <$>
        (PqxdhRegistrationJointPreparation.annotated setup codec identityIndex kemIndex query).run state =
      (PqxdhRegistrationJointPreparation.annotated setup codec identityIndex kemIndex query).run (prependPool earlier state) := by
  cases query
  case decapsulate ciphertext key =>
    simp only [PqxdhRegistrationJointPreparation.annotated, StateT.run, Functor.map_map]
    rfl
  case dhIdentity seed point =>
    simp [PqxdhRegistrationJointPreparation.annotated, StateT.run,
      prependPool, prependIdentity, PqxdhDynamicIdentityPool.record, List.append_assoc]
  all_goals simp only [PqxdhRegistrationJointPreparation.annotated, StateT.run, Functor.map_map]

/-- The complete native finish annotation is independent of the old identity transcript. -/
theorem finish_query_prefix (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex kemIndex : Nat) (query : (PqxdhRegistrationJointFinish.NativeSpec KemSK Response).Domain)
    (earlier : History) (state : PqxdhRegistrationJointFinish.State KemSK) :
    (fun result => (result.1, prependContext earlier result.2)) <$>
        (PqxdhRegistrationJointFinish.annotated setup codec identityIndex kemIndex query).run state =
      (PqxdhRegistrationJointFinish.annotated setup codec identityIndex kemIndex query).run (prependContext earlier state) := by
  cases query with
  | inl query =>
    simp only [PqxdhRegistrationJointFinish.annotated, PqxdhRegistrationJointFinish.onPool,
      StateT.run, Functor.map_map]
    have shifted := congrArg (fun work => (fun result => (result.1, (result.2, state.2))) <$> work)
      (preparation_prefix setup codec identityIndex kemIndex query earlier state.1)
    simp only [StateT.run, Functor.map_map] at shifted
    convert shifted using 1 <;> rfl
  | inr query => exact auxiliary_prefix earlier _ state

/-- Every adaptive native finish program has exact old-history prefix equivariance. -/
theorem finish_program_prefix (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex kemIndex : Nat)
    (program : OracleComp (PqxdhRegistrationJointFinish.NativeSpec KemSK Response) Result)
    (earlier : History) (state : PqxdhRegistrationJointFinish.State KemSK) :
    (fun result => (result.1, prependContext earlier result.2)) <$>
        (simulateQ (PqxdhRegistrationJointFinish.annotated setup codec identityIndex kemIndex) program).run state =
      (simulateQ (PqxdhRegistrationJointFinish.annotated setup codec identityIndex kemIndex) program).run
        (prependContext earlier state) :=
  simulate_naturality _ _ (fun query before => finish_query_prefix setup codec identityIndex kemIndex query earlier before)
    program state

/-- Actual raw-accept preparation preserves the complete consumed set and appends observations after the chosen old prefix. -/
theorem source_prepare_prefix (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (serverIndex : Nat) (raw : Pqxdh.Bytes) (earlier : History)
    (state : PqxdhRegistrationJointFinish.State KemSK) :
    (fun result => (result.1, prependContext earlier result.2)) <$>
        (PqxdhRegistrationJointServerAccept.sourcePrepare setup codec checks seed serverIndex raw).run state =
      (PqxdhRegistrationJointServerAccept.sourcePrepare setup codec checks seed serverIndex raw).run
        (prependContext earlier state) := by
  have shifted := congrArg (fun work =>
      (fun result => ((result.1, result.2.2), (result.2.1, state.2))) <$> work)
    (server_prefix_program setup.joint seed serverIndex (serverAux setup codec checks)
      (PqxdhServerRootPreparation.collect raw) earlier (state.1, state.2.2.server.consumed))
  simp only [PqxdhRegistrationJointServerAccept.sourcePrepare, StateT.run, Functor.map_map]
  simp only [Functor.map_map] at shifted
  convert shifted using 1 <;> rfl

/-- Full successful or rejected raw acceptance keeps exactly its real new observations after an arbitrary old identity prefix. -/
theorem source_accept_prefix (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (serverIndex : Nat) (raw : Pqxdh.Bytes) (earlier : History)
    (state : PqxdhRegistrationJointFinish.State KemSK) :
    (fun result => (result.1, prependContext earlier result.2)) <$>
        (PqxdhRegistrationJointServerAccept.source setup codec checks seed serverIndex raw).run state =
      (PqxdhRegistrationJointServerAccept.source setup codec checks seed serverIndex raw).run
        (prependContext earlier state) := by
  unfold PqxdhRegistrationJointServerAccept.source PqxdhRegistrationJointServerAccept.run
  apply bind_naturality (prependContext earlier) _ _
    (fun before => auxiliary_prefix earlier _ before)
  intro beforeNative current
  exact bind_naturality (prependContext earlier) _ _
    (fun before => source_prepare_prefix setup codec checks seed serverIndex raw earlier before)
    (fun _ before => auxiliary_prefix earlier _ before) current

/-- Reinstalling a complete native backend result leaves the old identity history prefix untouched. -/
theorem onBackend_prefix (earlier : History)
    (work : StateT (PqxdhRegistrationJointFinish.State KemSK) ProbComp Result)
    (law : ∀ state, (fun result => (result.1, prependContext earlier result.2)) <$> work.run state =
      work.run (prependContext earlier state)) (state : PqxdhRegistrationJointSchedule.State KemSK) :
    (fun result => (result.1, prependSchedule earlier result.2)) <$>
        (PqxdhRegistrationJointServerSchedule.onBackend work).run state =
      (PqxdhRegistrationJointServerSchedule.onBackend work).run (prependSchedule earlier state) := by
  simp only [PqxdhRegistrationJointServerSchedule.onBackend, StateT.run, Functor.map_map]
  have shifted := congrArg (fun computation =>
      (fun result => (result.1, { state with pool := result.2.1, shared := result.2.2 })) <$> computation)
    (law (state.pool, state.shared))
  simp only [Functor.map_map] at shifted
  convert shifted using 1 <;> rfl

private theorem annotated_finish_prefix (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex kemIndex : Nat) (retained : Option PqxdhEd25519EufCma.Phase1Candidate) (raw : Pqxdh.Bytes)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (earlier : History)
    (state : PqxdhRegistrationJointFinish.State KemSK) :
    (fun result => (result.1, prependContext earlier result.2)) <$>
        (PqxdhRegistrationJointFinish.annotatedFinish setup codec identityIndex kemIndex retained raw owner).run state =
      (PqxdhRegistrationJointFinish.annotatedFinish setup codec identityIndex kemIndex retained raw owner).run
        (prependContext earlier state) := by
  unfold PqxdhRegistrationJointFinish.annotatedFinish
  cases phase : owner.beacon.phase <;> simp only [StateT.run_pure, map_pure]
  case initSent control prekey oneTime kem =>
    cases retained <;> cases decoded : PqxdhServerAuthExperiment.responseOf codec raw <;>
      simp only [StateT.run_pure, map_pure]
    rw [StateT.run_bind, StateT.run_bind]
    simp only [PqxdhRegistrationJointFinish.onNative, StateT.run, prependContext,
      map_bind, bind_map_left]
    apply bind_congr
    intro hashed
    exact finish_program_prefix setup codec identityIndex kemIndex
      (PqxdhBeaconPhase2Publication.nativeOwner
        (completedBinding := PqxdhTranscriptAd.completedOf control hashed.1) codec.frameRead raw owner)
      earlier (state.1, hashed.2)

/-- A native finish at any present or absent owner keeps its actual owner result and KEM/shared effects under identity-history prefixing. -/
theorem source_finish_prefix (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (address : Nat) (raw : Pqxdh.Bytes) (earlier : History) (state : PqxdhRegistrationJointSchedule.State KemSK) :
    (fun result => (result.1, prependSchedule earlier result.2)) <$>
        (PqxdhRegistrationJointSchedule.finish setup codec address raw).run state =
      (PqxdhRegistrationJointSchedule.finish setup codec address raw).run (prependSchedule earlier state) := by
  cases found : state.owners[address]? with
  | none => simp [PqxdhRegistrationJointSchedule.finish, StateT.run, prependSchedule, found]
  | some entry =>
    simp only [PqxdhRegistrationJointSchedule.finish, StateT.run, prependSchedule, found, Functor.map_map]
    have shifted := congrArg (fun work => (fun result => (result.1.1, { state with
        pool := result.2.1, shared := result.2.2,
        owners := state.owners.set address { entry with owner := result.1.2 } })) <$> work)
      (annotated_finish_prefix setup codec entry.identityIndex entry.kemIndex (state.inits address) raw entry.owner
        earlier (state.pool, state.shared))
    simp only [Functor.map_map] at shifted
    convert shifted using 1 <;> rfl

/-- Constructor sampling and installation preserve the complete old identity prefix. -/
theorem source_create_prefix (setup : Setup baseSpec KemSK)
    (pin : PqxdhBeaconPhase2Preparation.Word32) (keyId : U64) (earlier : History)
    (state : PqxdhRegistrationJointSchedule.State KemSK) :
    (fun result => (result.1, prependSchedule earlier result.2)) <$>
        (PqxdhRegistrationJointSchedule.create setup pin keyId).run state =
      (PqxdhRegistrationJointSchedule.create setup pin keyId).run (prependSchedule earlier state) := by
  simp only [PqxdhRegistrationJointSchedule.create, StateT.run, Functor.map_map]
  congr 1
  funext material
  simp [PqxdhRegistrationJointSchedule.created, PqxdhRegistrationJointSchedule.birth,
    PqxdhRegistrationJointCreation.serviceView, PqxdhDynamicIdentityPool.createdReply,
    PqxdhDynamicIdentityPool.record, prependSchedule, prependPool, prependIdentity, List.append_assoc]

private theorem bundle_after_prefix (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (index : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (generated : Option PqxdhJointGapDh.ScalarBytes) (earlier : History) (pool : PqxdhDynamicIdentityPool.SourceState) :
    ((PqxdhRegistrationJointBundle.after setup codec index owner generated pool).1,
      prependIdentity earlier (PqxdhRegistrationJointBundle.after setup codec index owner generated pool).2) =
      PqxdhRegistrationJointBundle.after setup codec index owner generated (prependIdentity earlier pool) := by
  unfold PqxdhRegistrationJointBundle.after
  cases PqxdhBeaconPhase1Publication.prepare owner generated with
  | none => rfl
  | some prepared =>
    dsimp only
    split <;> simp [PqxdhJointPhase1SourceWriter.signedState, PqxdhJointPhase1SourceWriter.recordSign,
      PqxdhDynamicIdentityPool.record, prependIdentity, List.append_assoc]

/-- The actual Fresh scalar draw and all three current signing calls retain the old history prefix on both writer outcomes. -/
theorem bundle_trace_prefix (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (index : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK) (earlier : History)
    (pool : PqxdhDynamicIdentityPool.SourceState) :
    (fun result => (result.1, prependIdentity earlier result.2)) <$>
        PqxdhRegistrationJointBundle.trace setup codec index owner pool =
      PqxdhRegistrationJointBundle.trace setup codec index owner (prependIdentity earlier pool) := by
  cases phase : owner.beacon.phase <;> simp only [PqxdhRegistrationJointBundle.trace, phase, Functor.map_map, map_pure]
  case fresh =>
    congr 1
    funext scalar
    exact bundle_after_prefix setup codec index owner (some scalar) earlier pool
  case freshWithCoins => exact congrArg pure (bundle_after_prefix setup codec index owner none earlier pool)

private theorem bundle_traceLog_prefix (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (index : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK) (earlier : History)
    (pool : PqxdhDynamicIdentityPool.SourceState) (logged : Option PqxdhEd25519EufCma.Phase1Candidate) :
    (fun result => ((result.1.1, prependIdentity earlier result.1.2), result.2)) <$>
        PqxdhRegistrationJointBundle.traceLog setup codec index owner pool logged =
      PqxdhRegistrationJointBundle.traceLog setup codec index owner (prependIdentity earlier pool) logged := by
  cases phase : owner.beacon.phase <;>
    simp only [PqxdhRegistrationJointBundle.traceLog, phase, Functor.map_map, map_pure]
  case fresh =>
    congr 1
    funext scalar
    exact Prod.ext (bundle_after_prefix setup codec index owner (some scalar) earlier pool) rfl
  case freshWithCoins =>
    exact congrArg pure (Prod.ext (bundle_after_prefix setup codec index owner none earlier pool) rfl)

/-- Reinstalling a native bundle preserves source owner state and the exact new signing suffix. -/
theorem source_bundle_prefix (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (address : Nat) (earlier : History) (state : PqxdhRegistrationJointSchedule.State KemSK) :
    (fun result => (result.1, prependSchedule earlier result.2)) <$>
        (PqxdhRegistrationJointSchedule.bundle setup codec address).run state =
      (PqxdhRegistrationJointSchedule.bundle setup codec address).run (prependSchedule earlier state) := by
  cases found : state.owners[address]? with
  | none => simp [PqxdhRegistrationJointSchedule.bundle, StateT.run, prependSchedule, found]
  | some entry =>
    simp only [PqxdhRegistrationJointSchedule.bundle, StateT.run, prependSchedule, found, Functor.map_map]
    have shifted := congrArg (fun work => (fun result => (result.1.1.1, { state with
        pool := (result.1.2, state.pool.2),
        owners := state.owners.set address { entry with owner := result.1.1.2 },
        inits := Function.update state.inits address result.2 })) <$> work)
      (bundle_traceLog_prefix setup codec entry.identityIndex entry.owner earlier state.pool.1 (state.inits address))
    simp only [Functor.map_map] at shifted
    convert shifted using 1 <;> rfl

/-- Shared native computation neither reads nor changes any old identity observation. -/
theorem shared_prefix (earlier : History) (work : PqxdhServerAuthNative.NativeGame KemSK Result)
    (state : PqxdhRegistrationJointSchedule.State KemSK) :
    (fun result => (result.1, prependSchedule earlier result.2)) <$>
        (PqxdhRegistrationJointSchedule.onShared work).run state =
      (PqxdhRegistrationJointSchedule.onShared work).run (prependSchedule earlier state) := by
  simp only [PqxdhRegistrationJointSchedule.onShared, StateT.run, Functor.map_map]
  rfl

/-- Actual current-field disclosures append their present observation without interpreting any old history. -/
theorem read_prefix (request : Nat × PqxdhRegistrationJointLiveRead.Field) (earlier : History)
    (state : PqxdhRegistrationJointSchedule.State KemSK) :
    ((PqxdhRegistrationJointLiveRead.sourceStep request state).1,
      prependSchedule earlier (PqxdhRegistrationJointLiveRead.sourceStep request state).2) =
      PqxdhRegistrationJointLiveRead.sourceStep request (prependSchedule earlier state) := by
  cases found : state.owners[request.1]? with
  | none => simp [PqxdhRegistrationJointLiveRead.sourceStep, prependSchedule, found]
  | some entry =>
    simp only [PqxdhRegistrationJointLiveRead.sourceStep, prependSchedule, found]
    cases request.2
    case identity =>
      simp [PqxdhRegistrationJointLiveRead.entrySource, prependPool, prependIdentity,
        PqxdhDynamicIdentityPool.record, List.append_assoc]
    case kem =>
      simp only [PqxdhRegistrationJointLiveRead.entrySource]
      cases PqxdhRegistrationJointOwnership.activeKey entry.owner <;> rfl
    all_goals rfl

/-- Every actual source command has full old-identity-prefix equivariance, including rejected calls and current-field reads. -/
theorem source_query_prefix (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (serverIndex : Nat) (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (earlier : History) (state : PqxdhRegistrationJointSchedule.State KemSK) :
    (fun result => (result.1, prependSchedule earlier result.2)) <$>
        (PqxdhRegistrationJointServerSchedule.source setup codec checks seed serverIndex query).run state =
      (PqxdhRegistrationJointServerSchedule.source setup codec checks seed serverIndex query).run
        (prependSchedule earlier state) := by
  rcases query with (coin | request) | read
  · simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
      PqxdhRegistrationJointSchedule.handler, StateT.run_lift, bind_pure_comp, Functor.map_map]
  · cases request
    case create pin keyId => exact source_create_prefix setup pin keyId earlier state
    case bundle address => exact source_bundle_prefix setup codec address earlier state
    case accept raw =>
      exact onBackend_prefix earlier _ (fun before => source_accept_prefix setup codec checks seed serverIndex raw earlier before) state
    case finish address raw => exact source_finish_prefix setup codec address raw earlier state
    all_goals exact shared_prefix earlier _ state
  · simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
      StateT.run, map_pure]
    exact congrArg pure (read_prefix read earlier state)

/-- The full adaptive source program preserves all earlier identity observations and retains every new observation in original order. -/
theorem source_program_prefix (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (serverIndex : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (earlier : History) (state : PqxdhRegistrationJointSchedule.State KemSK) :
    (fun result => (result.1, prependSchedule earlier result.2)) <$>
        (simulateQ (PqxdhRegistrationJointServerSchedule.source setup codec checks seed serverIndex) program).run state =
      (simulateQ (PqxdhRegistrationJointServerSchedule.source setup codec checks seed serverIndex) program).run
        (prependSchedule earlier state) :=
  simulate_naturality _ _ (fun query before => source_query_prefix setup codec checks seed serverIndex query earlier before)
    program state

/-- Replace only the old private identity transcript; all seeds, KEM state, shared state and owners remain identical. -/
def replaceHistory (history : History) (state : PqxdhRegistrationJointSchedule.State KemSK) :
    PqxdhRegistrationJointSchedule.State KemSK :=
  { state with pool := ({ state.pool.1 with transcript := history }, state.pool.2) }

/-- Keep the target's complete prior log and append exactly the actual current execution's new suffix. -/
def rebase (originalPrefix replacement : History) (after : PqxdhRegistrationJointSchedule.State KemSK) :
    PqxdhRegistrationJointSchedule.State KemSK :=
  replaceHistory (replacement ++ after.pool.1.transcript.drop originalPrefix.length) after

private theorem rebase_from_prefix
    (work : PqxdhRegistrationJointSchedule.State KemSK → ProbComp (Result × PqxdhRegistrationJointSchedule.State KemSK))
    (equivariant : ∀ earlier state, (fun result => (result.1, prependSchedule earlier result.2)) <$> work state =
      work (prependSchedule earlier state))
    (replacement : History) (state : PqxdhRegistrationJointSchedule.State KemSK) :
    (fun result => (result.1, rebase state.pool.1.transcript replacement result.2)) <$> work state =
      work (replaceHistory replacement state) := by
  let cleared := replaceHistory [] state
  have original : prependSchedule state.pool.1.transcript cleared = state := by
    simp [cleared, replaceHistory, prependSchedule, prependPool, prependIdentity]
  have target : prependSchedule replacement cleared = replaceHistory replacement state := by
    simp [cleared, replaceHistory, prependSchedule, prependPool, prependIdentity]
  have originalRun := equivariant state.pool.1.transcript cleared
  rw [original] at originalRun
  rw [← originalRun, Functor.map_map]
  have mapper : ∀ result : Result × PqxdhRegistrationJointSchedule.State KemSK,
      (result.1, rebase state.pool.1.transcript replacement (prependSchedule state.pool.1.transcript result.2)) =
        (result.1, prependSchedule replacement result.2) := by
    intro result
    simp [rebase, replaceHistory, prependSchedule, prependPool, prependIdentity]
  simp only [mapper]
  rw [equivariant replacement cleared, target]

/-- Changing arbitrary old source histories preserves the entire current query and appends its actual new observations after the replacement prefix. No earlier signing query is retroactively removed. -/
theorem source_query_rebase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (serverIndex : Nat) (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (replacement : History) (state : PqxdhRegistrationJointSchedule.State KemSK) :
    (fun result => (result.1, rebase state.pool.1.transcript replacement result.2)) <$>
        (PqxdhRegistrationJointServerSchedule.source setup codec checks seed serverIndex query).run state =
      (PqxdhRegistrationJointServerSchedule.source setup codec checks seed serverIndex query).run
        (replaceHistory replacement state) :=
  rebase_from_prefix _ (fun earlier before => source_query_prefix setup codec checks seed serverIndex query earlier before)
    replacement state

/-- The same exact old-prefix/current-suffix equality holds for every full adaptive source program. -/
theorem source_program_rebase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (serverIndex : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (replacement : History) (state : PqxdhRegistrationJointSchedule.State KemSK) :
    (fun result => (result.1, rebase state.pool.1.transcript replacement result.2)) <$>
        (simulateQ (PqxdhRegistrationJointServerSchedule.source setup codec checks seed serverIndex) program).run state =
      (simulateQ (PqxdhRegistrationJointServerSchedule.source setup codec checks seed serverIndex) program).run
        (replaceHistory replacement state) :=
  rebase_from_prefix _ (fun earlier before => source_program_prefix setup codec checks seed serverIndex program earlier before)
    replacement state

/-- Every supported actual source step appends a concrete suffix after the complete original identity history. -/
theorem source_query_extension (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (serverIndex : Nat) (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (state : PqxdhRegistrationJointSchedule.State KemSK)
    (result : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query × PqxdhRegistrationJointSchedule.State KemSK)
    (supported : result ∈ support
      ((PqxdhRegistrationJointServerSchedule.source setup codec checks seed serverIndex query).run state)) :
    ∃ delta, result.2.pool.1.transcript = state.pool.1.transcript ++ delta := by
  have original : prependSchedule state.pool.1.transcript (replaceHistory [] state) = state := by
    simp [replaceHistory, prependSchedule, prependPool, prependIdentity]
  have prefixLaw := source_query_prefix setup codec checks seed serverIndex query state.pool.1.transcript
    (replaceHistory [] state)
  rw [original] at prefixLaw
  rw [← prefixLaw, support_map] at supported
  obtain ⟨after, _, same⟩ := supported
  exact ⟨after.2.pool.1.transcript, (congrArg (fun out => out.2.pool.1.transcript) same).symm⟩

/-- Rebasing an actually extended log to its own original prefix changes no field. -/
theorem rebase_self (original : History) (state : PqxdhRegistrationJointSchedule.State KemSK)
    (extended : ∃ delta, state.pool.1.transcript = original ++ delta) : rebase original original state = state := by
  obtain ⟨delta, same⟩ := extended
  have history : original ++ state.pool.1.transcript.drop original.length = state.pool.1.transcript := by
    rw [same]
    simp
  simp only [rebase, history, replaceHistory]

/-- The full current source poststate is unchanged when its original prefix is retained. -/
theorem source_query_rebase_self (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (serverIndex : Nat) (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (state : PqxdhRegistrationJointSchedule.State KemSK)
    (result : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query × PqxdhRegistrationJointSchedule.State KemSK)
    (supported : result ∈ support
      ((PqxdhRegistrationJointServerSchedule.source setup codec checks seed serverIndex query).run state)) :
    rebase state.pool.1.transcript state.pool.1.transcript result.2 = result.2 :=
  rebase_self _ _ (source_query_extension setup codec checks seed serverIndex query state result supported)

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.simulate_naturality' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.simulate_naturality

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.lazy_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.lazy_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.pool_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.pool_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.pool_program_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.pool_program_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.bind_naturality' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.bind_naturality

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.auxiliary_prefix' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.auxiliary_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.server_prefix_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.server_prefix_query

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.server_prefix_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.server_prefix_program

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.preparation_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.preparation_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.finish_query_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.finish_query_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.finish_program_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.finish_program_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.source_prepare_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.source_prepare_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.source_accept_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.source_accept_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.onBackend_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.onBackend_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.source_finish_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.source_finish_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.source_create_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.source_create_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.bundle_trace_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.bundle_trace_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.source_bundle_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.source_bundle_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.shared_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.shared_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.read_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.read_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.source_query_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.source_query_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.source_program_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.source_program_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.source_query_rebase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.source_query_rebase

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.source_program_rebase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.source_program_rebase




/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.source_query_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.source_query_extension

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.rebase_self' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.rebase_self

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.source_query_rebase_self' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationHistoryRebase.source_query_rebase_self
