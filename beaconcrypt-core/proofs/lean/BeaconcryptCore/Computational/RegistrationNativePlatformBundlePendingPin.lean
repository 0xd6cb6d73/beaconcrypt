-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinNative
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicationPendingPin
import BeaconcryptCore.Computational.RegistrationNativePlatformBundleCoherence

/-! The actual free dynamic bundle preserves the expected binding of each retained pending capability against its same owner's stored Server pin. The proof follows arbitrary source encoder and crypto replies, preserving all failed paths, owner metadata and the complete local environment. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformBundlePendingPin
open RegistrationNativeBeaconFrontend
open RegistrationWorldAgreementCompiler (EnvState)
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordPendingPinNative (Coherent Holds)
open RegistrationNativePlatformBeaconPublication
variable {n : Nat} {I Q KemSK Auxiliary Value Next Encoded : Type} {base : OracleSpec I} {target : OracleSpec Q}
variable {source : RegistrationNativeMldsa.Source}
private def SourceKeeps (work : M n KemSK source Auxiliary Value) : Prop :=
  ∀ owners env result, Holds owners → result ∈ support ((work.run owners).run env) → Holds result.1.2

private theorem source_pure_keeps (value : Value) : SourceKeeps (pure value : M n KemSK source Auxiliary Value) := by
  intro owners env result prior supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact prior

private theorem source_bind_keeps {Next : Type} (work : M n KemSK source Auxiliary Value)
    (next : Value → M n KemSK source Auxiliary Next) (first : SourceKeeps work)
    (rest : ∀ value, SourceKeeps (next value)) : SourceKeeps (work >>= next) := by
  intro owners env result prior supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  exact rest middle.1.1 middle.1.2 middle.2 result (first owners env middle prior reached) continued

private theorem source_lift_keeps (work : StateT (EnvState Auxiliary) (OracleComp (Trusted n KemSK)) Value) :
    SourceKeeps (StateT.lift work : M n KemSK source Auxiliary Value) := by
  intro owners env result prior supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
  obtain ⟨middle, _reached, returned⟩ := supported
  cases returned
  exact prior

private theorem source_lift_readonly (work : StateT (EnvState Auxiliary) (OracleComp (Trusted n KemSK)) Value) :
    RegistrationNativeBeaconFootprint.ReadOnly (StateT.lift work : M n KemSK source Auxiliary Value) := by
  intro owners env result supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
  obtain ⟨middle, _reached, returned⟩ := supported
  cases returned
  rfl

private theorem source_readonly_keeps (work : M n KemSK source Auxiliary Value)
    (readonly : RegistrationNativeBeaconFootprint.ReadOnly work) : SourceKeeps work := by
  intro owners env result prior supported
  rw [readonly owners env result supported]
  exact prior

private theorem source_simulate_keeps {Query : Type} {spec : OracleSpec Query}
    (implementation : QueryImpl spec (M n KemSK source Auxiliary))
    (law : ∀ query, SourceKeeps (implementation query)) (work : OracleComp spec Value) :
    SourceKeeps (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact source_pure_keeps value
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact source_bind_keeps _ _ (law query) ih

private theorem source_sample_keeps (work : ProbComp Value) :
    SourceKeeps (sample (n := n) (KemSK := KemSK) (mldsaSource := source) (Auxiliary := Auxiliary) work) :=
  source_simulate_keeps (fun (query : unifSpec.Domain) => effect (.inl query)) (fun _ => source_lift_keeps _) work

private theorem source_sample_readonly (work : ProbComp Value) :
    RegistrationNativeBeaconFootprint.ReadOnly
      (sample (n := n) (KemSK := KemSK) (mldsaSource := source) (Auxiliary := Auxiliary) work) := by
  unfold sample
  apply RegistrationNativeBeaconFootprint.program_readonly
  intro query
  exact source_lift_readonly _

private theorem source_current_keeps (index : Nat) (change : Owner source → Owner source)
    (valid : ∀ owner, Coherent owner → Coherent (change owner)) :
    SourceKeeps ((modify fun owners => match owners[index]? with
      | none => owners
      | some current => owners.set index (change current)) : M n KemSK source Auxiliary Unit) := by
  intro owners env result prior supported
  simp only [StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  cases found : owners[index]? with
  | none => exact prior
  | some owner =>
      intro selected member
      rcases List.mem_or_eq_of_mem_set member with original | rfl
      · exact prior selected original
      · exact valid owner (prior owner (List.mem_of_getElem? found))

private theorem source_log_keeps (index : Nat) (message : Pqxdh.Bytes)
    (signature : PqxdhEd25519EufCma.Ed25519Signature) :
    SourceKeeps (logEd (n := n) (KemSK := KemSK) (mldsaSource := source) (Auxiliary := Auxiliary) index message signature) :=
  source_current_keeps index (fun owner => { owner with edHistory := owner.edHistory ++ [.signed message signature] })
    (fun _ valid => valid)

private theorem source_outgoing_keeps (setup : Setup base KemSK) (index : Nat) (owner : Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    SourceKeeps (outgoing (n := n) (Auxiliary := Auxiliary) setup source index owner query) := by
  classical
  rcases query with (hashRequest | signRequest) | edRequest
  · exact source_lift_keeps _
  · exact source_bind_keeps _ _ (source_sample_keeps _) (fun _ =>
      source_bind_keeps _ _ (source_lift_keeps _) (fun _ => source_pure_keeps _))
  · simp only [outgoing]
    split
    · exact source_bind_keeps _ _ (source_log_keeps index _ _) (fun _ => source_pure_keeps _)
    · exact source_pure_keeps _

private abbrev G (source : RegistrationNativeMldsa.Source) (Auxiliary : Type) (target : OracleSpec Q) (V : Type) :=
  RegistrationNativePlatformGenericBundle.M source Auxiliary (OracleComp target) V
variable {Invariant : State source → Prop}
private def Keeps (work : G source Auxiliary target Value) : Prop :=
  ∀ owners env result, Invariant owners → result ∈ support ((work.run owners).run env) → Invariant result.1.2
private theorem pure_keeps (value : Value) : Keeps (Invariant := Invariant) (pure value : G source Auxiliary target Value) := by
  intro owners env result prior supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact prior
private theorem bind_keeps (work : G source Auxiliary target Value) (next : Value → G source Auxiliary target Next)
    (first : Keeps (Invariant := Invariant) work) (rest : ∀ value, Keeps (Invariant := Invariant) (next value)) : Keeps (Invariant := Invariant) (work >>= next) := by
  intro owners env result prior supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, called, continued⟩ := supported
  exact rest middle.1.1 middle.1.2 middle.2 result (first owners env middle prior called) continued
private theorem lift_keeps (work : StateT (EnvState Auxiliary) (OracleComp target) Value) :
    Keeps (Invariant := Invariant) (StateT.lift work : G source Auxiliary target Value) := by
  intro owners env result prior supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
  obtain ⟨middle, _called, same⟩ := supported
  cases same
  exact prior
private theorem get_keeps : Keeps (Invariant := Invariant) (get : G source Auxiliary target (State source)) := by
  intro owners env result prior supported
  simp only [StateT.run_get, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact prior
private theorem simulate_support {Q : Type} {spec : OracleSpec Q} (impl : QueryImpl spec (OracleComp target))
    (work : OracleComp spec Value) (value : Value) (supported : value ∈ support (simulateQ impl work)) : value ∈ support work := by
  induction work using OracleComp.inductionOn with
  | pure input =>
    simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at supported ⊢
    exact supported
  | query_bind query next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at supported
    obtain ⟨reply, _called, continued⟩ := supported
    rw [mem_support_bind_iff]
    exact ⟨reply, mem_support_query query reply, ih reply continued⟩
private theorem legacy_keeps (impl : QueryImpl (Trusted n KemSK) (OracleComp target))
    (work : M n KemSK source Auxiliary Value)
    (law : ∀ owners env result, Invariant owners → result ∈ support ((work.run owners).run env) → Invariant result.1.2) :
    Keeps (Invariant := Invariant) (RegistrationNativePlatformGenericBundle.liftLegacy impl work) := by
  intro owners env result prior supported
  exact law owners env result prior (simulate_support impl _ result supported)
private theorem continue_keeps {Input : Type} (action : RustM Input)
    (next : Input → G source Auxiliary target (RustM (RegistrationBeaconInitExecutor.Result Encoded)))
    (law : ∀ value, Keeps (Invariant := Invariant) (next value)) : Keeps (Invariant := Invariant) (continueWith action next) := by
  cases action with
  | fail error | div => exact pure_keeps (Invariant := Invariant) _
  | ok value => exact law value
private theorem ready_keeps (encode : registration.SignedInitView → G source Auxiliary target (RustM (core.option.Option Encoded)))
    (law : ∀ view, Keeps (Invariant := Invariant) (encode view)) (pending : registration.BeaconInitReady) : Keeps (Invariant := Invariant) (ready encode pending) := by
  unfold ready
  exact continue_keeps (Invariant := Invariant) _ _ fun view => bind_keeps (Invariant := Invariant) _ _ (law view) fun _ => pure_keeps (Invariant := Invariant) _
private theorem signing_keeps (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (G source Auxiliary target))
    (encode : registration.SignedInitView → G source Auxiliary target (RustM (core.option.Option Encoded)))
    (queries : ∀ query, Keeps (Invariant := Invariant) (impl query)) (encoding : ∀ view, Keeps (Invariant := Invariant) (encode view))
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest) (pending : registration.BeaconMldsaSigning) :
    Keeps (Invariant := Invariant) (fromSigning impl encode payload digest pending) := by
  unfold fromSigning
  apply continue_keeps (Invariant := Invariant) _ _
  intro request
  apply bind_keeps (Invariant := Invariant) _ _ (queries _)
  intro signature
  apply continue_keeps (Invariant := Invariant) _ _
  intro effect
  cases effect <;> first | exact pure_keeps (Invariant := Invariant) _ | exact ready_keeps (Invariant := Invariant) encode encoding _
private theorem hash_keeps (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (G source Auxiliary target))
    (encode : registration.SignedInitView → G source Auxiliary target (RustM (core.option.Option Encoded)))
    (queries : ∀ query, Keeps (Invariant := Invariant) (impl query)) (encoding : ∀ view, Keeps (Invariant := Invariant) (encode view))
    (pending : registration.BeaconInitHash) : Keeps (Invariant := Invariant) (fromHash impl encode pending) := by
  unfold fromHash
  apply continue_keeps (Invariant := Invariant) _ _
  intro request
  apply bind_keeps (Invariant := Invariant) _ _ (queries _)
  intro digest
  apply continue_keeps (Invariant := Invariant) _ _
  intro effect
  cases effect <;> first | exact pure_keeps (Invariant := Invariant) _ | exact signing_keeps (Invariant := Invariant) impl encode queries encoding _ _ _
private theorem fingerprint_keeps (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (G source Auxiliary target))
    (encode : registration.SignedInitView → G source Auxiliary target (RustM (core.option.Option Encoded)))
    (queries : ∀ query, Keeps (Invariant := Invariant) (impl query)) (encoding : ∀ view, Keeps (Invariant := Invariant) (encode view))
    (pending : registration.BeaconFingerprint) : Keeps (Invariant := Invariant) (fromFingerprint impl encode pending) := by
  unfold fromFingerprint
  apply continue_keeps (Invariant := Invariant) _ _
  intro request
  apply bind_keeps (Invariant := Invariant) _ _ (queries _)
  intro digest
  apply continue_keeps (Invariant := Invariant) _ _
  intro effect
  cases effect <;> first | exact pure_keeps (Invariant := Invariant) _ | exact hash_keeps (Invariant := Invariant) impl encode queries encoding _
private theorem ed_keeps (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (G source Auxiliary target))
    (encode : registration.SignedInitView → G source Auxiliary target (RustM (core.option.Option Encoded)))
    (queries : ∀ query, Keeps (Invariant := Invariant) (impl query)) (encoding : ∀ view, Keeps (Invariant := Invariant) (encode view))
    (pending : registration.BeaconEd25519Signing) : Keeps (Invariant := Invariant) (fromEd impl encode pending) := by
  rw [fromEd.eq_def]
  apply continue_keeps (Invariant := Invariant) _ _
  intro request
  apply bind_keeps (Invariant := Invariant) _ _ (queries _)
  intro reply
  cases resumed : pending.resume reply with
  | fail error | div => exact pure_keeps (Invariant := Invariant) _
  | ok effect => cases effect with
    | Rejected previous => exact pure_keeps (Invariant := Invariant) _
    | Ed25519SigningRequested next => exact ed_keeps impl encode queries encoding next
    | FingerprintRequested selected => exact fingerprint_keeps (Invariant := Invariant) impl encode queries encoding selected
    | _ => exact pure_keeps (Invariant := Invariant) _
termination_by RegistrationBeaconInitExecutor.edRank pending
decreasing_by exact RegistrationBeaconInitExecutor.ed_rank pending reply next resumed

/-- Every actual source publication stage preserves owner metadata under arbitrary crypto/writer replies, including failure and recursive Ed-signing stages. -/
private theorem publication (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (G source Auxiliary target))
    (encode : registration.SignedInitView → G source Auxiliary target (RustM (core.option.Option Encoded)))
    (queries : ∀ query, Keeps (Invariant := Invariant) (impl query)) (encoding : ∀ view, Keeps (Invariant := Invariant) (encode view))
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize) :
    Keeps (Invariant := Invariant) (begin impl encode control inputs coins pin mldsa) := by
  unfold begin
  apply continue_keeps (Invariant := Invariant) _ _
  intro effect
  cases effect <;> first | exact pure_keeps (Invariant := Invariant) _ | exact ed_keeps (Invariant := Invariant) impl encode queries encoding _


private noncomputable def bundled (impl : QueryImpl (Trusted n KemSK) (OracleComp target))
    (setup : Setup base KemSK)
    (encode : registration.SignedInitView → G source Auxiliary target (RustM (core.option.Option Encoded)))
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    G source Auxiliary target (RustM (Option Encoded)) := do
  let published ← begin (fun query => RegistrationNativePlatformGenericBundle.liftLegacy impl (outgoing setup source index owner query))
    encode ⟨owner.pin.binding⟩ (inputs setup owner) ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin owner.mldsa.publicKey
  match published with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err _) => pure (.ok none)
  | .ok (.Ok finished) => do
    RegistrationNativePlatformGenericBundle.liftLegacy impl (updatePhase index (.initSent finished.pending oneTime))
    let _ ← RegistrationNativePlatformGenericBundle.liftLegacy impl (effect (.inr (.advanceOwner owner.worldOwner .initSent)))
    pure (.ok (some finished.encoded))

private theorem legacy_modify (impl : QueryImpl (Trusted n KemSK) (OracleComp target))
    (change : State source → State source) :
    RegistrationNativePlatformGenericBundle.liftLegacy impl (modify change : M n KemSK source Auxiliary Unit) = modify change := by
  funext owners env
  rfl

private theorem bundled_keeps (impl : QueryImpl (Trusted n KemSK) (OracleComp target))
    (setup : Setup base KemSK)
    (encode : registration.SignedInitView → G source Auxiliary target (RustM (core.option.Option Encoded)))
    (encoding : ∀ view, Keeps (Invariant := Holds) (encode view))
    (encoding_metadata : ∀ view owners env result, result ∈ support (((encode view).run owners).run env) →
      result.1.2.map RegistrationNativeOwnerFields.metadata = owners.map RegistrationNativeOwnerFields.metadata)
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (owners : State source) (env : EnvState Auxiliary)
    (result : (RustM (Option Encoded) × State source) × EnvState Auxiliary)
    (prior : Holds owners) (found : owners[index]?=some owner)
    (supported : result ∈ support (((bundled impl setup encode index owner oneTime).run owners).run env)) :
    Holds result.1.2 := by
  simp only [bundled, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, called, continued⟩ := supported
  have retained := (publication _ _ (fun query => legacy_keeps impl _ (source_outgoing_keeps setup index owner query))
    encoding _ _ _ _ _) owners env middle prior called
  cases actual : middle.1.1 with
  | fail error | div =>
    simp only [actual, StateT.run_pure, mem_support_pure_iff] at continued
    cases continued
    exact retained
  | ok published => cases published with
    | Err previous =>
      simp only [actual, StateT.run_pure, mem_support_pure_iff] at continued
      cases continued
      exact retained
    | Ok published =>
      have metadata : middle.1.2.map RegistrationNativeOwnerFields.metadata = owners.map RegistrationNativeOwnerFields.metadata := by
        apply (publication (Invariant := fun current => current.map RegistrationNativeOwnerFields.metadata = owners.map RegistrationNativeOwnerFields.metadata)
          _ _ ?_ ?_ _ _ _ _ _) owners env middle rfl called
        · intro query
          apply legacy_keeps (Invariant := fun current => current.map RegistrationNativeOwnerFields.metadata = owners.map RegistrationNativeOwnerFields.metadata) impl _
          intro current environment reached valid possible
          exact (RegistrationNativeOwnerFields.outgoing_metadata setup source index owner (RegistrationBeaconInitExecutor.Spec.query query) current environment reached (by simpa only [simulateQ_spec_query] using possible)).trans valid
        · intro view current environment reached valid possible
          exact (encoding_metadata view current environment reached possible).trans valid
      have same := congrArg (fun roster => roster[index]?) metadata
      simp only [List.getElem?_map, found, Option.map_some] at same
      obtain ⟨current, currentFound, currentMetadata⟩ := Option.map_eq_some_iff.mp same
      have pin : current.pin.binding = owner.pin.binding := congrArg (fun owner => owner.pin.binding) currentMetadata
      have expected := RegistrationNativePlatformPublicationPendingPin.begin_coherent _ encode ⟨owner.pin.binding⟩
        (inputs setup owner) ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin owner.mldsa.publicKey
        published owners middle.1.2 env middle.2 (by simpa only [← actual] using called)
      have installed : Holds (middle.1.2.set index {current with phase:=.initSent published.pending oneTime}) := by
        intro selected member
        rcases List.mem_or_eq_of_mem_set member with original | rfl
        · exact retained selected original
        · change published.pending.control.expected_server_binding = current.pin.binding
          exact expected.trans pin.symm
      simp only [actual, updatePhase, legacy_modify, StateT.run_bind, StateT.run_modify, pure_bind, currentFound] at continued
      exact (bind_keeps (Invariant := Holds) _ _ (legacy_keeps impl _ (source_lift_keeps _)) (fun _ => pure_keeps _))
        (middle.1.2.set index {current with phase:=.initSent published.pending oneTime}) middle.2 result installed continued

private theorem encoder_keeps {E : Type} (view : registration.SignedInitView) :
    Keeps (Invariant := Holds) (RegistrationNativePlatformGenericBundle.encoder (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) E view) :=
  lift_keeps _

private theorem encoder_metadata {E : Type} (view : registration.SignedInitView)
    (owners : State source) (env : EnvState Auxiliary)
    (result : (RustM (core.option.Option (alloc.vec.Vec U8)) × State source) × EnvState Auxiliary)
    (possible : result ∈ support (((RegistrationNativePlatformGenericBundle.encoder (n := n) (KemSK := KemSK) E view).run owners).run env)) :
    result.1.2.map RegistrationNativeOwnerFields.metadata = owners.map RegistrationNativeOwnerFields.metadata := by
  simp only [RegistrationNativePlatformGenericBundle.encoder,RegistrationNativePlatformGenericBundle.encoderWith,
    StateT.run_lift,bind_pure_comp,StateT.run_map,Functor.map_map,support_map] at possible
  obtain ⟨bytes,_called,equal⟩ := possible
  cases equal
  rfl

/-- Every reached free source bundle retains the actual stored-pin relation, independently of arbitrary writer failures. -/
theorem program {E : Type} (setup : Setup base KemSK) (index : Nat)
    (owners : State source) (env : EnvState Auxiliary)
    (result : (RustM (Option (alloc.vec.Vec U8)) × State source) × EnvState Auxiliary)
    (prior : Holds owners)
    (supported : result ∈ support (((RegistrationNativePlatformGenericBundle.program (n := n) E setup source index).run owners).run env)) :
    Holds result.1.2 := by
  simp only [RegistrationNativePlatformGenericBundle.program, RegistrationNativePlatformGenericBundle.bundle,
    StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases found : owners[index]? with
  | none =>
    simp only [found, StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
    exact prior
  | some owner =>
    simp only [found] at supported
    cases phase : owner.phase <;> simp only [phase] at supported
    all_goals try { simp only [StateT.run_pure, mem_support_pure_iff] at supported; cases supported; exact prior }
    case fresh =>
      simp only [StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨sampled, draw, continued⟩ := supported
      have raw := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ draw
      have unchanged := source_sample_readonly _ owners env sampled raw
      have valid : Holds sampled.1.2 := by rw [unchanged]; exact prior
      apply bundled_keeps (RegistrationNativePlatformGenericBundle.trustedLift (E := E)) setup
        (RegistrationNativePlatformGenericBundle.encoder E) (encoder_keeps) (encoder_metadata) index owner sampled.1.1 sampled.1.2 sampled.2 result valid
        (by rw [unchanged]; exact found)
      simp only [bundled,StateT.run_bind,mem_support_bind_iff]
      obtain ⟨published,called,tail⟩ := continued
      refine ⟨published,called,?_⟩
      cases actual : published.1.1 with
      | fail error | div => simpa only [actual] using tail
      | ok reply => cases reply <;> simpa only [actual] using tail
    case freshWithCoins oneTime =>
      apply bundled_keeps (RegistrationNativePlatformGenericBundle.trustedLift (E := E)) setup
        (RegistrationNativePlatformGenericBundle.encoder E) (encoder_keeps) (encoder_metadata) index owner oneTime owners env result prior found
      simp only [bundled,StateT.run_bind,mem_support_bind_iff] at supported ⊢
      obtain ⟨published,called,tail⟩ := supported
      refine ⟨published,called,?_⟩
      cases actual : published.1.1 with
      | fail error | div => simpa only [actual] using tail
      | ok reply => cases reply <;> simpa only [actual] using tail

end BeaconcryptCore.Computational.RegistrationNativePlatformBundlePendingPin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundlePendingPin.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundlePendingPin.program
