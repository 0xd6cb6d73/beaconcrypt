-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicationCoherence
import BeaconcryptCore.Computational.RegistrationNativePlatformBundleMetadata
import BeaconcryptCore.Computational.RegistrationNativeBeaconCoherence

/-! Effectful source Init publication establishes control/server-pin coherence for every retained owner. Arbitrary crypto/writer replies and failed prefixes preserve prior coherent phases. Successful publication installs only the reached coherent pending capability; no encoder or pending-honesty premise is exposed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformBundleCoherence
open RegistrationNativeBeaconFrontend
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeBeaconCoherence (Holds PhaseCoherent)
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePlatformBeaconPublication
variable {ι κ KemSK Auxiliary Value Next Encoded : Type} {base : OracleSpec ι} {target : OracleSpec κ} {n : Nat}
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

private theorem source_current_keeps (index : Nat) (change : Owner source → Owner source)
    (valid : ∀ owner, PhaseCoherent owner.phase → PhaseCoherent (change owner).phase) :
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

private theorem source_phase_keeps (index : Nat) (phase : Phase) (valid : PhaseCoherent phase) :
    SourceKeeps (updatePhase (n := n) (KemSK := KemSK) (mldsaSource := source) (Auxiliary := Auxiliary) index phase) :=
  source_current_keeps index (fun owner => { owner with phase }) (fun _ _ => valid)

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
  · exact source_pure_keeps (core.option.Option.None : RegistrationSigningShared.SignReply)
  · simp only [outgoing]
    split
    · exact source_bind_keeps _ _ (source_log_keeps index _ _) (fun _ => source_pure_keeps _)
    · exact source_pure_keeps _


private abbrev G (source : RegistrationNativeMldsa.Source) (Auxiliary : Type) (target : OracleSpec κ) (V : Type) :=
  RegistrationNativePlatformGenericBundle.M source Auxiliary (OracleComp target) V
private def Keeps (work : G source Auxiliary target Value) : Prop :=
  ∀ owners env result, Holds owners → result ∈ support ((work.run owners).run env) → Holds result.1.2
private theorem pure_keeps (value : Value) : Keeps (pure value : G source Auxiliary target Value) := by
  intro owners env result prior supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact prior
private theorem bind_keeps (work : G source Auxiliary target Value) (next : Value → G source Auxiliary target Next)
    (first : Keeps work) (rest : ∀ value, Keeps (next value)) : Keeps (work >>= next) := by
  intro owners env result prior supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, called, continued⟩ := supported
  exact rest middle.1.1 middle.1.2 middle.2 result (first owners env middle prior called) continued
private theorem lift_keeps (work : StateT (EnvState Auxiliary) (OracleComp target) Value) :
    Keeps (StateT.lift work : G source Auxiliary target Value) := by
  intro owners env result prior supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
  obtain ⟨middle, _called, same⟩ := supported
  cases same
  exact prior
private theorem get_keeps : Keeps (get : G source Auxiliary target (State source)) := by
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
    (work : M n KemSK source Auxiliary Value) (law : SourceKeeps work) :
    Keeps (RegistrationNativePlatformGenericBundle.liftLegacy impl work) := by
  intro owners env result prior supported
  exact law owners env result prior (simulate_support impl _ result supported)
private theorem continue_keeps {Input : Type} (action : RustM Input)
    (next : Input → G source Auxiliary target (RustM (RegistrationBeaconInitExecutor.Result Encoded)))
    (law : ∀ value, Keeps (next value)) : Keeps (continueWith action next) := by
  cases action with
  | fail error | div => exact pure_keeps _
  | ok value => exact law value
private theorem ready_keeps (encode : registration.InitView → G source Auxiliary target (RustM (core.option.Option Encoded)))
    (law : ∀ view, Keeps (encode view)) (pending : registration.BeaconInitReady) : Keeps (ready encode pending) := by
  unfold ready
  exact continue_keeps _ _ fun view => bind_keeps _ _ (law view) fun _ => pure_keeps _
private theorem hash_keeps (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (G source Auxiliary target))
    (encode : registration.InitView → G source Auxiliary target (RustM (core.option.Option Encoded)))
    (queries : ∀ query, Keeps (impl query)) (encoding : ∀ view, Keeps (encode view))
    (pending : registration.BeaconInitHash) : Keeps (fromHash impl encode pending) := by
  unfold fromHash
  apply continue_keeps _ _
  intro request
  apply bind_keeps _ _ (queries _)
  intro digest
  apply continue_keeps _ _
  intro effect
  cases effect <;> first | exact pure_keeps _ | exact ready_keeps encode encoding _
private theorem ed_keeps (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (G source Auxiliary target))
    (encode : registration.InitView → G source Auxiliary target (RustM (core.option.Option Encoded)))
    (queries : ∀ query, Keeps (impl query)) (encoding : ∀ view, Keeps (encode view))
    (pending : registration.BeaconEd25519Signing) : Keeps (fromEd impl encode pending) := by
  rw [fromEd.eq_def]
  apply continue_keeps _ _
  intro request
  apply bind_keeps _ _ (queries _)
  intro reply
  cases resumed : pending.resume reply with
  | fail error | div => exact pure_keeps _
  | ok effect => cases effect with
    | Rejected previous => exact pure_keeps _
    | Ed25519SigningRequested next => exact ed_keeps impl encode queries encoding next
    | HashRequested selected => exact hash_keeps impl encode queries encoding selected
    | _ => exact pure_keeps _
termination_by RegistrationBeaconInitExecutor.edRank pending
decreasing_by exact RegistrationBeaconInitExecutor.ed_rank pending reply next resumed

/-- Every actual source publication stage preserves owner metadata under arbitrary crypto/writer replies, including failure and recursive Ed-signing stages. -/
private theorem publication (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (G source Auxiliary target))
    (encode : registration.InitView → G source Auxiliary target (RustM (core.option.Option Encoded)))
    (queries : ∀ query, Keeps (impl query)) (encoding : ∀ view, Keeps (encode view))
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) :
    Keeps (begin impl encode control inputs coins pin) := by
  unfold begin
  apply continue_keeps _ _
  intro effect
  cases effect <;> first | exact pure_keeps _ | exact ed_keeps impl encode queries encoding _


private noncomputable def bundled (impl : QueryImpl (Trusted n KemSK) (OracleComp target))
    (setup : Setup base KemSK)
    (encode : registration.InitView → G source Auxiliary target (RustM (core.option.Option Encoded)))
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    G source Auxiliary target (RustM (Option Encoded)) := do
  let published ← begin (fun query => RegistrationNativePlatformGenericBundle.liftLegacy impl (outgoing setup source index owner query))
    encode ⟨owner.pin.binding⟩ (inputs setup owner) ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin
  match published with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err _) => pure (.ok none)
  | .ok (.Ok finished) => do
    RegistrationNativePlatformGenericBundle.liftLegacy impl (updatePhase index (.initSent finished.pending oneTime))
    let _ ← RegistrationNativePlatformGenericBundle.liftLegacy impl (effect (.inr (.advanceOwner owner.worldOwner .initSent)))
    pure (.ok (some finished.encoded))

private theorem bundled_keeps (impl : QueryImpl (Trusted n KemSK) (OracleComp target))
    (setup : Setup base KemSK)
    (encode : registration.InitView → G source Auxiliary target (RustM (core.option.Option Encoded)))
    (encoding : ∀ view, Keeps (encode view)) (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    Keeps (bundled impl setup encode index owner oneTime) := by
  intro owners env result prior supported
  simp only [bundled, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, called, continued⟩ := supported
  have retained := (publication _ _ (fun query => legacy_keeps impl _ (source_outgoing_keeps setup index owner query))
    encoding _ _ _ _) owners env middle prior called
  cases actual : middle.1.1 with
  | fail error | div =>
    simp only [actual, StateT.run_pure, support_pure, Set.mem_singleton_iff] at continued
    cases continued
    exact retained
  | ok answer => cases answer with
    | Err previous =>
      simp only [actual, StateT.run_pure, support_pure, Set.mem_singleton_iff] at continued
      cases continued
      exact retained
    | Ok published =>
      have valid := RegistrationNativePlatformPublicationCoherence.begin_coherent _ encode ⟨owner.pin.binding⟩
        (inputs setup owner) ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin
        published owners middle.1.2 env middle.2 (by simpa only [← actual] using called)
      simp only [actual] at continued
      exact (bind_keeps _ _ (legacy_keeps impl _ (source_phase_keeps index (.initSent published.pending oneTime) valid))
        (fun _ => bind_keeps _ _ (legacy_keeps impl _ (source_lift_keeps _)) (fun _ => pure_keeps _)))
        middle.1.2 middle.2 result retained continued

/-- The free actual source bundle preserves all pending control/pin equations, with arbitrary crypto and writer replies. -/
theorem program {E : Type} (setup : Setup base KemSK) (index : Nat)
    (owners : State source) (env : EnvState Auxiliary) (prior : Holds owners)
    (result : (RustM (Option (alloc.vec.Vec U8)) × State source) × EnvState Auxiliary)
    (supported : result ∈ support (((RegistrationNativePlatformGenericBundle.program (n := n) E setup source index).run owners).run env)) :
    Holds result.1.2 := by
  have law : Keeps (RegistrationNativePlatformGenericBundle.program (n := n) (Auxiliary := Auxiliary) E setup source index) := by
    unfold RegistrationNativePlatformGenericBundle.program RegistrationNativePlatformGenericBundle.bundle
    apply bind_keeps _ _ get_keeps
    intro current
    cases current[index]? with
    | none => exact pure_keeps _
    | some owner =>
      dsimp only
      cases owner.phase with
      | fresh | freshWithCoins _ =>
        apply bind_keeps _ _ ?_
        · intro oneTime
          exact bundled_keeps _ setup _ (fun _ => lift_keeps _) index owner oneTime
        · first | exact pure_keeps _ | exact legacy_keeps _ _ (source_sample_keeps _)
      | _ => exact pure_keeps _
  exact law owners env result prior supported

private theorem map_apply {S X Y : Type} (f : X → Y) (work : StateT S ProbComp X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

private theorem interpreted_support {Q N P A : Type} {spec : OracleSpec Q}
    (implementation : QueryImpl spec (StateT N (StateT P ProbComp)))
    (work : OracleComp spec A) (value : A) (before after : N) (previous next : P)
    (supported : ((value, after), next) ∈ support (((simulateQ implementation work).run before).run previous)) : value ∈ support work := by
  induction work using OracleComp.inductionOn generalizing before after previous next with
  | pure input =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
    rw [support_pure, Set.mem_singleton_iff]
    exact supported.1.1
  | query_bind query continuation ih =>
    simp only [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨⟨⟨reply, middle⟩, platform⟩, _called, continued⟩ := supported
    rw [mem_support_bind_iff]
    exact ⟨reply, mem_support_query query reply, ih reply middle after platform next continued⟩

/-- Actual Platform source bundle preserves every retained pending control/pin equation on all outcomes. -/
theorem native_bundle {E Platform : Type} (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (source : RegistrationNativeMldsa.Source)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (index : Nat) (before after : RegistrationNativeExperiment.State n KemSK source) (previous next : Platform)
    (reply : RustM (Option Pqxdh.Bytes)) (prior : Holds before.beacons)
    (supported : ((reply, after), next) ∈ support
      (((RegistrationNativePlatformExperiment.bundle coins setup checks representation created source writer index).run before).run previous)) :
    Holds after.beacons := by
  simp only [RegistrationNativePlatformExperiment.bundle, StateT.run, bind_pure_comp, map_apply, support_map] at supported
  obtain ⟨⟨raw, platform⟩, called, same⟩ := supported
  have beacons : after.beacons = raw.1.1.2 := (congrArg (fun value => value.1.2.beacons) same).symm
  have original := interpreted_support (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer)
    (((RegistrationNativePlatformGenericBundle.program E setup source index).run before.beacons).run
      (RegistrationWorldAgreementCompiler.erase before.server.world)) raw.1 before raw.2 previous platform called
  rw [beacons]
  exact program setup index before.beacons (RegistrationWorldAgreementCompiler.erase before.server.world) prior raw.1 original

end BeaconcryptCore.Computational.RegistrationNativePlatformBundleCoherence

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundleCoherence.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundleCoherence.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundleCoherence.native_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundleCoherence.native_bundle
