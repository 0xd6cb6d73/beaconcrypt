-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorTargetSource
import BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordProviderSource
import BeaconcryptCore.Computational.RegistrationNativePlatformG3CheckedUniformSource
/-! Original broad LR good eligibility implies selected installation receipts on the same actual warm reserved-provider record game. Genuine startup supplies its original pin and cold frontend, and the sampled profile supplies capacity and selected-row evidence. RecordView is projected only to derive the support-level property; the probability comparison retains its unchanged complete result and arbitrary observer, including RecordView and persistent platform state. No provider identity, physical hiddenness or whole callback premise is introduced. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformTestsSelected
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (Budget)
open PqxdhKemIndCca
open RegistrationNativePlatformPublicRecordOpaqueInitialized (Context prior)
open RegistrationNativePlatformG3RecordKem (Result)
variable {I KemSK Platform E Value : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (reservePackets : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
local notation "wire" => RegistrationNativePlatformConcreteSource.wire
local notation "canonical" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reservePackets

omit primitive in
private theorem profile_selected (count : Nat) (selected : Fin (count+1))
    (profile : RegistrationNativeSecretWordAliasOuter.Profile KemSK)
    (supported : profile ∈ support (RegistrationNativeG3NativeRepeatUniformBound.prior setup.baseImpl setup.kem count selected)) :
    count ≤ profile.pairs.length ∧ ∃ chosen, profile.pairs[selected.val]?=some chosen ∧ chosen.1=profile.publicKey := by
  simp only [RegistrationNativeG3NativeRepeatUniformBound.prior,mem_support_bind_iff] at supported
  obtain ⟨chosen,_chosen,others,_others,pair,_pair,returned⟩ := supported
  rw [mem_support_pure_iff] at returned
  cases returned
  refine ⟨by simp only [List.length_ofFn];omega,chosen,?_,rfl⟩
  simpa only [List.nil_append,List.length_nil,Nat.zero_add] using PqxdhLiveKemSelection.selected_index [] selected chosen others

omit primitive in
private theorem startup_pin {n : Nat} (identity : PqxdhJointIdentity.PublicIdentity)
    (started : RegistrationNativePublicStartup.Started source) (after : PqxdhRecordLiftWorld.State n)
    (supported : (some started,after) ∈ support ((RegistrationNativePublicStartupFrame.startup setup source ensureInit identityIndex serverKeyId identity).run PqxdhRecordLiftWorld.initial)) :
    PqxdhRefinement.absBytes started.frontend.server.pin.binding.identity_public_key=identity.ed25519.toList := by
  simp only [RegistrationNativePublicStartupFrame.startup,StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨constructed,_constructed,continued⟩ := supported
  cases built : constructed.1.1 with
  | none => simp only [built,StateT.run_pure,mem_support_pure_iff] at continued;cases continued
  | some created =>
    simp only [built,StateT.run_bind,mem_support_bind_iff] at continued
    obtain ⟨generated,_generated,continued⟩ := continued
    cases sampled : generated.1 with
    | none => simp only [sampled,StateT.run_pure,mem_support_pure_iff] at continued;cases continued
    | some credential =>
      simp only [sampled,StateT.run_bind,mem_support_bind_iff] at continued
      obtain ⟨installed,_installed,returned⟩ := continued
      rw [StateT.run_pure,mem_support_pure_iff] at returned
      cases returned
      exact PqxdhRootTableInitialization.rootArray_bytes identity.ed25519

omit primitive in
private theorem prior_pin (budget : Budget) (context : Context source (budget.cap 4+budget.cap 5))
    (started : RegistrationNativePublicStartup.Started source)
    (supported : context ∈ support (prior setup source ensureInit identityIndex serverKeyId budget))
    (success : context.2.2.2.1=some started) :
    PqxdhRefinement.absBytes started.frontend.server.pin.binding.identity_public_key=(setup.joint.publicKeys context.1).ed25519.toList := by
  simp only [prior,mem_support_bind_iff,mem_support_pure_iff] at supported
  obtain ⟨seed,_seed,scalar,_scalar,materials,_materials,initialized,reached,rfl⟩ := supported
  apply startup_pin setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed) started initialized.2
  simpa only [←success] using reached

omit primitive in
def Good (budget : Budget) (target : Fin budget.accept × Fin budget.capacity)
    (filter : RegistrationNativeLorEvents.Filter Value) (result : Result source (budget.cap 4+budget.cap 5) Value Platform) : Prop :=
  match result.2 with
  | none => False
  | some completed => RegistrationNativeLorCanonical.GoodAt setup.source.crypto canonical serverKeyId budget filter target completed.1.1.1

omit primitive in
def Selected (budget : Budget) (candidate : MlKemSharedSecret) (result : Result source (budget.cap 4+budget.cap 5) Value Platform) : Prop :=
  match result.2 with
  | none => False
  | some completed => RegistrationNativeLorSelectedTests.TestsSelected setup.source.crypto canonical serverKeyId
      completed.1.1.1.2 completed.1.2.events
      (RegistrationNativeInstallKernelStorage.Selected setup result.1.1 result.1.2.1 candidate)

/-- The original warm materialized outcome has its own same-run selected receipts; terminal record data is retained on that exact outcome. -/
theorem fixed_selected (budget : Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (target : Fin budget.accept × Fin budget.capacity) (previous : Platform) (candidate : MlKemSharedSecret)
    (context : Context source (budget.cap 4+budget.cap 5))
    (sampled : context ∈ support (prior setup source ensureInit identityIndex serverKeyId budget))
    (profile : RegistrationNativeSecretWordAliasOuter.Profile KemSK)
    (reserved : profile ∈ support (RegistrationNativeG3NativeRepeatUniformBound.prior setup.baseImpl setup.kem budget.create target.2))
    (result : Result source (budget.cap 4+budget.cap 5) Value Platform)
    (supported : result ∈ support (RegistrationNativePlatformG3RecordProviderSource.full setup checks wire route source serverKeyId target.1.val
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary
      (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem target.2.val profile.pairs profile.publicKey profile.challenge candidate)
      none budget target.2.val previous candidate context))
    (filter : RegistrationNativeLorEvents.Filter Value)
    (good : Good setup source serverKeyId budget target filter result) :
    Selected setup source serverKeyId budget candidate result := by
  classical
  cases success : context.2.2.2.1 with
  | none =>
    simp only [RegistrationNativePlatformG3RecordProviderSource.full,success,mem_support_pure_iff] at supported
    cases supported
    exact good.elim
  | some started =>
    have cold := RegistrationNativePlatformPublicRecordOpaqueInitialized.prior_fields setup source ensureInit identityIndex serverKeyId budget context started sampled success
    have pin := prior_pin setup source ensureInit identityIndex serverKeyId budget context started sampled success
    obtain ⟨capacity,chosen,chosenAt,publicEq⟩ := profile_selected setup budget.create target.2 profile reserved
    let reference := RegistrationNativeOpenKeyKemEarlySource.reference setup.baseImpl setup.kem target.2.val profile.pairs profile.publicKey profile.challenge candidate
    have law := RegistrationNativePlatformG3RecordProviderSource.provider_source setup checks wire route source serverKeyId target.1.val
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary
      (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem target.2.val profile.pairs profile.publicKey profile.challenge candidate)
      none budget bounded target.2.val previous candidate context
    rw [support_eq_of_evalDistEq law] at supported
    change result ∈ support ((simulateQ reference (RegistrationNativePlatformG3RecordKem.after setup checks wire route source serverKeyId target.1.val view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget target.2.val previous context)).run' ((PqxdhLiveKemBirth.empty,none),∅)) at supported
    have projected := Set.mem_image_of_mem (RegistrationNativePlatformG3RecordKem.drop source) supported
    rw [←support_map] at projected
    have dropped := congrArg (fun requests => (simulateQ reference requests).run' ((PqxdhLiveKemBirth.empty,none),∅))
      (RegistrationNativePlatformG3RecordKem.after_drop setup checks wire route source serverKeyId target.1.val view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer bounds mode adversary budget target.2.val previous context)
    simp only [simulateQ_map,StateT.run'_map'] at dropped
    rw [dropped] at projected
    simp only [RegistrationNativePlatformG3InitializedKem.after,success,simulateQ_map,StateT.run'_map',support_map] at projected
    obtain ⟨native,called,equal⟩ := projected
    rcases result with ⟨resultContext,optional⟩
    cases optional with
    | none => exact good.elim
    | some completed =>
      change (context,some native)=(resultContext,some completed.1) at equal
      have contextEq := congrArg Prod.fst equal
      cases contextEq
      have nativeEq := Option.some.inj (congrArg Prod.snd equal)
      cases nativeEq
      have fixed := RegistrationNativePlatformG3CheckedUniformSource.fixed_source setup checks wire source
        (RegistrationNativeMldsa.owned source started.credential) target.2.val target.1.val (setup.dh.publicKey context.2.1)
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route context.1 context.2.1
        (setup.joint.staticDh context.1 (setup.dh.publicKey context.2.1)) serverKeyId bounds mode
        (adversary ⟨setup.joint.publicKeys context.1,started.credential.publicKey,serverKeyId⟩)
        (RegistrationNativeG3NativeStartupFields.word started.frontend,previous)
        (RegistrationNativeG3NativeUniformAuditBound.ordinary context.2.2.2.2)
        (by simp only [RegistrationNativeG3NativeStartupFields.word,cold.1,List.map_nil]) target.2.val profile.pairs profile.publicKey profile.challenge candidate
      rw [fixed,support_map] at called
      obtain ⟨aliasResult,aliasSupport,observed⟩ := called
      have wordGood : RegistrationNativeLorCanonical.GoodAt setup.source.crypto canonical serverKeyId budget filter target (aliasResult.1.1.1.1,aliasResult.1.1.1.2) := by
        simpa only [Good,←observed,RegistrationNativePlatformG3CheckedUniformSource.observe,Prod.map_def,id_eq] using good
      let actualClient := RegistrationNativePlatformSecretWordAliasClient.client setup checks wire source
        (RegistrationNativeMldsa.owned source started.credential) target.2.val target.1.val (setup.dh.publicKey context.2.1)
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route
        (RegistrationNativeSecretWordMessage.input setup.joint setup.dh context.1 context.2.1)
        (RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh context.1 (setup.dh.publicKey context.2.1)))
        (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem target.2.val profile.pairs profile.publicKey profile.challenge)
        serverKeyId bounds mode (adversary ⟨setup.joint.publicKeys context.1,started.credential.publicKey,serverKeyId⟩)
        (RegistrationNativeG3NativeStartupFields.word started.frontend,previous)
        (RegistrationNativeG3NativeUniformAuditBound.ordinary context.2.2.2.2) (RegistrationNativeSecretWordKemPool.empty,none)
      let : MeasurableSpace (RegistrationNativePlatformSecretWordAliasClient.Result source (budget.cap 4+budget.cap 5) KemSK Value Platform) := ⊤
      let : DiscreteMeasurableSpace (RegistrationNativePlatformSecretWordAliasClient.Result source (budget.cap 4+budget.cap 5) KemSK Value Platform) := ⟨fun _ => trivial⟩
      have tableLaw := _root_.EvalDistEq.of_evalDist_eq (RegistrationNativeSecretWordAliasTable.bytes_eager setup.source candidate actualClient).evalDist_eq
      rw [support_eq_of_evalDistEq tableLaw] at aliasSupport
      rw [mem_support_bind_iff] at aliasSupport
      obtain ⟨table,_sampled,aliasSupport⟩ := aliasSupport
      have selected := RegistrationNativePlatformLorSelectedTests.alias_selected setup checks source route
        (RegistrationNativeMldsa.owned source started.credential) context.1 context.2.1 profile.pairs chosen profile.challenge
        (RegistrationNativeSecretWordAliasTable.normalizedFixed table setup.source candidate)
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper reservePackets serverKeyId bounds mode
        (adversary ⟨setup.joint.publicKeys context.1,started.credential.publicKey,serverKeyId⟩) budget target (bounded _) capacity chosenAt
        (RegistrationNativeG3NativeStartupFields.word started.frontend,previous) cold.2.2.1 cold.2.1 pin
        (RegistrationNativeG3NativeUniformAuditBound.ordinary context.2.2.2.2) candidate aliasResult (by simpa only [publicEq] using aliasSupport) filter wordGood
      simpa only [Selected,←observed,RegistrationNativePlatformG3CheckedUniformSource.observe,RegistrationNativeSecretWordCheckedTrace.state,Prod.map_def,id_eq] using selected

/-- Genuine startup and the actual reserved profile discharge cold state, pin, family capacity and selected-row obligations internally. -/
theorem game_selected (budget : Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (target : Fin budget.accept × Fin budget.capacity) (previous : Platform)
    (result : MlKemSharedSecret × Result source (budget.cap 4+budget.cap 5) Value Platform)
    (supported : result ∈ support (RegistrationNativePlatformG3RecordProviderSource.game setup checks wire route source ensureInit identityIndex serverKeyId target.1.val
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget target.2 previous))
    (filter : RegistrationNativeLorEvents.Filter Value)
    (good : Good setup source serverKeyId budget target filter result.2) :
    Selected setup source serverKeyId budget result.1 result.2 := by
  simp only [RegistrationNativePlatformG3RecordProviderSource.game,mem_support_bind_iff,mem_support_pure_iff] at supported
  obtain ⟨context,sampled,profile,reserved,candidate,_candidate,finished,supported,rfl⟩ := supported
  exact fixed_selected setup checks route source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased
    helper reservePackets bounds mode adversary budget bounded target previous candidate context sampled profile reserved finished supported filter good

/-- Original broad eligibility and any observer of the complete same warm result imply its selected-install receipt, with RecordView and persistent platform state left literal. -/
theorem probability (budget : Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (target : Fin budget.accept × Fin budget.capacity) (previous : Platform)
    (filter : RegistrationNativeLorEvents.Filter Value)
    (observe : MlKemSharedSecret → Result source (budget.cap 4+budget.cap 5) Value Platform → Bool) :
    Pr{let pair ← (RegistrationNativePlatformG3RecordProviderSource.game setup checks wire route source ensureInit identityIndex serverKeyId target.1.val
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget target.2 previous)}[
      Good setup source serverKeyId budget target filter pair.2 ∧ observe pair.1 pair.2=true] ≤
    Pr{let pair ← (RegistrationNativePlatformG3RecordProviderSource.game setup checks wire route source ensureInit identityIndex serverKeyId target.1.val
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget target.2 previous)}[
      Selected setup source serverKeyId budget pair.1 pair.2 ∧ observe pair.1 pair.2=true] := by
  classical
  apply prEvent_mono_of_support
  intro result supported winning
  exact ⟨game_selected setup checks route source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased helper
    reservePackets bounds mode adversary budget bounded target previous result supported filter winning.1,winning.2⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformTestsSelected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformTestsSelected.fixed_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformTestsSelected.fixed_selected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformTestsSelected.game_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformTestsSelected.game_selected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformTestsSelected.probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformTestsSelected.probability
