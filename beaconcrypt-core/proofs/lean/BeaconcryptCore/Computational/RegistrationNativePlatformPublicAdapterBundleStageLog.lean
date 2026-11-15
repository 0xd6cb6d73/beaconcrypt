-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundlePublication
/-! The same Bundle primitive request tree retains its exact original publication packet and a joint chronological source-operation log. Erasure returns the original common sampler, and the physical source projection preserves actual hash requests and replies, including refusals and prior observations. The retired Beacon ML-sign fallback performs no source operation and appends no observation; Server signing observers are unchanged. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageLog
open BeaconcryptCore.Refinement
open RegistrationNativePlatformPublicAdapterSourceTrace (Stage recorded)
open RegistrationNativePlatformSdkReification (Backend backend)
variable {n :Nat} {I KemSK E P Log :Type} {base :OracleSpec I} {mlSource :RegistrationNativeMldsa.Source}
local notation "Native"=>RegistrationNativeExperiment.State n KemSK mlSource
local notation "Base"=>StateT P ProbComp
abbrev Spec (E :Type):=RegistrationNativePlatformWriter.Spec E

def observation :(query :(Spec E).Domain)→(Spec E).Range query→List Stage
  | .inl (.inl (.hash request)),reply=>RegistrationNativePlatformPublicAdapterSourceTrace.signingObservation (.hash request) reply
  | .inl (.inl (.sign _ _ _)),_=>[]
  | .inl (.inr _),_ | .inr _,_=>[]

section ActualObservation
variable {S : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
omit [LawfulMonad m] in
private theorem observation_hash_same {Encoded : Type}
    (left right : QueryImpl RegistrationBeaconInitExecutor.Spec m)
    (hashes : ∀ request, left (.inl (.hash request)) = right (.inl (.hash request)))
    (encode : registration.InitView → m (RustM (core.option.Option Encoded)))
    (pending : registration.BeaconInitHash) :
    RegistrationNativePlatformBeaconPublication.fromHash left encode pending =
      RegistrationNativePlatformBeaconPublication.fromHash right encode pending := by
  unfold RegistrationNativePlatformBeaconPublication.fromHash
  cases requested : pending.request <;>
    simp only [RegistrationNativePlatformBeaconPublication.continueWith]
  case ok request => rw [hashes request]

omit [LawfulMonad m] in
private theorem observation_ed_same {Encoded : Type}
    (left right : QueryImpl RegistrationBeaconInitExecutor.Spec m)
    (hashes : ∀ request, left (.inl (.hash request)) = right (.inl (.hash request)))
    (signatures : ∀ request, left (.inr request) = right (.inr request))
    (encode : registration.InitView → m (RustM (core.option.Option Encoded)))
    (pending : registration.BeaconEd25519Signing) :
    RegistrationNativePlatformBeaconPublication.fromEd left encode pending =
      RegistrationNativePlatformBeaconPublication.fromEd right encode pending := by
  conv_lhs => rw [RegistrationNativePlatformBeaconPublication.fromEd.eq_def]
  conv_rhs => rw [RegistrationNativePlatformBeaconPublication.fromEd.eq_def]
  cases requested : pending.request <;>
    simp only [RegistrationNativePlatformBeaconPublication.continueWith]
  case ok request =>
    rw [signatures request]
    apply bind_congr
    intro reply
    cases resumed : pending.resume reply with
    | fail error | div => rfl
    | ok effect => cases effect with
      | Ed25519SigningRequested next => exact observation_ed_same left right hashes signatures encode next
      | HashRequested next => exact observation_hash_same left right hashes encode next
      | _ => rfl
termination_by RegistrationBeaconInitExecutor.edRank pending
decreasing_by exact RegistrationBeaconInitExecutor.ed_rank pending reply next resumed

omit [LawfulMonad m] in
private theorem observation_begin_same {Encoded : Type}
    (left right : QueryImpl RegistrationBeaconInitExecutor.Spec m)
    (hashes : ∀ request, left (.inl (.hash request)) = right (.inl (.hash request)))
    (signatures : ∀ request, left (.inr request) = right (.inr request))
    (encode : registration.InitView → m (RustM (core.option.Option Encoded)))
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (scalar : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) :
    RegistrationNativePlatformBeaconPublication.begin left encode control inputs scalar pin =
      RegistrationNativePlatformBeaconPublication.begin right encode control inputs scalar pin := by
  unfold RegistrationNativePlatformBeaconPublication.begin
  cases started : registration.begin_beacon_init control inputs scalar pin <;>
    simp only [RegistrationNativePlatformBeaconPublication.continueWith]
  case ok effect =>
    cases effect <;> first
      | rfl
      | exact observation_ed_same left right hashes signatures encode _


/-- Retiring the unused Beacon ML fallback observation preserves the complete actual Init publication, including every reply, state and chronological log. -/
theorem begin_observation (implementation : QueryImpl (Spec E) (StateT S m)) (note : Stage → Log)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (scalar : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) :
    simulateQ (recorded implementation (fun query reply => (observation query reply).map note))
      (RegistrationNativePlatformWriter.begin E control inputs scalar pin) =
    simulateQ (recorded implementation (fun query reply => match query with
      | .inl (.inl request) => (RegistrationNativePlatformPublicAdapterSourceTrace.signingObservation request reply).map note
      | .inl (.inr _) | .inr _ => []))
      (RegistrationNativePlatformWriter.begin E control inputs scalar pin) := by
  rw [RegistrationNativePlatformWriter.begin_interpret, RegistrationNativePlatformWriter.begin_interpret]
  apply observation_begin_same
  · intro request
    rfl
  · intro request
    rfl
end ActualObservation

variable (coins :QueryImpl unifSpec (StateT P ProbComp))
variable (setup :PqxdhServerAuthExperiment.Setup base KemSK) (checks :PqxdhServerAuthExperiment.Checks)
variable (representation :RegistrationServerRoleBackend.ConvertedIdentity setup) (created :PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (writer :QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
variable (index :Nat) (owner :RegistrationNativeBeaconFrontend.Owner mlSource)

noncomputable def native :QueryImpl (Spec E) (StateT Native Base)
  | .inl query=>RegistrationNativeBundleInterpretation.outgoing coins setup checks representation created writer index owner query
  | .inr query=>StateT.lift (writer query)

private theorem native_tree (scalar :PqxdhJointGapDh.ScalarBytes) :
    simulateQ (native coins setup checks representation created writer index owner)
      (RegistrationNativePlatformWriter.begin E ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
        ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)⟩ owner.pin)=
      RegistrationNativeBundleLifetime.tree (n:=n) coins setup checks representation created writer index owner scalar :=by
  rw [RegistrationNativePlatformWriter.begin_interpret,RegistrationNativeBundleLifetime.tree_lower]
  congr 1
  funext signed
  change simulateQ (fun query=>StateT.lift (writer query)) _=_
  rw [RegistrationNativeBundleInterpretation.encoder_source]
  exact simulateQ_liftTarget writer _

noncomputable def physical (note :Stage→Log) (identity :PqxdhJointIdentity.IdentitySeed) (control :pqxdh.BeaconFresh) (inputs :pqxdh.BeaconStartInputs)
    (oneTime :pqxdh.BeaconCoins) (pin :session.ServerAuthenticationPin) :
    StateT (Backend n KemSK×List Log) Base (RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))) :=
  simulateQ (recorded (RegistrationNativePlatformPublicAdapterBundlePublication.handler coins setup checks representation created writer identity)
    (fun query reply=>(observation query reply).map note))
    (RegistrationNativePlatformWriter.begin E control inputs oneTime pin)

theorem source (note :Stage→Log) (scalar :PqxdhJointGapDh.ScalarBytes) (before :Native×List Log) :
    Prod.map id (Prod.map backend id) <$>
      (simulateQ (recorded (native coins setup checks representation created writer index owner)
        (fun query reply=>(observation query reply).map note))
        (RegistrationNativePlatformWriter.begin E ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
          ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)⟩ owner.pin)).run before=
      (physical coins setup checks representation created writer note owner.identitySeed
        ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
        ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)⟩ owner.pin).run (backend before.1,before.2) :=by
  apply RegistrationNativePlatformPublicAdapterSourceTrace.source
  intro query current
  cases query with
  | inl query=>exact RegistrationNativePlatformPublicAdapterBundleSigning.outgoing_platform coins setup checks representation created writer index owner query current
  | inr query=>
    simp only [native,RegistrationNativePlatformPublicAdapterBundlePublication.handler,StateT.run_lift,bind_pure_comp,Functor.map_map]
    rfl

theorem erase (note :Stage→Log) (identity :PqxdhJointIdentity.IdentitySeed) (control :pqxdh.BeaconFresh) (inputs :pqxdh.BeaconStartInputs)
    (oneTime :pqxdh.BeaconCoins) (pin :session.ServerAuthenticationPin)
    (before :Backend n KemSK×List Log) :
    Prod.map id Prod.fst <$>
      (physical coins setup checks representation created writer note identity control inputs oneTime pin).run before=
      (RegistrationNativePlatformPublicAdapterBundlePublication.program coins setup checks representation created writer identity
        control inputs oneTime pin).run before.1 :=by
  exact RegistrationNativePlatformPublicAdapterSourceTrace.erase _ _ _ before

noncomputable def runner (note :Stage→Log) (scalar :PqxdhJointGapDh.ScalarBytes) (before :Native) (previous :P) (journal :List Log) :
    ProbComp (((RegistrationNativePlatformExtractedSdkBundle.Publication×Native)×P)×List Log) :=
  (fun result=>(((result.1.1,result.1.2.1),result.2),result.1.2.2)) <$>
    ((simulateQ (recorded (native coins setup checks representation created writer index owner)
      (fun query reply=>(observation query reply).map note))
      (RegistrationNativePlatformWriter.begin E ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
        ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)⟩ owner.pin)).run (before,journal)).run previous

/-- The actual supported Bundle runner keeps its complete publication, native World/receipt state, persistent platform state and exact chronological log under the corrected observer. -/
theorem runner_observation (note :Stage→Log) (scalar :PqxdhJointGapDh.ScalarBytes) (before :Native) (previous :P) (journal :List Log) :
    runner coins setup checks representation created writer index owner note scalar before previous journal =
  (fun result=>(((result.1.1,result.1.2.1),result.2),result.1.2.2)) <$>
    ((simulateQ (recorded (native coins setup checks representation created writer index owner)
      (fun query reply=>match query with
      | .inl (.inl request)=>(RegistrationNativePlatformPublicAdapterSourceTrace.signingObservation request reply).map note
      | .inl (.inr _) | .inr _=>[]))
      (RegistrationNativePlatformWriter.begin E ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
        ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)⟩ owner.pin)).run (before,journal)).run previous
 :=by
  unfold runner
  rw [begin_observation]

theorem runner_erase (note :Stage→Log) (scalar :PqxdhJointGapDh.ScalarBytes) (before :Native) (previous :P) (journal :List Log) :
    Prod.fst <$>runner coins setup checks representation created writer index owner note scalar before previous journal=
      RegistrationNativePlatformExtractedSdkBundle.withCoinsRunner coins setup checks representation created writer index owner scalar before previous :=by
  have kept:=congrArg (fun work=>work.run previous)
    (RegistrationNativePlatformPublicAdapterSourceTrace.erase
      (native coins setup checks representation created writer index owner)
      (fun query reply=>(observation query reply).map note)
      (RegistrationNativePlatformWriter.begin E ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
        ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)⟩ owner.pin) (before,journal))
  rw [native_tree] at kept
  simpa only [runner,RegistrationNativePlatformExtractedSdkBundle.withCoinsRunner,StateT.run_map,Functor.map_map,Prod.map,id_eq] using kept


theorem runner_source (note :Stage→Log) (scalar :PqxdhJointGapDh.ScalarBytes) (before :Native) (previous :P) (journal :List Log) :
    (fun result=>(((result.1.1.1,backend result.1.1.2),result.1.2),result.2)) <$>
      runner coins setup checks representation created writer index owner note scalar before previous journal=
      (fun result=>(((result.1.1,result.1.2.1),result.2),result.1.2.2)) <$>
        ((physical coins setup checks representation created writer note owner.identitySeed
          ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
          ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)⟩ owner.pin).run (backend before,journal)).run previous :=by
  have same:=congrArg (fun work=>work.run previous)
    (source coins setup checks representation created writer index owner note scalar (before,journal))
  simpa only [runner,StateT.run_map,Functor.map_map,Prod.map,id_eq] using
    congrArg (fun distribution=>(fun result=>(((result.1.1,result.1.2.1),result.2),result.1.2.2)) <$>distribution) same

noncomputable def freshRunner (note :Stage→Log) (before :Native) (previous :P) (journal :List Log) :
    ProbComp ((((PqxdhJointGapDh.ScalarBytes×RegistrationNativePlatformExtractedSdkBundle.Publication)×Native)×P)×List Log) :=do
  let sampled←((RegistrationNativeBundleLifetime.sample coins setup checks representation created writer).run before).run previous
  let result←runner coins setup checks representation created writer index owner note sampled.1.1 sampled.1.2 sampled.2 journal
  pure ((((sampled.1.1,result.1.1.1),result.1.1.2),result.1.2),result.2)

/-- Fresh sampling and every failed/successful publication prefix retain the complete original joint result and log. -/
theorem freshRunner_observation (note :Stage→Log) (before :Native) (previous :P) (journal :List Log) :
    freshRunner coins setup checks representation created writer index owner note before previous journal = (do
      let sampled←((RegistrationNativeBundleLifetime.sample coins setup checks representation created writer).run before).run previous
      let result←(fun result=>(((result.1.1,result.1.2.1),result.2),result.1.2.2)) <$>
          ((simulateQ (recorded (native coins setup checks representation created writer index owner)
            (fun query reply=>match query with
            | .inl (.inl request)=>(RegistrationNativePlatformPublicAdapterSourceTrace.signingObservation request reply).map note
            | .inl (.inr _) | .inr _=>[]))
            (RegistrationNativePlatformWriter.begin E ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
              ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey sampled.1.1)⟩ owner.pin)).run (sampled.1.2,journal)).run sampled.2
      pure ((((sampled.1.1,result.1.1.1),result.1.1.2),result.1.2),result.2)) :=by
  unfold freshRunner
  simp_rw [runner_observation]

theorem freshRunner_erase (note :Stage→Log) (before :Native) (previous :P) (journal :List Log) :
    Prod.fst <$>freshRunner coins setup checks representation created writer index owner note before previous journal=
      RegistrationNativePlatformExtractedSdkBundle.freshRunner coins setup checks representation created writer index owner before previous :=by
  unfold freshRunner RegistrationNativePlatformExtractedSdkBundle.freshRunner RegistrationNativeBundleLifetime.fresh_tree
  simp only [map_bind,StateT.run_bind,StateT.run_pure]
  apply bind_congr
  rintro ⟨⟨scalar,current⟩,nextP⟩
  have same:=congrArg (fun distribution=>(fun result=>(((scalar,result.1.1),result.1.2),result.2)) <$>distribution)
    (runner_erase coins setup checks representation created writer index owner note scalar current nextP journal)
  simpa only [RegistrationNativePlatformExtractedSdkBundle.withCoinsRunner,map_pure,Functor.map_map,bind_pure_comp] using same

noncomputable def freshPhysical (note :Stage→Log) (identity :PqxdhJointIdentity.IdentitySeed) (control :pqxdh.BeaconFresh) (inputs :pqxdh.BeaconStartInputs)
    (pin :session.ServerAuthenticationPin) (before :Backend n KemSK)
    (previous :P) (journal :List Log) :
    ProbComp ((((PqxdhJointGapDh.ScalarBytes×RegistrationNativePlatformExtractedSdkBundle.Publication)×Backend n KemSK)×P)×List Log) :=do
  let sampled←((RegistrationNativePlatformPublicAdapterBundleSigning.sample coins setup checks representation created PqxdhJointGapDh.sampleScalar).run before).run previous
  let result←((physical coins setup checks representation created writer note identity control inputs
    ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey sampled.1.1)⟩ pin).run (sampled.1.2,journal)).run sampled.2
  pure ((((sampled.1.1,result.1.1),result.1.2.1),result.2),result.1.2.2)

theorem freshRunner_source (note :Stage→Log) (before :Native) (previous :P) (journal :List Log) :
    (fun result=>(((result.1.1.1,backend result.1.1.2),result.1.2),result.2)) <$>
      freshRunner coins setup checks representation created writer index owner note before previous journal=
      freshPhysical coins setup checks representation created writer note owner.identitySeed
        ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner) owner.pin
        (backend before) previous journal :=by
  have first:=congrArg (fun work=>work.run previous)
    (RegistrationNativePlatformPublicAdapterBundleSigning.sample_source (source:=mlSource)
      coins setup checks representation created PqxdhJointGapDh.sampleScalar before)
  unfold freshRunner RegistrationNativeBundleLifetime.sample freshPhysical
  rw [RegistrationNativeBundleInterpretation.legacy]
  simp only [map_bind,StateT.run_map] at first ⊢
  rw [←first,bind_map_left]
  apply bind_congr
  rintro ⟨⟨scalar,current⟩,nextP⟩
  have same:=congrArg (fun distribution=>(fun result=>((((scalar,result.1.1.1),result.1.1.2),result.1.2),result.2)) <$>distribution)
    (runner_source coins setup checks representation created writer index owner note scalar current nextP journal)
  simpa only [map_pure,bind_pure_comp,Functor.map_map,Prod.map,id_eq] using same

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageLog
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageLog.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageLog.source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageLog.erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageLog.erase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageLog.runner_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageLog.runner_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageLog.runner_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageLog.runner_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageLog.freshRunner_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageLog.freshRunner_erase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageLog.freshRunner_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageLog.freshRunner_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageLog.begin_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageLog.begin_observation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageLog.runner_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageLog.runner_observation
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageLog.freshRunner_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageLog.freshRunner_observation
