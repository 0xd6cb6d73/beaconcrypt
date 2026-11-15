-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedRetained
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleSelectorSample
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleVisitorReceipt
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorMaskedVisitorSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedJournalSurvival
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBundleReceipt
/-! A proof-only sampler retains the actual first-selector receipt jointly with the same normalized bundle reply and full poststate. Erasing that receipt recovers the literal callback exactly. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedCollector
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformIdentityCtxKeyJournal (Whole drop owners)
open RegistrationNativeStageTrace (Call Path Executed)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reserve
local notation "wire" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire RegistrationNativePlatformConcreteSource.wire
local notation "frontend" => RegistrationNativePlatformIdentityCtxTyped.handler setup checks wire route representation created credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer
local notation "actual" => RegistrationNativePlatformIdentityCtxSigningSource.typedHandler setup.joint frontend


local notation "NativeState" => RegistrationNativeIdentityMain.State n KemSK source × Platform
local notation "Mode" => RegistrationNativeIdentityCensorCompiler.Mode
local notation "Private" => RegistrationNativeIdentityCensorSource.State
local notation "current(" placeholder ")" => RegistrationNativeIdentityCensorAdaptivePostselection.normalized setup checks wire route representation created credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper reserve placeholder
local notation "callback(" selected "," position "," placeholder ")" => RegistrationNativeIdentityCensorPublicClient.callback selected position placeholder current(placeholder)



variable {A : Type}
local notation "FullState" => RegistrationNativeIdentityCensorEdOutgoingSource.Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := source)
local notation "PlainState" => RegistrationNativePlatformIdentityCtxMain.Full n KemSK Platform source
local notation "target" => RegistrationNativeIdentityCensorVisitorCanonicalJournal.getTarget (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := source)
local notation "published" => RegistrationNativeIdentityCensorAdaptivePostselection.published (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := source)
local notation "impl(" selected "," position "," placeholder ")" => RegistrationNativeIdentityCensorBundlePrefix.marked setup.joint selected position placeholder true current(placeholder)
local notation "sample(" selected "," position "," placeholder ")" => RegistrationNativeIdentityCensorBundleSelectorSample.sample setup checks route representation created credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder
local notation "retained(" selected "," position "," placeholder ")" => RegistrationNativeIdentityCensorBundleBoundaryPair.retained setup checks wire route representation created credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder true

omit primitives in
def PlainEvent (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (result : Option (RegistrationNativeIdentityCensorBundleVisitorReceipt.PlainReceipt A FullState PlainState)) : Prop :=
  result.elim False (fun result=>∃seed,result.1.2.1.2.pool.seeds[selected]?=some seed ∧
    RegistrationNativeIdentityCensorIssuedRetained.Good joint selected seed result.1.2.1 (some (result.2.1,some result.2.2)))

omit primitives in
def Event (joint : PqxdhJointIdentity.Primitives) (selected : Nat)
    (result : Option (RegistrationNativeIdentityCensorBundleVisitorReceipt.Receipt A FullState PlainState
      (RegistrationNativeIdentityCensorBundleSelectorSample.Receipt (n := n) (KemSK := KemSK) (Platform := Platform) (source := source)))) : Prop :=
  PlainEvent joint selected (RegistrationNativeIdentityCensorBundleVisitorReceipt.forget result)

private theorem positive_probability (selected position accept index : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (next : TypedSpec.Range (.inr (.bundle index)) → OracleComp TypedSpec A) (before : FullState)
    (leading : List (Call TypedSpec PlainState)) (seed : PqxdhJointIdentity.IdentitySeed)
    (row : before.2.pool.seeds[selected]?=some seed) :
    Pr{let result←(retained(selected,position,placeholder) accept index next (before,RegistrationNativeIdentityCensorVisitorFold.count leading))}[
      RegistrationNativeIdentityCensorIssuedRetained.Good setup.joint selected seed before result]=
    Pr{let result←(RegistrationNativeIdentityCensorBundleVisitorReceipt.positivePlain impl(selected,position,placeholder) target published accept index next before leading)}[
      PlainEvent setup.joint selected result] := by
  classical
  unfold RegistrationNativeIdentityCensorBundleBoundaryPair.retained RegistrationNativeIdentityCensorBundleVisitorReceipt.positivePlain
  rw [show (impl(selected,position,placeholder) (.inr (.bundle index))).run before=
      RegistrationNativeIdentityCensorAdaptivePostselection.call setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder true (.inr (.bundle index)) before from
    RegistrationNativeIdentityCensorPublicSource.current setup.joint selected position placeholder true current(placeholder) (.inr (.bundle index)) before]
  simp only [bind_map_left]
  apply prEvent_bind_congr
  intro kept
  unfold RegistrationNativeIdentityCensorAdaptivePostselection.cut
  cases stopped : published (.inr (.bundle index)) kept.1 kept.2 with
  | true=>simp only [ite_true,map_pure,RegistrationNativeIdentityCensorIssuedRetained.Good,PlainEvent,Option.elim_none]
  | false=>
    simp only [Bool.false_eq_true,ite_false]
    rw [RegistrationNativeIdentityCensorMaskedVisitorSource.visit_eq setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      selected position placeholder true accept (next kept.1) kept.2 (RegistrationNativeIdentityCensorVisitorFold.count leading)]
    simp only [prEvent_map]
    apply prEvent_congr
    intro found
    cases found with
    | none=>simp [PlainEvent,RegistrationNativeIdentityCensorIssuedRetained.Good]
    | some found=>
      simp only [Option.map_some,PlainEvent,Option.elim_some,row,Option.some.injEq]
      constructor
      · intro good;exact ⟨seed,rfl,good⟩
      · rintro ⟨other,equal,good⟩
        cases equal
        exact good

private theorem positive_none (selected position accept index : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (next : TypedSpec.Range (.inr (.bundle index)) → OracleComp TypedSpec A) (before : FullState)
    (leading : List (Call TypedSpec PlainState)) (row : before.2.pool.seeds[selected]?=none) :
    Pr{let result←(RegistrationNativeIdentityCensorBundleVisitorReceipt.positivePlain impl(selected,position,placeholder) target published accept index next before leading)}[
      PlainEvent setup.joint selected result]=0 := by
  apply prEvent_eq_zero_of_forall_mem_support
  intro result reached failed
  simp only [RegistrationNativeIdentityCensorBundleVisitorReceipt.positivePlain,mem_support_bind_iff] at reached
  obtain ⟨kept,_called,reached⟩ := reached
  split at reached
  · simp only [mem_support_pure_iff] at reached
    subst result
    cases failed
  · rw [support_map] at reached
    obtain ⟨found,_following,rfl⟩ := reached
    cases found with
    | none=>cases failed
    | some found=>
      obtain ⟨seed,stored,_good⟩ := failed
      rw [row] at stored
      cases stored

/-- Original retained row gating is exactly the positive before-b split observation, with the same complete before/after states and packet. -/
theorem run_probability (selected position accept : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (work : OracleComp TypedSpec A) (before : Whole n KemSK Platform source) :
    Pr{let result←(RegistrationNativeIdentityCensorIssuedRetained.run setup checks route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper reserve selected position accept placeholder true work before)}[
        RegistrationNativeIdentityCensorIssuedRetained.Event setup.joint selected result]=
    Pr{let result←(RegistrationNativeIdentityCensorBundleVisitorReceipt.splitPlain impl(selected,position,placeholder)
      RegistrationNativeIdentityCensorActualHashSource.project target published position accept work
      (RegistrationNativeIdentityCensorPrefixOwned.lift placeholder
        ({knownInputs:=before.2.2.2} : Mode) (drop before)) [] 0)}[PlainEvent setup.joint selected result] := by
  classical
  unfold RegistrationNativeIdentityCensorIssuedRetained.run RegistrationNativeIdentityCensorBundleVisitorReceipt.splitPlain
    RegistrationNativeIdentityCensorIssuedPrefixImage.markedPrefix
  apply prEvent_bind_congr
  intro mark
  cases kind : mark.1 with
  | returned value=>
    cases mark.2.1.2.pool.seeds[selected]? <;> simp only [RegistrationNativeIdentityCensorIssuedRetained.Event,PlainEvent,Option.elim_none,prEvent_pure,ite_false]
  | bundle index next=>
    cases row : mark.2.1.2.pool.seeds[selected]? with
    | none=>
      rw [positive_none setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
        selected position accept index placeholder next mark.2.1 mark.2.2 row]
      simp only [RegistrationNativeIdentityCensorIssuedRetained.Event,Option.elim_none,prEvent_pure,ite_false]
    | some seed=>
      simp only [bind_pure_comp,prEvent_map,RegistrationNativeIdentityCensorIssuedRetained.Event,Option.elim_some]
      exact positive_probability setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
        selected position accept index placeholder next mark.2.1 mark.2.2 seed row

noncomputable def collect (selected position accept : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (work : OracleComp TypedSpec A) (before : Whole n KemSK Platform source) :=
  RegistrationNativeIdentityCensorBundleVisitorReceipt.collect impl(selected,position,placeholder)
    RegistrationNativeIdentityCensorActualHashSource.project target published sample(selected,position,placeholder) position accept work
    (RegistrationNativeIdentityCensorPrefixOwned.lift placeholder ({knownInputs:=before.2.2.2} : Mode) (drop before)) [] 0

omit primitives in
private theorem law_probability {T : Type} (left right : ProbComp T) (law : LazyOracleDiscard.LawEq left right)
    (event : T → Prop) : Pr{let result←left}[event result]=Pr{let result←right}[event result] := by
  let : MeasurableSpace T := ⊤
  have equal := law T (fun value=>pure value)
  simp only [bind_pure] at equal
  exact (EvalDistEq.of_evalDist_eq equal) event

/-- The actual retained event is exactly the whole before-accept collector event with the same jointly sampled b selector receipt. Public early accepts and unused later work are handled by the proved lossless law. -/
theorem probability (selected position accept : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature)
    (work : OracleComp TypedSpec A) (before : Whole n KemSK Platform source) :
    Pr{let result←(RegistrationNativeIdentityCensorIssuedRetained.run setup checks route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper reserve selected position accept placeholder true work before)}[
        RegistrationNativeIdentityCensorIssuedRetained.Event setup.joint selected result]=
    Pr{let result←(collect setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      selected position accept placeholder work before)}[Event setup.joint selected result] := by
  classical
  rw [run_probability]
  let initial : FullState := RegistrationNativeIdentityCensorPrefixOwned.lift placeholder ({knownInputs:=before.2.2.2} : Mode) (drop before)
  have erasedReceipt := RegistrationNativeIdentityCensorBundleVisitorReceipt.split_erasure impl(selected,position,placeholder)
    RegistrationNativeIdentityCensorActualHashSource.project target published sample(selected,position,placeholder)
      (fun index current=>RegistrationNativeIdentityCensorBundleSelectorSample.marginal setup checks route representation created credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder index current)
      position accept work initial [] 0
  rw [←erasedReceipt,prEvent_map]
  change Pr{let result←(RegistrationNativeIdentityCensorBundleVisitorReceipt.split impl(selected,position,placeholder)
    RegistrationNativeIdentityCensorActualHashSource.project target published sample(selected,position,placeholder) position accept work initial [] 0)}[
      Event setup.joint selected result]=_
  apply law_probability
  exact RegistrationNativeIdentityCensorBundleVisitorReceipt.current_source setup.joint selected position accept placeholder true current(placeholder)
    sample(selected,position,placeholder) work initial [] 0 rfl rfl

variable {V : Type}
/-- The unchanged original same-run fixed i/a/b event is bounded by the actual whole before-accept collector, retaining its literal b selector receipt jointly. -/
theorem bound (serverKeyId : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) V)
    (budget : PqxdhDeploymentInterface.Budget) (before : Whole n KemSK Platform source) (empty : owners before=[])
    (zero : before.1.2.nextBundle=0) (good : RegistrationNativePlatformIdentityCtxKeyJournal.Good setup.joint before)
    (selected position accept : Nat) (placeholder : PqxdhEd25519EufCma.Ed25519Signature) :
    Pr{let result←(RegistrationNativeIdentityCensorIssuedCutProbability.coupled setup.joint frontend position
      (RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKeyId bounds mode work) before)}[
        RegistrationNativeIdentityCensorIssuedCutProbability.Matched setup.joint wire budget selected accept position result] ≤
    Pr{let result←(collect setup checks route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper reserve
      selected position accept placeholder (RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKeyId bounds mode work) before)}[
        Event setup.joint selected result] := by
  rw [←probability]
  exact RegistrationNativeIdentityCensorIssuedRetained.bound setup checks route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reserve serverKeyId bounds mode work budget before empty zero good selected position accept placeholder

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedCollector
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedCollector.run_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedCollector.run_probability

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedCollector.probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedCollector.probability

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedCollector.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorIssuedCollector.bound
