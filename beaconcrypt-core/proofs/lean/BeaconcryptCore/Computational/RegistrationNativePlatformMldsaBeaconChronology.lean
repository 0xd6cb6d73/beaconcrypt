-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaPublicationChronology
import BeaconcryptCore.Computational.RegistrationNativeMldsaBeaconChronology
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBundle
import BeaconcryptCore.Computational.RegistrationNativePlatformInitWriterFrame
import BeaconcryptCore.Computational.RegistrationNativePlatformHashReceipt

/-! The complete actual effectful source bundle retains positionwise native-payload receipts and real private signing attempts, including failed signatures and writer failures. Source continuation equations derive every complete request alignment; actual source writes retain the full Local state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBeaconChronology
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaOpaque (Pool handleSource)
open RegistrationNativeMldsaShared (Local lower)
open RegistrationNativeMldsaChronology (Aligned)
open RegistrationNativeMldsaRequestAlignment (BeaconQuery)
open RegistrationNativePlatformMldsaPublicationChronology (Keeps pure_keeps bind_keeps closed)
open RegistrationNativePlatformMldsaTableProgram (runState)
open RegistrationNativePlatformMldsaProgram (M lift inject coins)
variable {n : Nat} {E Platform Value ι KemSK : Type} {base : OracleSpec ι}
variable (source : RegistrationNativeMldsa.Source)

def receipts (before : Local n KemSK (handleSource source)) := before.2.1.receipts

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- Actual outgoing callbacks append the same raw request and native receipt, with no private signer evaluation shortcut. -/
theorem outgoing (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner (handleSource source))
    (query : RegistrationBeaconInitExecutor.Spec.Domain) (correct : BeaconQuery query) :
    Keeps (Platform := Platform) source (receipts (n := n) (KemSK := KemSK) source)
      (RegistrationNativePlatformMldsaBundle.outgoing setup checks representation created index owner query) := by
  intro before previous pool result aligned supported
  rw [RegistrationNativePlatformMldsaBundle.outgoing, RegistrationNativePlatformMldsaTableProgram.run_inject, support_map] at supported
  obtain ⟨inner, called, same⟩ := supported
  cases same
  exact RegistrationNativeMldsaBeaconChronology.outgoing source setup checks representation created index owner query correct before pool inner aligned called

private def NoSign (work : RegistrationNativeBeaconFrontend.M n KemSK (handleSource source) RegistrationServerRoleBackend.State Value) : Prop :=
  ∀ owners env result, result ∈ support ((work.run owners).run env) → result.2.receipts = env.receipts

private theorem noSign_lift (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value) :
    NoSign source (StateT.lift (StateT.lift work) : RegistrationNativeBeaconFrontend.M n KemSK (handleSource source) RegistrationServerRoleBackend.State Value) := by
  intro owners env result supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, Functor.map_map, support_map] at supported
  obtain ⟨inner, _possible, same⟩ := supported
  cases same
  rfl
private theorem noSign_get : NoSign source
    (get : RegistrationNativeBeaconFrontend.M n KemSK (handleSource source) RegistrationServerRoleBackend.State
      (RegistrationNativeBeaconFrontend.State (handleSource source))) := by
  intro owners env result supported
  simp only [StateT.run_get, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl
private theorem noSign_phase (index : Nat) (phase : RegistrationNativeBeaconFrontend.Phase) :
    NoSign source (RegistrationNativeBeaconFrontend.updatePhase (n := n) (KemSK := KemSK)
      (mldsaSource := handleSource source) (Auxiliary := RegistrationServerRoleBackend.State) index phase) := by
  intro owners env result supported
  simp only [RegistrationNativeBeaconFrontend.updatePhase, StateT.run_modify, StateT.run_pure,
    support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl
private theorem noSign_sample (draw : ProbComp Value) :
    NoSign source (RegistrationNativeBeaconFrontend.sample (n := n) (KemSK := KemSK)
      (mldsaSource := handleSource source) (Auxiliary := RegistrationServerRoleBackend.State) draw) := by
  have lift_bind {A B : Type}
      (work : RegistrationNativeBeaconFrontend.M n KemSK (handleSource source) RegistrationServerRoleBackend.State A)
      (next : A → RegistrationNativeBeaconFrontend.M n KemSK (handleSource source) RegistrationServerRoleBackend.State B)
      (first : NoSign source work) (rest : ∀ value, NoSign source (next value)) : NoSign source (work >>= next) := by
    intro owners env result supported
    simp only [StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, queried, continued⟩ := supported
    exact (rest middle.1.1 middle.1.2 middle.2 result continued).trans (first owners env middle queried)
  induction draw using OracleComp.inductionOn with
  | pure value =>
      intro owners env result supported
      simp only [RegistrationNativeBeaconFrontend.sample, simulateQ_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at supported
      cases supported
      rfl
  | query_bind query next ih =>
      simp only [RegistrationNativeBeaconFrontend.sample, simulateQ_bind, simulateQ_spec_query]
      exact lift_bind _ _ (noSign_lift source _) ih

private theorem native_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (work : RegistrationNativeBeaconFrontend.M n KemSK (handleSource source) RegistrationServerRoleBackend.State Value)
    (law : NoSign source work) :
    Keeps (Platform := Platform) source (receipts source)
      (lift (RegistrationNativePlatformBundleLower.native coins setup checks representation created work)) := by
  apply closed
  intro before previous result supported
  have actual : result.1 ∈ support ((lower setup checks representation created work).run before) :=
    RegistrationNativePlatformHashReceipt.native_support coins _ _ previous result.2 supported
  simp only [lower, StateT.run, support_map] at actual
  obtain ⟨inner, called, same⟩ := actual
  have envEq : inner.1.2.receipts = result.1.2.2.1.receipts := congrArg (fun value => value.2.2.1.receipts) same
  rw [receipts, ← envEq]
  apply law before.1 before.2.1 inner.1
  apply OracleComp.support_simulateQ_run'_subset
    (RegistrationNativeExperiment.trusted setup checks representation created (handleSource source)) _ before.2.2
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst called

private theorem encoder_keeps
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (view : registration.SignedInitView) :
    Keeps source (receipts (n := n) (KemSK := KemSK) source)
      (lift (RegistrationNativePlatformBundleLower.lower
        (RegistrationNativePlatformGenericBundle.encoderWith (source := handleSource source) (Auxiliary := RegistrationServerRoleBackend.State)
          (RegistrationNativePlatformExperiment.writer (n := n) (KemSK := KemSK) (source := handleSource source) writer) view))) := by
  apply closed
  intro before previous result supported
  change result ∈ support (((RegistrationNativePlatformInitWriterFrame.encoder writer view).run before).run previous) at supported
  rw [RegistrationNativePlatformInitWriterFrame.encoder_frame] at supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
  obtain ⟨inner, _called, same⟩ := supported
  exact (congrArg (fun value => receipts source value.1.2) same).symm

attribute [local irreducible] RegistrationNativePlatformBundleLower.native RegistrationNativePlatformMldsaProgram.lift
  RegistrationNativePlatformMldsaBundle.outgoing RegistrationNativePlatformGenericBundle.encoderWith

/-- All actual bundle branches retain the two literal chronological logs through the same persistent writer state. -/
theorem bundle (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) (index : Nat) :
    Keeps source (receipts (n := n) (KemSK := KemSK) source)
      (RegistrationNativePlatformMldsaBundle.bundle setup checks representation created
        (RegistrationNativePlatformGenericBundle.encoderWith (source := handleSource source) (Auxiliary := RegistrationServerRoleBackend.State)
          (RegistrationNativePlatformExperiment.writer (n := n) (KemSK := KemSK) (source := handleSource source) writer)) index) := by
  unfold RegistrationNativePlatformMldsaBundle.bundle
  apply bind_keeps source (receipts source) _ _ (native_keeps source setup checks representation created _ (noSign_get source))
  intro current
  cases current[index]? with
  | none => exact pure_keeps source (receipts source) _
  | some owner =>
    dsimp only
    cases owner.phase with
    | fresh | freshWithCoins _ =>
      apply bind_keeps source (receipts source) _ _ ?_
      · intro oneTime
        apply bind_keeps source (receipts source) _ _
          (RegistrationNativePlatformMldsaPublicationChronology.Beacon.begin_keeps source (receipts source) _ _
            (outgoing source setup checks representation created index owner) (encoder_keeps source writer) _ _ _ _ _)
        intro published
        cases published with
        | fail error | div => exact pure_keeps source (receipts source) _
        | ok answer => cases answer with
          | Err previous => exact pure_keeps source (receipts source) _
          | Ok completed =>
            apply bind_keeps source (receipts source) _ _ (native_keeps source setup checks representation created _ (noSign_phase source index _))
            intro ignored
            exact bind_keeps source (receipts source) _ _ (native_keeps source setup checks representation created _ (noSign_lift source _))
              (fun _ => pure_keeps source (receipts source) _)
      · first | exact pure_keeps source (receipts source) _
              | exact native_keeps source setup checks representation created _ (noSign_sample source _)
    | _ => exact pure_keeps source (receipts source) _

/-- The complete actual source envelope publishes exactly that chronological correspondence into the original global receipt list. -/
theorem sourceBundle (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) (index : Nat)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) (previous : Platform) (pool : Pool source)
    (result : ((RustM (Option Pqxdh.Bytes) × RegistrationNativeExperiment.State n KemSK (handleSource source)) × Platform) × Pool source)
    (aligned : Aligned pool.signing before.server.world.world.2)
    (supported : result ∈ support (runState source
      (RegistrationNativePlatformMldsaBundle.sourceBundle setup checks representation created writer index) before previous pool)) :
    Aligned result.2.signing result.1.1.2.server.world.world.2 := by
  simp only [RegistrationNativePlatformMldsaBundle.sourceBundle, StateT.run, runState,
    RegistrationNativeMldsaTableProgram.evaluate, simulateQ_map, map_apply, support_map] at supported
  obtain ⟨inner, called, same⟩ := supported
  cases same
  exact bundle source setup checks representation created writer index
    (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before)) previous pool inner aligned called

end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBeaconChronology

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBeaconChronology.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBeaconChronology.outgoing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBeaconChronology.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBeaconChronology.bundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBeaconChronology.sourceBundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBeaconChronology.sourceBundle
