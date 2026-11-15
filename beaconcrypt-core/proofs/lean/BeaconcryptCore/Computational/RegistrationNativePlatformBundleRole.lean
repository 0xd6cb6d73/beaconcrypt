-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicationProject
import BeaconcryptCore.Computational.RegistrationNativePlatformInitTupleCache
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicationRole
import BeaconcryptCore.Computational.RegistrationNativeWorldCache
import BeaconcryptCore.Computational.RegistrationNativePlatformHashReceipt
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProgram

/-! Every complete actual source bundle preserves the Server-role signing subsequence through owner selection, all crypto/writer failures and the actual later phase/lifecycle suffix. No public key distinctness or publication-success premise is used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformBundleRole
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaShared (Local lower project)
open RegistrationNativeMldsaRoleFrame (serverReceipts)
open RegistrationNativePlatformMldsaProgram (coins)
open RegistrationNativePlatformPackedState (pack)
variable {n : Nat} {E Platform Value Next ι KemSK : Type} {base : OracleSpec ι}
variable (source : RegistrationNativeMldsa.Source)

private abbrev PWork (Value : Type) := StateT (Local n KemSK source) (StateT Platform ProbComp) Value
private def Keeps (work : PWork (n := n) (KemSK := KemSK) (Platform := Platform) source Value) : Prop :=
  ∀ before previous result, result ∈ support ((work.run before).run previous) →
    serverReceipts (project result.1.2).1 = serverReceipts (project before).1

private theorem pure_keeps (value : Value) : Keeps source
    (pure value : PWork (n := n) (KemSK := KemSK) (Platform := Platform) source Value) := by
  intro before previous result supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl

private theorem bind_keeps (work : PWork (n := n) (KemSK := KemSK) (Platform := Platform) source Value)
    (next : Value → PWork (n := n) (KemSK := KemSK) (Platform := Platform) source Next)
    (first : Keeps source work) (rest : ∀ value, Keeps source (next value)) : Keeps source (work >>= next) := by
  intro before previous result supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, called, continued⟩ := supported
  exact (rest middle.1.1 middle.1.2 middle.2 result continued).trans (first before previous middle called)

/-- Literal complete effectful source Init publication preserves the actual Server-role receipt subsequence. -/
theorem publication (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    Keeps source (RegistrationNativePlatformInitTupleCache.program (n := n) coins setup checks representation created writer index owner oneTime) := by
  intro before previous result supported
  exact RegistrationNativePlatformPublicationRole.outgoing coins setup checks representation created writer index owner oneTime
    before result.1.2 previous result.2 result.1.1 supported

private def NoSign (work : RegistrationNativeBeaconFrontend.M n KemSK (source) RegistrationServerRoleBackend.State Value) : Prop :=
  ∀ owners env result, result ∈ support ((work.run owners).run env) → result.2.receipts = env.receipts

private theorem noSign_lift (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value) :
    NoSign source (StateT.lift (StateT.lift work) : RegistrationNativeBeaconFrontend.M n KemSK (source) RegistrationServerRoleBackend.State Value) := by
  intro owners env result supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, Functor.map_map, support_map] at supported
  obtain ⟨inner, _possible, same⟩ := supported
  cases same
  rfl
private theorem noSign_get : NoSign source
    (get : RegistrationNativeBeaconFrontend.M n KemSK (source) RegistrationServerRoleBackend.State
      (RegistrationNativeBeaconFrontend.State (source))) := by
  intro owners env result supported
  simp only [StateT.run_get, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl
private theorem noSign_phase (index : Nat) (phase : RegistrationNativeBeaconFrontend.Phase) :
    NoSign source (RegistrationNativeBeaconFrontend.updatePhase (n := n) (KemSK := KemSK)
      (mldsaSource := source) (Auxiliary := RegistrationServerRoleBackend.State) index phase) := by
  intro owners env result supported
  simp only [RegistrationNativeBeaconFrontend.updatePhase, StateT.run_modify, StateT.run_pure,
    support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl
private theorem noSign_sample (draw : ProbComp Value) :
    NoSign source (RegistrationNativeBeaconFrontend.sample (n := n) (KemSK := KemSK)
      (mldsaSource := source) (Auxiliary := RegistrationServerRoleBackend.State) draw) := by
  have lift_bind {A B : Type}
      (work : RegistrationNativeBeaconFrontend.M n KemSK (source) RegistrationServerRoleBackend.State A)
      (next : A → RegistrationNativeBeaconFrontend.M n KemSK (source) RegistrationServerRoleBackend.State B)
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
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (law : NoSign source work) :
    Keeps source (RegistrationNativePlatformBundleLower.native (m := StateT Platform ProbComp) coins setup checks representation created work) := by
  intro before previous result supported
  have actual : result.1 ∈ support ((lower setup checks representation created work).run before) :=
    RegistrationNativePlatformHashReceipt.native_support coins _ _ previous result.2 supported
  have retained : result.1.2.2.1.receipts = before.2.1.receipts := by
    simp only [lower, StateT.run, support_map] at actual
    obtain ⟨inner, called, same⟩ := actual
    have envEq : inner.1.2.receipts = result.1.2.2.1.receipts := congrArg (fun value => value.2.2.1.receipts) same
    rw [← envEq]
    apply law before.1 before.2.1 inner.1
    apply OracleComp.support_simulateQ_run'_subset
      (RegistrationNativeExperiment.trusted setup checks representation created source) _ before.2.2
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst called
  change serverReceipts result.1.2.2.1.receipts = serverReceipts before.2.1.receipts
  rw [retained]

attribute [local irreducible] RegistrationNativePlatformBundleLower.native RegistrationNativePlatformGenericBundle.encoderWith

/-- All actual source bundle selection, failed publication and later phase/World branches preserve Server-role receipts. -/
theorem bundle (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) (index : Nat) :
    Keeps source (RegistrationNativePlatformBundleLower.bundle (n := n) coins setup checks representation created
      (RegistrationNativePlatformGenericBundle.encoderWith (source := source) (Auxiliary := RegistrationServerRoleBackend.State)
        (RegistrationNativePlatformExperiment.writer (n := n) (KemSK := KemSK) (source := source) writer)) index) := by
  unfold RegistrationNativePlatformBundleLower.bundle
  apply bind_keeps source _ _ (native_keeps source setup checks representation created _ (noSign_get source))
  intro current
  cases current[index]? with
  | none => exact pure_keeps source _
  | some owner =>
    dsimp only
    cases owner.phase with
    | fresh | freshWithCoins _ =>
      apply bind_keeps source _ _ ?_
      · intro oneTime
        apply bind_keeps source _ _ (publication source setup checks representation created writer index owner oneTime)
        intro published
        cases published with
        | fail error | div => exact pure_keeps source _
        | ok answer => cases answer with
          | Err previous => exact pure_keeps source _
          | Ok completed =>
            apply bind_keeps source _ _ (native_keeps source setup checks representation created _ (noSign_phase source index _))
            intro ignored
            exact bind_keeps source _ _ (native_keeps source setup checks representation created _ (noSign_lift source _))
              (fun _ => pure_keeps source _)
      · first | exact pure_keeps source _ | exact native_keeps source setup checks representation created _ (noSign_sample source _)
    | _ => exact pure_keeps source _

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- Literal complete native source bundle execution preserves Server-role receipts at its actual returned native/platform cut. -/
theorem native_bundle (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) (index : Nat)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : Platform)
    (result : (RustM (Option Pqxdh.Bytes) × RegistrationNativeExperiment.State n KemSK source) × Platform)
    (supported : result ∈ support
      (((RegistrationNativePlatformExperiment.bundle coins setup checks representation created source writer index).run before).run previous)) :
    serverReceipts (RegistrationNativeMldsaShared.nativeProject result.1.2).1 =
      serverReceipts (RegistrationNativeMldsaShared.nativeProject before).1 := by
  rw [← RegistrationNativePlatformBundleLower.sourceBundle_actual] at supported
  simp only [RegistrationNativePlatformBundleLower.sourceBundle, StateT.run, map_apply, support_map] at supported
  obtain ⟨⟨⟨reply, current⟩, platform⟩, called, same⟩ := supported
  cases same
  exact bundle source setup checks representation created writer index
    (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before)) previous ((reply, current), platform) called

end BeaconcryptCore.Computational.RegistrationNativePlatformBundleRole

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundleRole.publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundleRole.publication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundleRole.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundleRole.bundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundleRole.native_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundleRole.native_bundle
