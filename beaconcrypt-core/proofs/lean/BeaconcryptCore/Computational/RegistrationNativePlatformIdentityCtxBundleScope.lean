-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOutgoingFold
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleRun

/-! Full lookup, optional scalar dispatch, publication and terminal phase effects satisfy the actual NoKem scope. This makes the existing exact Main closing lens compositional for the complete bundle, including all failed replies and dynamic P writers. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleScope
open RegistrationNativeIdentityFrontend (M Trusted Ambient Owner)
open RegistrationNativePlatformIdentityCtxOutgoingScope (NativeAllowed NativeWork Work)
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {I KemSK Auxiliary Platform Value Next E : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}

private theorem mapped {Index : Type} {queries : OracleSpec Index} {A B : Type}
    (work : OracleComp queries A) (change : A → B) (predicate : Index → Prop)
    (allowed : work.AllQueriesSatisfy predicate) : (change <$> work).AllQueriesSatisfy predicate := by
  rw [map_eq_bind_pure_comp]
  exact allQueriesSatisfy_bind allowed (fun _ => allQueriesSatisfy_pure _ _)

private theorem native_pure (value : Value) : NativeWork (pure value : M n KemSK Auxiliary source Value) := by
  intro owners env
  simp only [StateT.run_pure]
  trivial

private theorem native_bind (work : M n KemSK Auxiliary source Value) (next : Value → M n KemSK Auxiliary source Next)
    (first : NativeWork work) (later : ∀ value, NativeWork (next value)) : NativeWork (work >>= next) := by
  intro owners env
  rw [StateT.run_bind, StateT.run_bind]
  exact allQueriesSatisfy_bind (first owners env) (fun result => later result.1.1 result.1.2 result.2)

private theorem native_program {Index : Type} {queries : OracleSpec Index}
    (handler : QueryImpl queries (M n KemSK Auxiliary source))
    (law : ∀ query, NativeWork (handler query)) (work : OracleComp queries Value) : NativeWork (simulateQ handler work) := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure] using native_pure value
  | query_bind query next ih =>
    rw [simulateQ_bind, simulateQ_spec_query]
    exact native_bind _ _ (law query) ih

private theorem lifted (work : OracleComp (Trusted n KemSK) Value)
    (allowed : work.AllQueriesSatisfy (NativeAllowed (n := n) (KemSK := KemSK))) :
    NativeWork (StateT.lift (StateT.lift work) : M n KemSK Auxiliary source Value) := by
  intro owners env
  simp only [StateT.run_lift, StateT.run_map, bind_pure_comp, Functor.map_map]
  exact mapped work _ _ allowed

private theorem effect (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    NativeWork (RegistrationNativeIdentityFrontend.effect (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) query) :=
  lifted _ ((allQueriesSatisfy_query_iff _ _).mpr trivial)

private theorem sample (work : ProbComp Value) :
    NativeWork (RegistrationNativeIdentityFrontend.sample (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) work) :=
  native_program (fun query : unifSpec.Domain => RegistrationNativeIdentityFrontend.effect (.inl query))
    (fun _ => effect _) work

private theorem modified (change : RegistrationNativeIdentityFrontend.State source → RegistrationNativeIdentityFrontend.State source) :
    NativeWork (modify change : M n KemSK Auxiliary source Unit) := by
  intro owners env
  simp only [StateT.run_modify, StateT.run_pure]
  trivial

private theorem native_allowed {A : Type} (work : OracleComp (Trusted n KemSK) A)
    (allowed : work.AllQueriesSatisfy (NativeAllowed (n := n) (KemSK := KemSK))) :
    (simulateQ RegistrationNativePlatformIdentityProgram.nativeLift work).AllQueriesSatisfy
      (RegistrationNativePlatformIdentityCtxEnvPatch.Allowed (n := n) (KemSK := KemSK)) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at allowed
    simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativePlatformIdentityProgram.nativeLift]
    exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨allowed.1, fun reply => ih reply (allowed.2 reply)⟩

private theorem lifted_native (work : M n KemSK Auxiliary source Value) (allowed : NativeWork work) :
    Work (RegistrationNativePlatformIdentityProgram.native work : RegistrationNativePlatformIdentityProgram.M n KemSK Auxiliary Platform source Value) := by
  intro owners env platform
  simp only [RegistrationNativePlatformIdentityProgram.native, StateT.run]
  exact mapped _ _ _ (native_allowed _ (allowed owners env))

private theorem pure_work (value : Value) :
    Work (pure value : RegistrationNativePlatformIdentityProgram.M n KemSK Auxiliary Platform source Value) := by
  intro owners env platform
  simp only [StateT.run_pure]
  trivial

private theorem bind_work (work : RegistrationNativePlatformIdentityProgram.M n KemSK Auxiliary Platform source Value)
    (next : Value → RegistrationNativePlatformIdentityProgram.M n KemSK Auxiliary Platform source Next)
    (first : Work work) (later : ∀ value, Work (next value)) : Work (work >>= next) := by
  intro owners env platform
  rw [StateT.run_bind, StateT.run_bind, StateT.run_bind]
  exact allQueriesSatisfy_bind (first owners env platform)
    (fun result => later result.1.1.1 result.1.1.2 result.1.2 result.2)


/-- Actual success advances the source phase/World slot; all other replies remain pure. No indexed KEM Other capability occurs. -/
theorem next_scope (index : Nat) (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (reply : RegistrationNativePlatformIdentityBundle.Reply) :
    Work (RegistrationNativePlatformIdentityBundle.next (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (Platform := Platform) index owner scalar reply) := by
  cases reply with
  | fail error | div => exact pure_work _
  | ok result => cases result with
    | Err previous => exact pure_work _
    | Ok published =>
      unfold RegistrationNativePlatformIdentityBundle.next
      apply bind_work _ _ (lifted_native _ ?_)
      · intro _
        exact bind_work _ _ (lifted_native _ (effect _)) (fun _ => pure_work _)
      · exact modified _

/-- The literal entire source publication and its actual terminal controller stay inside the derived scope for every writer outcome. -/
theorem bundled (setup : Setup base KemSK) (index : Nat) (owner : Owner source)
    (scalar : PqxdhJointGapDh.ScalarBytes)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    Work (RegistrationNativePlatformIdentityBundle.bundled (n := n) (Auxiliary := Auxiliary) setup index owner scalar writer) := by
  unfold RegistrationNativePlatformIdentityBundle.bundled
  exact bind_work _ _ (RegistrationNativePlatformIdentityCtxOutgoingScope.publication setup index owner writer _)
    (next_scope index owner scalar)

/-- Supplied and sampled one-time material have the same scope; invalid phases never query the writer. -/
theorem start (setup : Setup base KemSK) (index : Nat) (owner : Owner source)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    Work (RegistrationNativePlatformIdentityBundleRun.start (n := n) (Auxiliary := Auxiliary) setup index owner writer) := by
  cases phase : owner.phase with
  | fresh =>
    simp only [RegistrationNativePlatformIdentityBundleRun.start, phase]
    exact bind_work _ _ (lifted_native _ (sample _)) (fun scalar => bundled setup index owner scalar writer)
  | freshWithCoins scalar =>
    simpa only [RegistrationNativePlatformIdentityBundleRun.start, phase, pure_bind] using bundled (n := n) (Auxiliary := Auxiliary) setup index owner scalar writer
  | initSent pending scalar | established completed | aborted aborted =>
    simpa only [RegistrationNativePlatformIdentityBundleRun.start, phase] using
      (pure_work (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (Platform := Platform) (source := source) (.ok none : RustM (Option (alloc.vec.Vec U8))))

/-- Every actual owner lookup and full dynamic bundle callback has the NoKem environment-patch scope, including missing handles. -/
theorem bundle (setup : Setup base KemSK) (index : Nat)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    Work (RegistrationNativePlatformIdentityBundleRun.bundle (n := n) (Auxiliary := Auxiliary) (source := source) setup index writer) := by
  intro owners env platform
  simp only [RegistrationNativePlatformIdentityBundleRun.bundle, StateT.run_bind, StateT.run_get, pure_bind]
  cases selected : owners[index]? with
  | none => trivial
  | some owner => exact start setup index owner writer owners env platform


/-- The actual source publication and terminal state commit distribute through Main without an unrestricted ambient monad-hom premise. -/
theorem bundled_fold (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (index : Nat) (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    RegistrationNativePlatformIdentityCtxMain.beacon (n := n) setup checks representation created
      (RegistrationNativePlatformIdentityBundle.bundled setup index owner scalar writer) =
      (do let reply ← RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
            (simulateQ (RegistrationNativePlatformIdentityPublication.callback (n := n) (Auxiliary := RegistrationServerRoleBackend.State) setup index owner writer)
              (RegistrationNativePlatformWriter.begin E ⟨owner.pin.binding⟩ (RegistrationNativeIdentityFrontend.inputs owner)
                ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)⟩ owner.pin owner.mldsa.publicKey))
          RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
            (RegistrationNativePlatformIdentityBundle.next index owner scalar reply)) := by
  unfold RegistrationNativePlatformIdentityBundle.bundled
  exact RegistrationNativePlatformIdentityCtxOutgoingFold.bind_source setup checks representation created _ _
    (next_scope index owner scalar)

/-- Reading the actual owner roster closes and reopens the native environment exactly; no physical service query or P effect is introduced. -/
theorem get_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit) :
    RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (source := source) (Platform := Platform) setup checks representation created
      get = (fun before => pure (before.1.beacons, before) : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform source (RegistrationNativeIdentityFrontend.State source)) := by
  funext before
  change (RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created get).run before = _
  rw [RegistrationNativePlatformIdentityCtxOutgoingFold.run]
  simp only [StateT.run_get, StateT.run_pure, simulateQ_pure, map_pure,
    RegistrationNativePlatformIdentityCtxOutgoingFold.close, RegistrationNativePlatformIdentityCtxEnvPatch.patch,
    RegistrationWorldAgreementCompiler.join_erase]

/-- Actual owner lookup can be performed in Main before the unchanged optional scalar/start program, including missing handles and every rejected phase. -/
theorem bundle_fold (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (index : Nat) (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (source := source) setup checks representation created
      (RegistrationNativePlatformIdentityBundleRun.bundle setup index writer) =
      (do let owners ← (fun before => pure (before.1.beacons, before) : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform source (RegistrationNativeIdentityFrontend.State source))
          match owners[index]? with
          | none => pure (.ok none)
          | some owner => (RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
              (RegistrationNativePlatformIdentityBundleRun.start setup index owner writer))) := by
  unfold RegistrationNativePlatformIdentityBundleRun.bundle
  rw [RegistrationNativePlatformIdentityCtxOutgoingFold.bind_source setup checks representation created _ _ ?_, get_source]
  · congr 1
    funext owners
    cases owners[index]? with
    | none => exact RegistrationNativePlatformIdentityCtxOutgoingFold.pure_source setup checks representation created _
    | some owner => rfl
  · intro owners
    cases owners[index]? with
    | none => exact pure_work _
    | some owner => exact start setup index owner writer

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleScope

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleScope.next_scope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleScope.next_scope

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleScope.bundled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleScope.bundled

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleScope.start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleScope.start

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleScope.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleScope.bundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleScope.bundled_fold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleScope.bundled_fold

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleScope.get_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleScope.get_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleScope.bundle_fold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleScope.bundle_fold
