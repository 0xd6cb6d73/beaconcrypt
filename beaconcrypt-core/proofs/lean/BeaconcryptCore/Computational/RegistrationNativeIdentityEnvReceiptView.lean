-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryView
import BeaconcryptCore.Computational.RegistrationNativePlatformViewStable
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityHistoryView

/-! The free Beacon frontend stores ML receipt payloads in compact EnvState before joining Local.world.2. This analysis view clears precisely that log. The actual source outgoing dictionary never reads its previous payloads, and the complete original request tree therefore has an exact projected execution. Owner state, signed-message order, auxiliary values and request/record journals remain literal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityEnvReceiptView
open RegistrationNativeIdentityFrontend (M Owner)
open RegistrationNativeIdentityHistoryView (Packed pack)
variable {n : Nat} {I KemSK Auxiliary Platform Value Next : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}

def view (before : Packed (source := source) (Auxiliary := Auxiliary)) :=
  (before.1, {before.2 with receipts := []})

def Stable (work : M n KemSK Auxiliary source Value) : Prop := RegistrationNativePlatformViewStable.Stable view (pack work)

private theorem idempotent (before : Packed (source := source) (Auxiliary := Auxiliary)) : view (view before) = view before := rfl
private theorem bind_apply {S A B : Type} {m : Type → Type} [Monad m]
    (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl
private theorem pure_apply {S A : Type} {m : Type → Type} [Monad m] (value : A) (before : S) :
    (pure value : StateT S m A) before = pure (value, before) := rfl
private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before
private theorem lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) :
    (StateT.lift work : StateT S m A) before = (fun value => (value, before)) <$> work := by
  change (do let value ← work; pure (value, before)) = _
  rw [bind_pure_comp]
private theorem modify_apply {S : Type} {m : Type → Type} [Monad m] (change : S → S) (before : S) :
    (modify change : StateT S m Unit) before = pure ((), change before) := rfl

private theorem pack_pure (value : Value) : pack (pure value : M n KemSK Auxiliary source Value) = pure value := by
  funext before
  simp only [pack, StateT.run, pure_apply, map_pure]
private theorem pack_bind (work : M n KemSK Auxiliary source Value)
    (next : Value → M n KemSK Auxiliary source Next) :
    pack (work >>= next) = (pack work >>= fun value => pack (next value)) := by
  funext before
  simp only [pack, StateT.run, bind_apply, map_bind, bind_map_left]
private theorem pure_stable (value : Value) : Stable (pure value : M n KemSK Auxiliary source Value) := by
  change RegistrationNativePlatformViewStable.Stable view _
  rw [pack_pure]
  exact RegistrationNativePlatformViewStable.pure_stable view idempotent value
private theorem bind_stable (work : M n KemSK Auxiliary source Value)
    (next : Value → M n KemSK Auxiliary source Next) (first : Stable work) (later : ∀ value, Stable (next value)) :
    Stable (work >>= next) := by
  change RegistrationNativePlatformViewStable.Stable view _
  rw [pack_bind]
  exact RegistrationNativePlatformViewStable.bind_stable view _ _ first later

/-- Trusted source calls retain the complete compact environment without inspecting previous ML receipt payloads. -/
theorem trusted (work : OracleComp (RegistrationNativeIdentityFrontend.Trusted n KemSK) Value) :
    Stable (StateT.lift (StateT.lift work) : M n KemSK Auxiliary source Value) := by
  rintro ⟨owners, env⟩
  simp only [pack, StateT.run,
    lift_apply, map_apply, Functor.map_map, Prod.map_def, id_eq, view]

private theorem effect (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    Stable (RegistrationNativeIdentityFrontend.effect (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) query) :=
  trusted _
private theorem program_stable {K : Type} {queries : OracleSpec K}
    (handler : QueryImpl queries (M n KemSK Auxiliary source)) (law : ∀ query, Stable (handler query))
    (work : OracleComp queries Value) : Stable (simulateQ handler work) := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure]; exact pure_stable value
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    exact bind_stable _ _ (law query) ih
private theorem sample (work : ProbComp Value) :
    Stable (RegistrationNativeIdentityFrontend.sample (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) work) :=
  program_stable _ (fun query => effect (.inl query)) work
private theorem log (index : Nat) (message : Pqxdh.Bytes) (signature : PqxdhEd25519EufCma.Ed25519Signature) :
    Stable (RegistrationNativeIdentityFrontend.logEd (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) index message signature) := by
  rintro ⟨owners, env⟩
  simp only [pack, RegistrationNativeIdentityFrontend.logEd,
    StateT.run, modify_apply, pure_apply, map_pure, view, Prod.map_def, id_eq]
private theorem receipt (receipt : RegistrationSigningShared.Receipt) :
    Stable (RegistrationNativeIdentityFrontend.updateEnv (n := n) (KemSK := KemSK) (source := source)
      (fun env : RegistrationWorldAgreementCompiler.EnvState Auxiliary => {env with receipts := env.receipts ++ [receipt]})) := by
  rintro ⟨owners, env⟩
  simp only [pack, RegistrationNativeIdentityFrontend.updateEnv,
    StateT.run, lift_apply, map_apply, modify_apply, map_pure, view, Prod.map_def, id_eq]

/-- Actual hash, optional signing, history append and raw receipt append all preserve this input-independent compact Env view. -/
theorem outgoing (setup : PqxdhServerAuthExperiment.Setup base KemSK) (index : Nat) (owner : Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    Stable (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := Auxiliary) setup source index owner query) := by
  classical
  cases query with
  | inl query => cases query with
    | hash request => exact effect (.inr (.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request)))
    | sign request payload digest =>
      exact bind_stable _ _ (sample _) fun reply => bind_stable _ _ (receipt _) fun _ => pure_stable reply
  | inr request =>
    simp only [RegistrationNativeIdentityFrontend.outgoing]
    split
    · apply bind_stable _ _ (trusted _)
      intro signature
      cases signature with
      | none => exact pure_stable _
      | some signature => exact bind_stable _ _ (log index _ signature) fun _ => pure_stable _
    · exact pure_stable _

/-- Every adaptive actual Init controller has the same compact projected output; no full raw-log equality is asserted. -/
theorem program (setup : PqxdhServerAuthExperiment.Setup base KemSK) (index : Nat) (owner : Owner source)
    (work : OracleComp RegistrationBeaconInitExecutor.Spec Value) :
    Stable (simulateQ (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := Auxiliary) setup source index owner) work) :=
  program_stable _ (outgoing setup index owner) work

/-- The actual compact receipt view joins to precisely the full Local receipt view used by nonBeacon source controllers. -/
theorem join (before : Packed (source := source) (Auxiliary := Auxiliary)) (world : PqxdhRecordLiftWorld.State n) :
    RegistrationWorldAgreementCompiler.join (view before).2 world =
      RegistrationNativePlatformIdentityReceiptView.view (RegistrationWorldAgreementCompiler.join before.2 world) := rfl


abbrev PlatformM := RegistrationNativePlatformIdentityProgram.M n KemSK Auxiliary Platform source
abbrev PlatformPacked := RegistrationNativePlatformIdentityHistoryView.Packed (source := source) (Auxiliary := Auxiliary) (Platform := Platform)
def platformView (before : PlatformPacked (source := source) (Auxiliary := Auxiliary) (Platform := Platform)) :=
  (view before.1, before.2)
def PlatformStable (work : PlatformM (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (Platform := Platform) (source := source) Value) : Prop :=
  RegistrationNativePlatformViewStable.Stable platformView (RegistrationNativePlatformIdentityHistoryView.pack work)

/-- The actual external-state lift retains the compact receipt-view law and all original native requests. -/
theorem platform_native (work : M n KemSK Auxiliary source Value) (law : Stable work) :
    PlatformStable (RegistrationNativePlatformIdentityProgram.native work :
      RegistrationNativePlatformIdentityProgram.M n KemSK Auxiliary Platform source Value) := by
  rintro ⟨⟨owners, env⟩, platform⟩
  have same := congrArg (fun action => (fun result => (result.1, (result.2, platform))) <$>
    simulateQ (RegistrationNativePlatformIdentityProgram.nativeLift (n := n) (KemSK := KemSK)) action) (law (owners, env))
  simpa only [RegistrationNativePlatformIdentityHistoryView.pack, RegistrationNativePlatformIdentityProgram.native,
    pack, StateT.run, view, platformView, simulateQ_map, Functor.map_map, Prod.map_def, id_eq] using same

/-- The literal stateful source writer is independent of compact receipt bytes, retaining every P mutation. -/
theorem platform_external (work : StateT Platform ProbComp Value) :
    PlatformStable (RegistrationNativePlatformIdentityProgram.external work :
      RegistrationNativePlatformIdentityProgram.M n KemSK Auxiliary Platform source Value) := by
  rintro ⟨⟨owners, env⟩, platform⟩
  simp only [RegistrationNativePlatformIdentityHistoryView.pack, RegistrationNativePlatformIdentityProgram.external,
    StateT.run, view, platformView, Functor.map_map, Prod.map_def, id_eq]

private theorem platform_pack_pure (value : Value) :
    RegistrationNativePlatformIdentityHistoryView.pack
      (pure value : RegistrationNativePlatformIdentityProgram.M n KemSK Auxiliary Platform source Value) = pure value := by
  funext before
  simp only [RegistrationNativePlatformIdentityHistoryView.pack, StateT.run, pure_apply, map_pure]
private theorem platform_pack_bind (work : RegistrationNativePlatformIdentityProgram.M n KemSK Auxiliary Platform source Value)
    (next : Value → RegistrationNativePlatformIdentityProgram.M n KemSK Auxiliary Platform source Next) :
    RegistrationNativePlatformIdentityHistoryView.pack (work >>= next) =
      (RegistrationNativePlatformIdentityHistoryView.pack work >>= fun value => RegistrationNativePlatformIdentityHistoryView.pack (next value)) := by
  funext before
  simp only [RegistrationNativePlatformIdentityHistoryView.pack, StateT.run, bind_apply, map_bind, bind_map_left]
private theorem platform_pack_program {K : Type} {queries : OracleSpec K}
    (handler : QueryImpl queries (RegistrationNativePlatformIdentityProgram.M n KemSK Auxiliary Platform source))
    (work : OracleComp queries Value) :
    RegistrationNativePlatformIdentityHistoryView.pack (simulateQ handler work) =
      simulateQ (fun query => RegistrationNativePlatformIdentityHistoryView.pack (handler query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, platform_pack_pure]
  | query_bind query next ih => simp only [simulateQ_bind, simulateQ_spec_query, platform_pack_bind, ih]

/-- The entire actual dynamic-writer Init source program can clear prior raw ML receipt payloads without changing any remaining compact state or public result. -/
theorem platform_program {E : Type} (setup : PqxdhServerAuthExperiment.Setup base KemSK) (index : Nat) (owner : Owner source)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (work : OracleComp (RegistrationNativePlatformWriter.Spec E) Value) :
    PlatformStable (simulateQ (RegistrationNativePlatformIdentityPublication.callback (n := n) (Auxiliary := Auxiliary) setup index owner writer) work) := by
  change RegistrationNativePlatformViewStable.Stable platformView _
  rw [platform_pack_program]
  apply RegistrationNativePlatformViewStable.program_stable platformView (fun _ => rfl)
  intro query
  cases query with
  | inl query => exact platform_native _ (outgoing setup index owner query)
  | inr query => exact platform_external (writer query)

end BeaconcryptCore.Computational.RegistrationNativeIdentityEnvReceiptView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityEnvReceiptView.trusted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityEnvReceiptView.trusted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityEnvReceiptView.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityEnvReceiptView.outgoing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityEnvReceiptView.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityEnvReceiptView.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityEnvReceiptView.join' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityEnvReceiptView.join

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityEnvReceiptView.platform_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityEnvReceiptView.platform_native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityEnvReceiptView.platform_external' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityEnvReceiptView.platform_external

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityEnvReceiptView.platform_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityEnvReceiptView.platform_program
