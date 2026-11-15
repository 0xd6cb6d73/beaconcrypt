-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBundle
import BeaconcryptCore.Computational.RegistrationNativeMldsaBundleMap

/-! Source-key transport retains the actual stateful Init writer and the shared public platform state. Working owner credentials and the private native state map together; each complete ML signing request translates through the same owned credential. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBundleMap
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaMap (Map owner owners nativeState)
open RegistrationNativeMldsaShared (Local)
open RegistrationNativeMldsaBundleMap (localState)
open RegistrationNativePlatformMldsaProgram (M)
variable {left right : RegistrationNativeMldsa.Source} {n : Nat} {KemSK Platform Value Other Next OtherNext ι : Type} {base : OracleSpec ι}

abbrev Natural (mapping : Map left right) (value : Value → Other)
    (first : StateT (Local n KemSK left) (M left Platform) Value)
    (second : StateT (Local n KemSK right) (M right Platform) Other) : Prop :=
  ∀ before previous, Prod.map (Prod.map value (localState mapping)) id <$>
      RegistrationNativeMldsaSignMap.transform mapping ((first.run before).run previous) =
    (second.run (localState mapping before)).run previous

private theorem pure_natural (mapping : Map left right) (value : Value → Other) (input : Value) :
    Natural (n := n) (KemSK := KemSK) (Platform := Platform) mapping value (pure input) (pure (value input)) := by
  intro before previous
  simp only [StateT.run_pure, RegistrationNativeMldsaSignMap.transform, simulateQ_pure, map_pure]
  rfl

private theorem bind_natural (mapping : Map left right) (value : Value → Other) (nextValue : Next → OtherNext)
    (first : StateT (Local n KemSK left) (M left Platform) Value)
    (second : StateT (Local n KemSK right) (M right Platform) Other)
    (nextFirst : Value → StateT (Local n KemSK left) (M left Platform) Next)
    (nextSecond : Other → StateT (Local n KemSK right) (M right Platform) OtherNext)
    (initial : Natural mapping value first second)
    (continued : ∀ input, Natural mapping nextValue (nextFirst input) (nextSecond (value input))) :
    Natural mapping nextValue (first >>= nextFirst) (second >>= nextSecond) := by
  intro before previous
  simp only [StateT.run_bind, RegistrationNativeMldsaSignMap.transform, simulateQ_bind, map_bind]
  rw [← initial before previous, bind_map_left]
  apply bind_congr
  intro result
  exact continued result.1.1 result.1.2 result.2

private theorem inject_natural (mapping : Map left right) (value : Value → Other)
    (first : StateT (Local n KemSK left) (OracleComp (RegistrationNativeMldsaProgram.Spec left)) Value)
    (second : StateT (Local n KemSK right) (OracleComp (RegistrationNativeMldsaProgram.Spec right)) Other)
    (related : RegistrationNativeMldsaBundleMap.Natural mapping value first second) :
    Natural (Platform := Platform) mapping value
      (RegistrationNativePlatformMldsaProgram.inject first) (RegistrationNativePlatformMldsaProgram.inject second) := by
  intro before previous
  change Prod.map (Prod.map value (localState mapping)) id <$>
    RegistrationNativeMldsaSignMap.transform mapping (do let result ← first.run before; pure (result, previous)) =
      (do let result ← second.run (localState mapping before); pure (result, previous))
  simp only [RegistrationNativeMldsaSignMap.transform, bind_pure_comp, simulateQ_map, Functor.map_map]
  have law := congrArg (fun computation => (fun result => (result, previous)) <$> computation) (related before)
  simpa only [RegistrationNativeMldsaSignMap.transform, Functor.map_map, Prod.map, id_eq] using law

private theorem native_inject {source : RegistrationNativeMldsa.Source}
    (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value) :
    RegistrationNativePlatformMldsaProgram.lift (RegistrationNativePlatformBundleLower.native
      (RegistrationNativePlatformMldsaProgram.coins (Platform := Platform)) setup checks representation created work) =
      RegistrationNativePlatformMldsaProgram.inject (RegistrationNativeMldsaBundle.native setup checks representation created work) := by
  funext before previous
  change RegistrationNativeMldsaProgram.lift
      ((simulateQ RegistrationNativePlatformMldsaProgram.coins
        ((RegistrationNativeMldsaShared.lower setup checks representation created work).run before)).run previous) = _
  rw [RegistrationNativePlatformMldsaProgram.lift_coins]
  change simulateQ RegistrationNativeMldsaProgram.ordinary (do
    let value ← (RegistrationNativeMldsaShared.lower setup checks representation created work).run before
    pure (value, previous)) = (do
      let value ← RegistrationNativeMldsaProgram.lift
        ((RegistrationNativeMldsaShared.lower setup checks representation created work).run before)
      pure (value, previous))
  simp only [simulateQ_bind, simulateQ_pure]
  rfl

private theorem native_natural (mapping : Map left right) (value : Value → Other)
    (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (first : RegistrationNativeBeaconFrontend.M n KemSK left RegistrationServerRoleBackend.State Value)
    (second : RegistrationNativeBeaconFrontend.M n KemSK right RegistrationServerRoleBackend.State Other)
    (related : RegistrationNativeMldsaOrdinaryMap.Natural mapping value first second) :
    Natural (Platform := Platform) mapping value
      (RegistrationNativePlatformMldsaProgram.lift (RegistrationNativePlatformBundleLower.native
        RegistrationNativePlatformMldsaProgram.coins setup checks representation created first))
      (RegistrationNativePlatformMldsaProgram.lift (RegistrationNativePlatformBundleLower.native
        RegistrationNativePlatformMldsaProgram.coins setup checks representation created second)) := by
  rw [native_inject, native_inject]
  exact inject_natural mapping value _ _ (RegistrationNativeMldsaBundleMap.native_natural mapping value
    setup checks representation created first second related)

private theorem outgoing_natural (mapping : Map left right) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (index : Nat)
    (current : RegistrationNativeBeaconFrontend.Owner left) (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    Natural (n := n) (Platform := Platform) mapping id
      (RegistrationNativePlatformMldsaBundle.outgoing setup checks representation created index current query)
      (RegistrationNativePlatformMldsaBundle.outgoing setup checks representation created index (owner mapping current) query) :=
  inject_natural mapping id _ _ (RegistrationNativeMldsaBundleMap.outgoing_natural mapping
    setup checks representation created index current query)

private theorem state_lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (before : S) : (StateT.lift work) before = (fun value => (value, before)) <$> work := bind_pure_comp _ _
private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (state : S) :
    (f <$> work) state = Prod.map f id <$> work state := bind_pure_comp _ _

private theorem state_liftM_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (before : S) : (liftM work : StateT S m X) before = (fun value => (value, before)) <$> work := bind_pure_comp _ _

private theorem encoder_lower {source : RegistrationNativeMldsa.Source} {m : Type → Type} [Monad m] [LawfulMonad m]
    {E : Type} (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (view : registration.InitView) :
    RegistrationNativePlatformBundleLower.lower
      (RegistrationNativePlatformGenericBundle.encoderWith (source := source) (Auxiliary := RegistrationServerRoleBackend.State)
        (RegistrationNativePlatformExperiment.writer (n := n) (KemSK := KemSK) (source := source) writer) view) =
      (StateT.lift (simulateQ writer (AdapterRegistrationWriterRequestExtraction.encodeInit
        (E := E) (m := AdapterRegistrationWriterRequestMonad.Program E)
        (RegistrationNativePlatformWriter.initPacket view)).run) : StateT (Local n KemSK source) m _) := by
  have handler : RegistrationNativePlatformExperiment.writer (n := n) (KemSK := KemSK) (source := source) writer =
      writer.liftTarget (RegistrationNativePlatformExperiment.M n KemSK source m) := by
    funext query
    rfl
  unfold RegistrationNativePlatformBundleLower.lower RegistrationNativePlatformGenericBundle.encoderWith
  rw [handler, simulateQ_liftTarget]
  funext before
  simp only [StateT.run, state_lift_apply, state_map_apply, state_liftM_apply, Functor.map_map, Prod.map, id_eq]

private theorem external_natural (mapping : Map left right) (work : StateT Platform ProbComp Value) :
    Natural (n := n) (KemSK := KemSK) mapping id
      (RegistrationNativePlatformMldsaProgram.lift (StateT.lift work))
      (RegistrationNativePlatformMldsaProgram.lift (StateT.lift work)) := by
  intro before previous
  change Prod.map (Prod.map id (localState mapping)) id <$>
    RegistrationNativeMldsaSignMap.transform mapping (RegistrationNativeMldsaProgram.lift
      (((StateT.lift work : StateT (Local n KemSK left) (StateT Platform ProbComp) Value).run before).run previous)) = _
  rw [RegistrationNativeMldsaSignMap.transform_lift]
  simp only [RegistrationNativePlatformMldsaProgram.lift, RegistrationNativeMldsaProgram.liftState,
    RegistrationNativeMldsaProgram.lift, StateT.run, state_lift_apply, state_map_apply,
    simulateQ_map, Functor.map_map, Prod.map, id_eq]
  rfl

private theorem encoder_natural (mapping : Map left right) {E : Type}
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (view : registration.InitView) :
    Natural (n := n) (KemSK := KemSK) mapping id
      (RegistrationNativePlatformMldsaProgram.lift (RegistrationNativePlatformBundleLower.lower
        (RegistrationNativePlatformGenericBundle.encoderWith (source := left) (Auxiliary := RegistrationServerRoleBackend.State)
          (RegistrationNativePlatformExperiment.writer (n := n) (KemSK := KemSK) (source := left) writer) view)))
      (RegistrationNativePlatformMldsaProgram.lift (RegistrationNativePlatformBundleLower.lower
        (RegistrationNativePlatformGenericBundle.encoderWith (source := right) (Auxiliary := RegistrationServerRoleBackend.State)
          (RegistrationNativePlatformExperiment.writer (n := n) (KemSK := KemSK) (source := right) writer) view))) := by
  rw [encoder_lower, encoder_lower]
  exact external_natural mapping _

private theorem simulate_natural {I : Type} {spec : OracleSpec I} (mapping : Map left right)
    (first : QueryImpl spec (StateT (Local n KemSK left) (M left Platform)))
    (second : QueryImpl spec (StateT (Local n KemSK right) (M right Platform)))
    (queries : ∀ query, Natural mapping id (first query) (second query)) (work : OracleComp spec Value) :
    Natural mapping id (simulateQ first work) (simulateQ second work) := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure, id_eq] using pure_natural mapping id value
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query]
      exact bind_natural mapping id id _ _ _ _ (queries query) ih

private theorem lift_pure {source : RegistrationNativeMldsa.Source} {S : Type} (value : Value) :
    RegistrationNativePlatformMldsaProgram.lift
      (pure value : StateT S (StateT Platform ProbComp) Value) = pure (f := StateT S (M source Platform)) value := by
  funext before previous
  rfl

private theorem lift_bind {source : RegistrationNativeMldsa.Source} {S : Type}
    (work : StateT S (StateT Platform ProbComp) Value) (next : Value → StateT S (StateT Platform ProbComp) Next) :
    RegistrationNativePlatformMldsaProgram.lift (source := source) (work >>= next) =
      (RegistrationNativePlatformMldsaProgram.lift work >>= fun value => RegistrationNativePlatformMldsaProgram.lift (next value)) := by
  funext before previous
  simp only [RegistrationNativePlatformMldsaProgram.lift, RegistrationNativeMldsaProgram.liftState,
    RegistrationNativeMldsaProgram.lift, StateT.run_bind, simulateQ_bind]
  rfl

private theorem lift_simulate {source : RegistrationNativeMldsa.Source} {S I : Type} {spec : OracleSpec I}
    (handler : QueryImpl spec (StateT S (StateT Platform ProbComp))) (work : OracleComp spec Value) :
    RegistrationNativePlatformMldsaProgram.lift (source := source) (simulateQ handler work) =
      simulateQ (fun query => RegistrationNativePlatformMldsaProgram.lift (handler query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, lift_pure]
  | query_bind query next ih => simp only [simulateQ_bind, simulateQ_spec_query, lift_bind, ih]

private theorem external_simulate {source : RegistrationNativeMldsa.Source} {S I : Type} {spec : OracleSpec I}
    (handler : QueryImpl spec (StateT Platform ProbComp)) (work : OracleComp spec Value) :
    RegistrationNativePlatformMldsaProgram.lift
      (StateT.lift (simulateQ handler work) : StateT S (StateT Platform ProbComp) Value) =
      simulateQ (fun query => RegistrationNativePlatformMldsaProgram.lift (source := source) (StateT.lift (handler query))) work := by
  have stateLift : (StateT.lift (simulateQ handler work) : StateT S (StateT Platform ProbComp) Value) =
      simulateQ (fun query => StateT.lift (handler query)) work := by
    change liftM (simulateQ handler work) = simulateQ (handler.liftTarget (StateT S (StateT Platform ProbComp))) work
    exact (simulateQ_liftTarget handler work).symm
  rw [stateLift, lift_simulate]

private def combined {source : RegistrationNativeMldsa.Source} {E : Type}
    (crypto : QueryImpl RegistrationBeaconInitExecutor.Spec (StateT (Local n KemSK source) (M source Platform)))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    QueryImpl (RegistrationNativePlatformWriter.Spec E) (StateT (Local n KemSK source) (M source Platform))
  | .inl query => crypto query
  | .inr query => RegistrationNativePlatformMldsaProgram.lift (StateT.lift (writer query))

/-- The actual source publication is exactly the shared free crypto/writer program, with both state layers retained. -/
theorem begin_source {source : RegistrationNativeMldsa.Source} {E : Type}
    (crypto : QueryImpl RegistrationBeaconInitExecutor.Spec (StateT (Local n KemSK source) (M source Platform)))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) :
    simulateQ (combined crypto writer) (RegistrationNativePlatformWriter.begin E control inputs coins pin) =
      RegistrationNativePlatformBeaconPublication.begin crypto
        (fun view => RegistrationNativePlatformMldsaProgram.lift (RegistrationNativePlatformBundleLower.lower
          (RegistrationNativePlatformGenericBundle.encoderWith (source := source) (Auxiliary := RegistrationServerRoleBackend.State)
            (RegistrationNativePlatformExperiment.writer (n := n) (KemSK := KemSK) (source := source) writer) view)))
        control inputs coins pin := by
  rw [RegistrationNativePlatformWriter.begin_interpret]
  simp only [combined]
  congr 1
  funext view
  rw [encoder_lower, external_simulate]

private theorem begin_natural (mapping : Map left right) {E : Type}
    (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (index : Nat)
    (current : RegistrationNativeBeaconFrontend.Owner left)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) :
    Natural mapping id
      (RegistrationNativePlatformBeaconPublication.begin
        (RegistrationNativePlatformMldsaBundle.outgoing setup checks representation created index current)
        (fun view => RegistrationNativePlatformMldsaProgram.lift (RegistrationNativePlatformBundleLower.lower
          (RegistrationNativePlatformGenericBundle.encoderWith (source := left) (Auxiliary := RegistrationServerRoleBackend.State)
            (RegistrationNativePlatformExperiment.writer (n := n) (KemSK := KemSK) (source := left) writer) view)))
        control inputs coins pin)
      (RegistrationNativePlatformBeaconPublication.begin
        (RegistrationNativePlatformMldsaBundle.outgoing setup checks representation created index (owner mapping current))
        (fun view => RegistrationNativePlatformMldsaProgram.lift (RegistrationNativePlatformBundleLower.lower
          (RegistrationNativePlatformGenericBundle.encoderWith (source := right) (Auxiliary := RegistrationServerRoleBackend.State)
            (RegistrationNativePlatformExperiment.writer (n := n) (KemSK := KemSK) (source := right) writer) view)))
        control inputs coins pin) := by
  rw [← begin_source, ← begin_source]
  apply simulate_natural
  intro query
  cases query with
  | inl query => exact outgoing_natural mapping setup checks representation created index current query
  | inr query => exact external_natural mapping (writer query)

private noncomputable def tail {source : RegistrationNativeMldsa.Source} (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (index : Nat)
    (current : RegistrationNativeBeaconFrontend.Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (published : RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))) :
    StateT (Local n KemSK source) (M source Platform) (RustM (Option (alloc.vec.Vec U8))) :=
  match published with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err _) => pure (.ok none)
  | .ok (.Ok finished) => do
      RegistrationNativePlatformMldsaProgram.lift (RegistrationNativePlatformBundleLower.native
        RegistrationNativePlatformMldsaProgram.coins setup checks representation created
        (RegistrationNativeBeaconFrontend.updatePhase index (.initSent finished.pending oneTime)))
      let _ ← RegistrationNativePlatformMldsaProgram.lift (RegistrationNativePlatformBundleLower.native
        RegistrationNativePlatformMldsaProgram.coins setup checks representation created
        (RegistrationNativeBeaconFrontend.effect (.inr (.advanceOwner current.worldOwner .initSent))))
      pure (.ok (some finished.encoded))

private theorem tail_natural (mapping : Map left right) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (index : Nat)
    (current : RegistrationNativeBeaconFrontend.Owner left) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (published : RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))) :
    Natural (n := n) (Platform := Platform) mapping id
      (tail setup checks representation created index current oneTime published)
      (tail setup checks representation created index (owner mapping current) oneTime published) := by
  cases published with
  | fail error | div => exact pure_natural mapping id _
  | ok answer => cases answer with
    | Err prior => exact pure_natural mapping id _
    | Ok finished =>
        apply bind_natural mapping id id _ _ _ _ (native_natural mapping id setup checks representation created _ _
          (RegistrationNativeMldsaOrdinaryMap.phase_natural mapping index (.initSent finished.pending oneTime)))
        intro _changed
        apply bind_natural mapping id id _ _ _ _ (native_natural mapping id setup checks representation created _ _
          (RegistrationNativeMldsaOrdinaryMap.effect_natural mapping _))
        intro _advanced
        exact pure_natural mapping id _

private theorem published_natural (mapping : Map left right) {E : Type}
    (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (index : Nat)
    (current : RegistrationNativeBeaconFrontend.Owner left) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    Natural (n := n) mapping id
      (do
        let published ← RegistrationNativePlatformBeaconPublication.begin
          (RegistrationNativePlatformMldsaBundle.outgoing setup checks representation created index current)
          (fun view => RegistrationNativePlatformMldsaProgram.lift (RegistrationNativePlatformBundleLower.lower
            (RegistrationNativePlatformGenericBundle.encoderWith (source := left) (Auxiliary := RegistrationServerRoleBackend.State)
              (RegistrationNativePlatformExperiment.writer (n := n) (KemSK := KemSK) (source := left) writer) view)))
          ⟨current.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup current)
          ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ current.pin
        tail setup checks representation created index current oneTime published)
      (do
        let published ← RegistrationNativePlatformBeaconPublication.begin
          (RegistrationNativePlatformMldsaBundle.outgoing setup checks representation created index (owner mapping current))
          (fun view => RegistrationNativePlatformMldsaProgram.lift (RegistrationNativePlatformBundleLower.lower
            (RegistrationNativePlatformGenericBundle.encoderWith (source := right) (Auxiliary := RegistrationServerRoleBackend.State)
              (RegistrationNativePlatformExperiment.writer (n := n) (KemSK := KemSK) (source := right) writer) view)))
          ⟨(owner mapping current).pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup (owner mapping current))
          ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ (owner mapping current).pin
        tail setup checks representation created index (owner mapping current) oneTime published) := by
  apply bind_natural mapping id id _ _ _ _ (begin_natural mapping setup checks representation created index current writer _ _ _ _)
  intro published
  exact tail_natural mapping setup checks representation created index current oneTime published

/-- The actual effectful Init bundle preserves its complete public owner data under the Server ML representation map and retains all allocator state. -/
theorem bundle_natural (mapping : Map left right) {E : Type}
    (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) (index : Nat) :
    Natural (n := n) mapping id
      (RegistrationNativePlatformMldsaBundle.bundle (source := left) setup checks representation created
        (RegistrationNativePlatformGenericBundle.encoderWith (source := left) (Auxiliary := RegistrationServerRoleBackend.State)
          (RegistrationNativePlatformExperiment.writer (n := n) (KemSK := KemSK) (source := left) writer)) index)
      (RegistrationNativePlatformMldsaBundle.bundle (source := right) setup checks representation created
        (RegistrationNativePlatformGenericBundle.encoderWith (source := right) (Auxiliary := RegistrationServerRoleBackend.State)
          (RegistrationNativePlatformExperiment.writer (n := n) (KemSK := KemSK) (source := right) writer)) index) := by
  unfold RegistrationNativePlatformMldsaBundle.bundle
  apply bind_natural mapping (owners mapping) id _ _ _ _ (native_natural mapping (owners mapping) setup checks representation created _ _
    (RegistrationNativeMldsaOrdinaryMap.get_natural mapping))
  intro before
  simp only [RegistrationNativeMldsaMap.owners_lookup]
  cases before[index]? with
  | none => exact pure_natural mapping id _
  | some current =>
      simp only [Option.map_some]
      dsimp only [owner]
      cases phase : current.phase with
      | initSent pending oneTime | established completed | aborted previous => exact pure_natural mapping id _
      | fresh =>
          apply bind_natural mapping id id _ _ _ _ (native_natural mapping id setup checks representation created _ _
            (RegistrationNativeMldsaOrdinaryMap.sample_natural mapping PqxdhJointGapDh.sampleScalar))
          intro oneTime
          convert published_natural (n := n) (Platform := Platform) mapping setup checks representation created index current oneTime writer using 1 <;>
            (simp only [tail, owner, id_eq, phase]
             congr 1
             funext published
             cases published with
             | fail error => rfl
             | div => rfl
             | ok answer => cases answer <;> rfl)
      | freshWithCoins oneTime =>
          apply bind_natural mapping id id _ _ _ _ (pure_natural mapping id oneTime)
          intro actual
          convert published_natural (n := n) (Platform := Platform) mapping setup checks representation created index current actual writer using 1 <;>
            (simp only [tail, owner, id_eq, phase]
             congr 1
             funext published
             cases published with
             | fail error => rfl
             | div => rfl
             | ok answer => cases answer <;> rfl)

/-- The complete global source bundle preserves credential translation, full native state and external poststate. -/
theorem sourceBundle_natural (mapping : Map left right) {E : Type}
    (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) (index : Nat)
    (before : RegistrationNativeExperiment.State n KemSK left) (previous : Platform) :
    Prod.map (Prod.map id (nativeState mapping)) id <$>
      RegistrationNativeMldsaSignMap.transform mapping
        (((RegistrationNativePlatformMldsaBundle.sourceBundle setup checks representation created writer index).run before).run previous) =
      (((RegistrationNativePlatformMldsaBundle.sourceBundle setup checks representation created writer index).run
        (nativeState mapping before)).run previous) := by
  have localLaw := bundle_natural mapping setup checks representation created writer index
    (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before)) previous
  let closeResult := fun result : RustM (Option (alloc.vec.Vec U8)) × Local n KemSK right =>
    ((do let optional ← result.1; .ok (optional.map TranscriptAuthParts.absSlice)), RegistrationNativeMldsaShared.close result.2)
  have closed := congrArg (fun work => Prod.map closeResult id <$> work) localLaw
  simp only [RegistrationNativePlatformMldsaBundle.sourceBundle, StateT.run,
    RegistrationNativeMldsaSignMap.transform, state_map_apply, simulateQ_map, Functor.map_map,
    Prod.map, id_eq] at closed ⊢
  exact closed

end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBundleMap

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBundleMap.bundle_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBundleMap.bundle_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBundleMap.sourceBundle_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBundleMap.sourceBundle_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBundleMap.begin_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBundleMap.begin_source
