-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationBackend
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishAllocationCaps
import BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationBundleCaps
import BeaconcryptCore.Computational.RegistrationNativeHiddenServerAllocationCaps
import BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxBounds
/-! The actual local dictionaries preserve the literal non-append predicate through common platform state. Corrected OPEN acceptance uses its derived zero-administrative source bill, while effectful bundle publication uses its complete source syntax. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationLocal
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicFrontend
open RegistrationNativeHiddenAllocationCore (mapped simulation)
open RegistrationNativeHiddenServerAllocationCaps (LocalAllowed)
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I}

def Allowed : (LocalSpec n KemSK).Domain → Prop
  | .inl query => RegistrationNativeHiddenAllocationCore.Allowed (.inl query)
  | .inr _ => True
private theorem every {J V : Type} {spec : OracleSpec J} (work : OracleComp spec V) :
    AllQueriesSatisfy work (fun _ => True) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih => exact ⟨trivial, ih⟩

/-- Native local routing changes no physical allocation request. -/
theorem native_query (selected : Bool) (query : (RegistrationBeaconReferenceCompiler.Spec n KemSK).Domain)
    (safe : LocalAllowed query) : (localQuery selected query).AllQueriesSatisfy (Allowed (KemSK := KemSK)) := by
  rcases query with message | (message | common) | kem
  · exact (allQueriesSatisfy_query_iff _ _).mpr trivial
  · exact (allQueriesSatisfy_query_iff _ _).mpr trivial
  · cases common <;> exact (allQueriesSatisfy_query_iff _ _).mpr safe
  · unfold localQuery
    apply simulation _ (fun _ => True) (Allowed (KemSK := KemSK)) _ _ (every _)
    intro request _
    exact (allQueriesSatisfy_query_iff _ _).mpr trivial

/-- Closing actual local callbacks preserves every platform result and the source allocation footprint. -/
theorem native_program (selected : Bool) (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) A)
    (safe : work.AllQueriesSatisfy (LocalAllowed (KemSK := KemSK))) (before : Platform) :
    ((simulateQ (localHandler selected) work).run before).AllQueriesSatisfy (Allowed (KemSK := KemSK)) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => trivial
  | query_bind query next ih =>
    obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp safe
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, localHandler, StateT.run_lift, bind_pure_comp]
    apply allQueriesSatisfy_bind (mapped _ _ _ (native_query selected query first))
    intro result
    exact ih result.1 (later result.1) result.2

/-- External platform samplers cannot append a physical owner. -/
theorem platform_free (work : StateT Platform ProbComp A) (before : Platform) :
    ((platform (n := n) (KemSK := KemSK) work).run before).AllQueriesSatisfy (Allowed (KemSK := KemSK)) := by
  apply simulation _ (fun _ => True) (Allowed (KemSK := KemSK)) _ _ (every _)
  intro query _
  exact (allQueriesSatisfy_query_iff _ _).mpr trivial

private theorem trusted_free (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain)
    (safe : RegistrationNativeHiddenBeaconAllocationCaps.Allowed query) (before : Platform) :
    ((trusted query).run before).AllQueriesSatisfy (Allowed (KemSK := KemSK)) := by
  simp only [trusted, StateT.run_lift, bind_pure_comp]
  apply mapped
  apply simulation _ (LocalAllowed (KemSK := KemSK)) (Allowed (KemSK := KemSK)) (native_query false) _
  rcases query with effect | other | pool | key
  · exact (allQueriesSatisfy_query_iff _ _).mpr safe
  · simp [RegistrationBeaconReferenceCompiler.trustedLift, RegistrationBeaconReferenceCompiler.indexed,
      LocalAllowed, allQueriesSatisfy_query_iff]
  · cases pool <;> simp [RegistrationBeaconReferenceCompiler.trustedLift, RegistrationBeaconReferenceCompiler.indexed,
      LocalAllowed, allQueriesSatisfy_query_iff]
  · simp [RegistrationBeaconReferenceCompiler.trustedLift, RegistrationBeaconReferenceCompiler.indexed,
      LocalAllowed, allQueriesSatisfy_query_iff]

private theorem owner_program
    (implementation : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (work : OracleComp (RegistrationNativePlatformGenericBundle.Spec E n KemSK) A)
    (safe : work.AllQueriesSatisfy (RegistrationNativePlatformHiddenAllocationBundleCaps.Allowed (E := E) (KemSK := KemSK)))
    (before : Platform) :
    ((simulateQ (fun (query : (RegistrationNativePlatformGenericBundle.Spec E n KemSK).Domain) => match query with | .inl query => trusted query | .inr query => writer implementation query) work).run before).AllQueriesSatisfy
      (Allowed (KemSK := KemSK)) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => trivial
  | query_bind query next ih =>
    obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp safe
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    apply allQueriesSatisfy_bind
    · cases query with
      | inl query =>
        apply trusted_free query _ before
        cases query with
        | inl effect => exact first
        | inr query => trivial
      | inr query => exact platform_free (implementation query) before
    · intro result
      exact ih result.1 (later result.1) result.2

private theorem map_apply {S V W : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : V → W) (work : StateT S m V) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- The complete actual shared-writer public bundle has no physical append request on any path. -/
theorem bundle {source : RegistrationNativeMldsa.Source} (setup : Setup base KemSK)
    (implementation : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (index : Nat)
    (owners : RegistrationNativePublicOwners.State source) (env : RegistrationServerReferenceCompiler.Environment) (before : Platform) :
    ((((RegistrationNativePlatformPublicOwners.bundle (trusted (n := n) (KemSK := KemSK)) (writer implementation) setup source selected publicPrekey index).run owners).run env).run before).AllQueriesSatisfy
      (Allowed (KemSK := KemSK)) := by
  let joint : QueryImpl (RegistrationNativePlatformGenericBundle.Spec E n KemSK) (Base n KemSK Platform)
    | .inl query => trusted query
    | .inr query => writer implementation query
  have actual := RegistrationNativePlatformGenericBundle.program_evaluate (Auxiliary := RegistrationServerRoleBackend.State) joint setup source index
  change RegistrationNativePlatformGenericBundle.evaluate joint _ = RegistrationNativePlatformGenericBundle.bundle trusted setup source
    (RegistrationNativePlatformGenericBundle.encoderWith (writer implementation)) index at actual
  simp only [RegistrationNativePlatformPublicOwners.bundle, RegistrationNativePlatformPublicOwners.executeLocal, StateT.run, map_apply]
  rw [← actual]
  unfold RegistrationNativePlatformGenericBundle.evaluate
  simp only [StateT.run]
  exact mapped _ _ _ (owner_program implementation _ (RegistrationNativePlatformHiddenAllocationBundleCaps.program_free setup index _ _) before)

private def acceptHandler (selected : Bool) (reserve : StateT Platform ProbComp Bool) :
    QueryImpl (RegistrationNativePlatformServerOpenSyntax.Spec n KemSK) (Base n KemSK Platform)
  | .inl query => localHandler selected query
  | .inr _ => platform reserve
private def SyntaxAllowed : (RegistrationNativePlatformServerOpenSyntax.Spec n KemSK).Domain → Prop
  | .inl query => LocalAllowed (KemSK := KemSK) query
  | .inr _ => True

private theorem syntax_admin (query : (RegistrationNativePlatformServerOpenSyntax.Spec n KemSK).Domain)
    (excluded : ¬ SyntaxAllowed (KemSK := KemSK) query) :
    RegistrationNativePlatformServerOpenSyntaxBounds.queryKind query = .admin := by
  rcases query with (message | (message | (publication | environment)) | kem) | reserve
  · exact (excluded trivial).elim
  · exact (excluded trivial).elim
  · exact (excluded trivial).elim
  · rcases environment with coin | capability
    · exact (excluded rfl).elim
    · cases capability <;> simp_all [SyntaxAllowed, LocalAllowed, RegistrationNativeHiddenServerAllocationCaps.EffectAllowed,
        RegistrationNativeHiddenAllocationProtocol.effectDelta, RegistrationNativeHiddenAllocationProtocol.capabilityDelta,
        RegistrationNativePlatformServerOpenSyntaxBounds.queryKind,
        RegistrationNativePlatformServerOpenSyntaxBounds.protocolKind, PqxdhRecordLiftInterface.effectKind]
  · exact (excluded trivial).elim
  · exact (excluded trivial).elim

private theorem syntax_program (selected : Bool) (reserve : StateT Platform ProbComp Bool)
    (work : OracleComp (RegistrationNativePlatformServerOpenSyntax.Spec n KemSK) A)
    (safe : work.AllQueriesSatisfy (SyntaxAllowed (KemSK := KemSK))) (before : Platform) :
    ((simulateQ (acceptHandler selected reserve) work).run before).AllQueriesSatisfy (Allowed (KemSK := KemSK)) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => trivial
  | query_bind query next ih =>
    obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp safe
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    apply allQueriesSatisfy_bind
    · cases query with
      | inl query =>
        simp only [acceptHandler, localHandler, StateT.run_lift, bind_pure_comp]
        exact mapped _ _ _ (native_query selected query first)
      | inr query => exact platform_free reserve before
    · intro result
      exact ih result.1 (later result.1) result.2

/-- Literal corrected OPEN acceptance performs no physical append, including its actual stateful reservation and every failed prefix. -/
theorem accept (selected : Bool) (reserve : StateT Platform ProbComp Bool)
    (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket)
    (front : RegistrationServerMaterialFrontend.State) (env : RegistrationServerReferenceCompiler.Environment) (before : Platform) :
    ((((RegistrationNativePlatformServerOpenControl.accept (localHandler (n := n) selected) (platform reserve) setup checks verify packet).run front).run env).run before).AllQueriesSatisfy
      (Allowed (KemSK := KemSK)) := by
  classical
  have source := congrArg (fun work => ((work.run front).run env).run before)
    (RegistrationNativePlatformServerOpenSyntax.accept_source (acceptHandler (n := n) (KemSK := KemSK) selected reserve) setup checks verify packet)
  have implementation_eq : RegistrationNativePlatformServerOpenSyntax.implementation (acceptHandler (n := n) (KemSK := KemSK) selected reserve) = localHandler (n := n) (KemSK := KemSK) selected := by
    funext query
    rfl
  rw [implementation_eq] at source
  simp only [acceptHandler] at source
  rw [← source]
  have bounded := (RegistrationNativePlatformServerOpenSyntaxBounds.accept_bound (n := n) (KemSK := KemSK) setup checks verify .admin packet front env).of_imp
    (syntax_admin (n := n) (KemSK := KemSK))
  have safe := (isQueryBoundP_zero_iff _ (SyntaxAllowed (n := n) (KemSK := KemSK))).mp bounded
  exact syntax_program selected reserve _ safe before

/-- Embedding the actual local dictionary retains its exact physical-allocation predicate. -/
theorem embedding (work : OracleComp (LocalSpec n KemSK) A)
    (safe : work.AllQueriesSatisfy (Allowed (KemSK := KemSK))) :
    (simulateQ embedLocal work).AllQueriesSatisfy (RegistrationNativePlatformHiddenAllocationBackend.Allowed (KemSK := KemSK)) := by
  apply simulation _ (Allowed (KemSK := KemSK)) _ _ _ safe
  intro query allowed
  cases query <;> exact (allQueriesSatisfy_query_iff _ _).mpr allowed

private theorem ordinary (setup : Setup base KemSK) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) A)
    (safe : work.AllQueriesSatisfy (LocalAllowed (KemSK := KemSK))) :
    (simulateQ (RegistrationNativePublicOwners.ordinary setup scalar) work).AllQueriesSatisfy (LocalAllowed (KemSK := KemSK)) := by
  apply simulation _ (LocalAllowed (KemSK := KemSK)) (LocalAllowed (KemSK := KemSK)) _ _ safe
  intro query permitted
  cases query with
  | inl message =>
    simp only [RegistrationNativePublicOwners.ordinary]
    cases RegistrationNativeLocalMessage.materialize setup.joint setup.dh scalar message <;>
      simp [LocalAllowed, allQueriesSatisfy_query_iff, allQueriesSatisfy_pure]
  | inr query => exact (allQueriesSatisfy_query_iff _ _).mpr permitted

/-- Corrected selected or ordinary finish preserves the native no-append syntax through its actual common platform lift. -/
theorem finish (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) {source : RegistrationNativeMldsa.Source}
    (index : Nat) (packet : Option registration.ResponsePacket)
    (owners : RegistrationNativePublicOwners.State source) (env : RegistrationServerReferenceCompiler.Environment) (before : Platform) :
    ((((RegistrationNativePlatformPublicFrontend.finish (n := n) (KemSK := KemSK) setup wire source index packet).run owners).run env).run before).AllQueriesSatisfy
      (Allowed (KemSK := KemSK)) := by
  simp only [RegistrationNativePlatformPublicFrontend.finish, StateT.run]
  cases found : owners[index]? with
  | none => trivial
  | some owner =>
    simp only [map_apply]
    apply mapped
    apply native_program
    cases own : owner.scalar with
    | none => exact RegistrationNativePlatformPublicFinishAllocationCaps.finish_safe setup wire packet owner.view env
    | some scalar => exact ordinary setup scalar _ (RegistrationNativePlatformPublicFinishAllocationCaps.finish_safe setup wire packet owner.view env)

end BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationLocal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationLocal.native_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationLocal.native_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationLocal.native_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationLocal.native_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationLocal.platform_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationLocal.platform_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationLocal.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationLocal.bundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationLocal.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationLocal.accept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationLocal.embedding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationLocal.embedding

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationLocal.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationLocal.finish
