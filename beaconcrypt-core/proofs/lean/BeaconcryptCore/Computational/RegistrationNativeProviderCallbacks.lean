-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeProviderLocal
import BeaconcryptCore.Computational.RegistrationNativeProviderBuildFrame

/-! The provider source has an exact native private layout. Outside KEM callbacks the existing source operations frame the provider state; every KEM callback retains the same routed provider. The restricted frame theorem therefore applies only to programs whose actual AST contains no KEM request. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProviderCallbacks
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes)
open RegistrationNativeProviderInterpreter (Provider State)
open RegistrationNativePublicSourceEffects (Private toPrivate fromPrivate)
open RegistrationNativeProviderBuildCaps (IsLocalKem)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

abbrev NativeState (n : Nat) (KemSK ProviderState : Type) := Private n KemSK × ProviderState

def pack (before : State n KemSK ProviderState) : NativeState n KemSK ProviderState :=
  (toPrivate before.1, before.2)

def unpack (before : NativeState n KemSK ProviderState) : State n KemSK ProviderState :=
  (fromPrivate before.1, before.2)

theorem unpack_pack (before : State n KemSK ProviderState) : unpack (pack before) = before := by
  cases before with
  | mk before extra => rw [pack, unpack, RegistrationNativePublicSourceEffects.layout]

theorem pack_unpack (before : NativeState n KemSK ProviderState) : pack (unpack before) = before := by
  rcases before with ⟨⟨world, pool, roots, receipts⟩, extra⟩
  rfl

def withPrivate (work : StateT (Private n KemSK) ProbComp Value) :
    StateT (NativeState n KemSK ProviderState) ProbComp Value := fun before =>
  (fun result => (result.1, (result.2, before.2))) <$> work.run before.1

noncomputable def implementation (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) (provider : Provider KemSK ProviderState) (selected : Bool) :
    QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK)
      (StateT (NativeState n KemSK ProviderState) ProbComp) := fun query before =>
  Prod.map id pack <$>
    (RegistrationNativeProviderSource.localImpl setup wire route sign seed scalar provider selected query).run (unpack before)

/-- Exact private reassembly commutes with the complete adaptive source program, including routed KEM operations. -/
theorem program_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) (provider : Provider KemSK ProviderState) (selected : Bool)
    (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) Value)
    (before : State n KemSK ProviderState) :
    Prod.map id pack <$>
      (simulateQ (RegistrationNativeProviderSource.localImpl setup wire route sign seed scalar provider selected) work).run before =
      (simulateQ (implementation setup wire route sign seed scalar provider selected) work).run (pack before) := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
  intro query current
  change Prod.map id pack <$>
    (RegistrationNativeProviderSource.localImpl setup wire route sign seed scalar provider selected query).run current =
    Prod.map id pack <$>
    (RegistrationNativeProviderSource.localImpl setup wire route sign seed scalar provider selected query).run (unpack (pack current))
  rw [unpack_pack]

/-- A non-KEM callback runs the original literal source and retains the provider as a complete frame. -/
theorem query_free (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) (provider : Provider KemSK ProviderState) (selected : Bool)
    (query : (RegistrationBeaconReferenceCompiler.Spec n KemSK).Domain) (quiet : ¬IsLocalKem query) :
    implementation setup wire route sign seed scalar provider selected query =
      withPrivate (RegistrationNativePublicSourceCallbacks.implementation setup wire route sign seed scalar query) := by
  funext before
  rcases query with message | (query | query)
  · have old := RegistrationNativePublicSourceCallbacks.query_source setup wire route sign seed scalar selected
      (.inl message) (fromPrivate before.1)
    simpa only [implementation, RegistrationNativeProviderSource.localImpl,
      RegistrationNativeProviderSource.localHandler, RegistrationNativePublicFrontend.liftLocal,
      simulateQ_spec_query, RegistrationNativeProviderInterpreter.handler,
      RegistrationNativeProviderSource.withBase_source, withPrivate, unpack,
      Functor.map_map, Prod.map_def, id_eq, pack,
      RegistrationNativePublicSourceEffects.toPrivate, RegistrationNativePublicSourceEffects.fromPrivate] using
      congrArg (fun distribution => (fun result => (result.1, (result.2, before.2))) <$> distribution) old
  · have old := RegistrationNativePublicSourceCallbacks.query_source setup wire route sign seed scalar selected
      (.inr (.inl query)) (fromPrivate before.1)
    simpa only [implementation, RegistrationNativeProviderSource.localImpl,
      RegistrationNativeProviderSource.localHandler, RegistrationNativePublicFrontend.liftLocal,
      simulateQ_spec_query, RegistrationNativeProviderInterpreter.handler,
      RegistrationNativeProviderSource.withBase_source, withPrivate, unpack,
      Functor.map_map, Prod.map_def, id_eq, pack,
      RegistrationNativePublicSourceEffects.toPrivate, RegistrationNativePublicSourceEffects.fromPrivate] using
      congrArg (fun distribution => (fun result => (result.1, (result.2, before.2))) <$> distribution) old
  · exact False.elim (quiet trivial)

/-- No-KEM ASTs use the established source interpreter without changing any provider coordinate. -/
theorem program_free (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) (provider : Provider KemSK ProviderState) (selected : Bool)
    (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) Value)
    (bounded : work.IsQueryBoundP IsLocalKem 0) (before : NativeState n KemSK ProviderState) :
    (simulateQ (implementation setup wire route sign seed scalar provider selected) work).run before =
      (fun result => (result.1, (result.2, before.2))) <$>
        (simulateQ (RegistrationNativePublicSourceCallbacks.implementation setup wire route sign seed scalar) work).run before.1 := by
  have same : simulateQ (implementation setup wire route sign seed scalar provider selected) work =
      simulateQ (fun query => withPrivate
        (RegistrationNativePublicSourceCallbacks.implementation setup wire route sign seed scalar query)) work := by
    induction work using OracleComp.inductionOn with
    | pure value => rfl
    | query_bind query next ih =>
        rw [isQueryBoundP_query_bind_iff] at bounded
        have quiet : ¬IsLocalKem query := bounded.1.resolve_right (Nat.not_lt_zero _)
        simp only [simulateQ_bind, simulateQ_spec_query]
        rw [query_free setup wire route sign seed scalar provider selected query quiet]
        apply congrArg (fun continuation => withPrivate
          (RegistrationNativePublicSourceCallbacks.implementation setup wire route sign seed scalar query) >>= continuation)
        funext reply
        exact ih reply (by simpa using bounded.2 reply)
  rw [same]
  let embed : Private n KemSK → NativeState n KemSK ProviderState := fun current => (current, before.2)
  simpa only [embed, Prod.map_def, id_eq] using
    (OracleComp.map_run_simulateQ_eq_of_query_map_eq
      (RegistrationNativePublicSourceCallbacks.implementation setup wire route sign seed scalar)
      (fun query => withPrivate (RegistrationNativePublicSourceCallbacks.implementation setup wire route sign seed scalar query))
      embed (fun _ _ => rfl) work before.1).symm

end BeaconcryptCore.Computational.RegistrationNativeProviderCallbacks

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderCallbacks.unpack_pack' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderCallbacks.unpack_pack
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderCallbacks.pack_unpack' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderCallbacks.pack_unpack
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderCallbacks.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderCallbacks.program_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderCallbacks.query_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderCallbacks.query_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderCallbacks.program_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderCallbacks.program_free
