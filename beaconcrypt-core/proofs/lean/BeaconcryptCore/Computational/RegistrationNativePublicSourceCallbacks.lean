-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicSourceEffects
import BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceStage

/-! The mixed public frontend and the native open Server source controller use one exact private layout. This module transports the real source callbacks and entire adaptive open programs; source roots remain private and the one chronological signing log stays in the current environment. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicSourceCallbacks
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePublicInterpreter (State M)
open RegistrationNativePublicSourceEffects (Private Extra close toPrivate fromPrivate)
open RegistrationNativeRelatedFamily (Message)
open PqxdhSecretInputKdf (RootOutput)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

def interpret (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (work : M n KemSK Value) : StateT (Private n KemSK) ProbComp Value :=
  fun before => Prod.map id toPrivate <$> (close setup seed scalar work).run (fromPrivate before)

def remember (before : Extra) (message : Message) (root : Option RootOutput) : Extra :=
  (Function.update before.1 message root, before.2)

noncomputable def services (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) :
    RegistrationNativeKemReferenceEffects.Callbacks n KemSK Extra where
  other := RegistrationNativePublicInterpreter.unavailable
  prepare := fun message => interpret setup seed scalar
    (RegistrationNativePublicInterpreter.handler setup wire route sign (.inl (.inl message)))
  demand := fun message => interpret setup seed scalar
    (RegistrationNativePublicInterpreter.handler setup wire route sign (.inl (.inr (.inl (.inl message)))))
  publication := fun query => interpret setup seed scalar
    (RegistrationNativePublicInterpreter.publication setup wire sign query)

noncomputable def implementation (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) :
    QueryImpl (RegistrationNativeKemReferenceCompiler.Spec n KemSK) (StateT (Private n KemSK) ProbComp) :=
  RegistrationNativeKemReferenceEffects.implementation setup
    (RegistrationServerOpenReferenceSourceStage.callbacks setup seed scalar remember
      (services setup wire route sign seed scalar))

/-- Every actual mixed-client callback is the same native source callback after exact private layout reassembly. -/
theorem query_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (selected : Bool) (query : (RegistrationNativeKemReferenceCompiler.Spec n KemSK).Domain)
    (before : State n KemSK) :
    Prod.map id toPrivate <$> (close setup seed scalar
      (simulateQ (RegistrationNativePublicInterpreter.handler setup wire route sign)
        (RegistrationNativePublicFrontend.liftLocal selected query))).run before =
      (implementation setup wire route sign seed scalar query).run (toPrivate before) := by
  cases query with
  | inl message =>
      simp only [RegistrationNativePublicFrontend.liftLocal, simulateQ_spec_query,
        RegistrationNativePublicInterpreter.handler, simulateQ_spec_query, implementation, RegistrationNativeKemReferenceEffects.implementation,
        RegistrationNativeKemReferenceWorld.handler,
        RegistrationServerOpenReferenceSourceStage.callbacks,
        toPrivate, ]
      rfl
  | inr query => cases query with
    | inl query => cases query with
      | inl message =>
          simp only [RegistrationNativePublicFrontend.liftLocal, simulateQ_spec_query,
            implementation, RegistrationNativeKemReferenceEffects.implementation,
            RegistrationNativeKemReferenceWorld.handler,
            RegistrationServerOpenReferenceSourceStage.callbacks, services, ]
          rfl
      | inr query => cases query with
        | inl query =>
            simp only [RegistrationNativePublicFrontend.liftLocal, simulateQ_spec_query,
              implementation, RegistrationNativeKemReferenceEffects.implementation,
              RegistrationNativeKemReferenceWorld.handler,
              RegistrationServerOpenReferenceSourceStage.callbacks, services, RegistrationNativePublicInterpreter.handler, RegistrationNativePublicInterpreter.common]
            rfl
        | inr query =>
            simp only [RegistrationNativePublicFrontend.liftLocal, simulateQ_spec_query,
              RegistrationNativePublicInterpreter.handler, RegistrationNativePublicInterpreter.common,
              RegistrationNativePublicInterpreter.effect]
            rw [RegistrationNativePublicSourceEffects.close_world]
            simp only [implementation, RegistrationNativeKemReferenceEffects.implementation,
              RegistrationNativeKemReferenceWorld.handler, RegistrationNativeKemReferenceWorld.effect,
              RegistrationNativeKemReferenceWorld.withWorld, StateT.run, Functor.map_map,
              toPrivate, Prod.map, id_eq]
            rfl
    | inr query =>
        rw [RegistrationNativePublicSourceEffects.routed_real]
        exact RegistrationNativePublicSourceEffects.kem_source setup seed scalar query before

private theorem close_simulate {Index : Type} {spec : OracleSpec Index}
    (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (handler : QueryImpl spec (M n KemSK))
    (work : OracleComp spec Value) (before : State n KemSK) :
    (close setup seed scalar (simulateQ handler work)).run before =
      (simulateQ (fun query => close setup seed scalar (handler query)) work).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure output => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, close, StateT.run,
        StateT.monad_bind_def, StateT.bind, simulateQ_bind]
      apply bind_congr
      rintro ⟨output, after⟩
      exact ih output after

/-- Complete adaptive open clients retain every native source result and private coordinate under the callback layout. -/
theorem program_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (selected : Bool) (work : OracleComp (RegistrationNativeKemReferenceCompiler.Spec n KemSK) Value)
    (before : State n KemSK) :
    Prod.map id toPrivate <$> (close setup seed scalar
      (simulateQ (RegistrationNativePublicInterpreter.handler setup wire route sign)
        (simulateQ (RegistrationNativePublicFrontend.liftLocal selected) work))).run before =
      (simulateQ (implementation setup wire route sign seed scalar) work).run (toPrivate before) := by
  rw [← QueryImpl.simulateQ_compose, close_simulate]
  induction work using OracleComp.inductionOn generalizing before with
  | pure output => simp only [simulateQ_pure, StateT.run_pure, map_pure]; rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      calc
        _ = (Prod.map id toPrivate <$> (close setup seed scalar
          ((RegistrationNativePublicInterpreter.handler setup wire route sign ∘ₛ
            RegistrationNativePublicFrontend.liftLocal selected) query)).run before) >>= fun reached =>
              (simulateQ (implementation setup wire route sign seed scalar) (next reached.1)).run reached.2 := by
          rw [bind_map_left]
          apply bind_congr
          rintro ⟨output, after⟩
          exact ih output after
        _ = _ := by rw [QueryImpl.compose, query_source]

end BeaconcryptCore.Computational.RegistrationNativePublicSourceCallbacks
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceCallbacks.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceCallbacks.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceCallbacks.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceCallbacks.program_source
