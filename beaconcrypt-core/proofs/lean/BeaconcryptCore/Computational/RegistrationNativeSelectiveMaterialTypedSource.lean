-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialSource

/-! The original public typed Server build closes to the same current-environment selective material service. The exact frontend and thin private poststates are restored after the actual one-use controller executes. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialTypedSource
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK ProviderState : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- The actual public typed build and normalized service have exactly the same complete native result and poststates. -/
theorem build (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (handle : Nat) (application : Option (Slice U8)) (frontend : RegistrationNativePublicFrontend.State source)
    (before : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) :
    (simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider)
      ((RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey
        (.inr (.build handle application))).run frontend)).run before =
      (fun result => ((result.1.1, { frontend with server := result.1.2, environment := result.2.1 }), result.2.2)) <$>
        (simulateQ (RegistrationNativeSelectiveMaterialService.handler setup wire sign seed scalar candidate provider)
          ((RegistrationServerMaterialFrontend.build wire checks.reservePeer handle application).run frontend.server)).run
            (frontend.environment, before) := by
  have normalized := congrArg (Functor.map (fun result =>
      ((result.1.1, { frontend with server := result.1.2, environment := result.2.1 }), result.2.2)))
    (RegistrationNativeSelectiveMaterialSource.program_source setup wire sign seed scalar candidate provider
      ((RegistrationServerMaterialFrontend.build wire checks.reservePeer handle application).run frontend.server) frontend.environment before)
  simp only [RegistrationNativeSelectiveMaterialSource.closedLocal, RegistrationNativeSelectiveMaterialSource.original,
    QueryImpl.simulateQ_compose, RegistrationNativePublicFrontend.handler, RegistrationNativePublicFrontend.serverOpen,
    RegistrationServerOpenReferenceCompiler.build, StateT.run, simulateQ_map, map_apply, Functor.map_map, Prod.map_def, id_eq] at *
  convert normalized using 1
  rfl

end BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialTypedSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialTypedSource.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialTypedSource.build
