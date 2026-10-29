-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedOpenSource
import BeaconcryptCore.Computational.RegistrationNativeG3NativeUniformAuditBound

/-! The actual known108 frontend at a fixed early challenge has the complete native result and same installation trace of the original fixed reference open program. The startup frontend is literalized and evaluated back exactly; no original public or private poststate is replaced. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedEarlySource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhKemIndCca
variable {ι KemSK P Value A : Type} {base : OracleSpec ι}

private theorem reference_values
    (provider : RegistrationNativeSecretWordNativePlain.NativeProvider KemSK P)
    (work : OracleComp (RegistrationNativeOpenKey.Spec KemSK) A) (state : P)
    (table : RegistrationNativeOpenKeyKemGame.Table) :
    (simulateQ ((PqxdhRegistrationJointKemSecondEntry.lazyImpl.mapStateTBase
        (RegistrationNativeOpenCompile.close RegistrationNativeKeyCompiler.coins provider)).flattenStateT) work).run' (state, table) =
      (simulateQ PqxdhRegistrationJointKemSecondEntry.lazyImpl
        ((simulateQ (RegistrationNativeOpenCompile.close RegistrationNativeKeyCompiler.coins provider) work).run' state)).run' table := by
  have actual := OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT PqxdhRegistrationJointKemSecondEntry.lazyImpl
    (RegistrationNativeOpenCompile.close RegistrationNativeKeyCompiler.coins provider) work state table
  have observed := congrArg (Functor.map (fun result => result.1.1)) actual
  simpa only [StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map] using observed.symm

/-- Every fixed actual uniform-provider continuation has precisely the original fixed reference program's joint result and original chronology. -/
theorem fixed_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret) (selectedAccept : Nat)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (front : RegistrationNativePublicFrontend.State source)
    (world : PqxdhRecordLiftWorld.State (budget.cap 4 + budget.cap 5))
    (seeds_empty : world.seeds = PqxdhRecordLiftLazyTable.initial) :
    LazyOracleDiscard.LawEq
      (RegistrationNativeG3MaterializedTracedProtocolLazy.fullGame setup (RegistrationNativeWire.ledgerCodec wire) route wire sign seed scalar candidate
        (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected pairs publicKey challenge candidate) source checks
        selected selectedAccept (setup.dh.publicKey scalar)
        (RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKeyId bounds mode work) front
        (RegistrationNativeSelectiveHiddenInterpreter.initial none, world))
      ((simulateQ (RegistrationNativeOpenKeyKemEarlySource.reference setup.baseImpl setup.kem selected pairs publicKey challenge candidate)
        (RegistrationNativeG3NativeCheckedUniformSource.openProgram setup checks wire source route sign selected selectedAccept (setup.dh.publicKey scalar) serverKeyId bounds mode seed scalar
          (setup.joint.staticDh seed (setup.dh.publicKey scalar)) work (RegistrationNativeG3NativeStartupFields.word front)
          (RegistrationNativeG3NativeUniformAuditBound.ordinary world))).run' ((PqxdhLiveKemBirth.empty, none), ∅)) := by
  have compared := RegistrationNativeG3MaterializedTracedOpenSource.frontend_source setup checks wire source route sign seed scalar candidate
    (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected pairs publicKey challenge candidate) none
    selected selectedAccept serverKeyId bounds mode work budget bounded front world seeds_empty
  rw [RegistrationNativeOpenKeyKemEarlySource.reference, reference_values]
  simpa only [RegistrationNativeG3MaterializedRetainedLazy.client, RegistrationNativeG3MaterializedRetainedSource.ordinary,
    RegistrationNativeHiddenInterpreter.initial, RegistrationNativeG3NativeUniformAuditBound.ordinary,
    RegistrationNativeG3NativeCheckedUniformSource.openProgram, RegistrationNativeG3NativeStartupFields.word_eval] using compared

/-- The same supported actual startup supplies the complete fixed-reference law, retaining its reached shared World cache and every original output. -/
theorem after_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret) (selectedAccept : Nat)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (born : RegistrationNativeHiddenStartup.Started source)
    (world : PqxdhRecordLiftWorld.State (budget.cap 4 + budget.cap 5))
    (supported : (some born, world) ∈ support
      (RegistrationNativeG3MaterializedTracedStartup.startup setup wire route source ensureInit identityIndex serverKeyId seed)) :
    LazyOracleDiscard.LawEq
      (RegistrationNativeG3MaterializedTracedStartup.fullAfter setup checks wire route source serverKeyId seed scalar candidate
        (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected pairs publicKey challenge candidate) none
        selected selectedAccept bounds mode adversary (some born, world))
      ((fun result => some (PqxdhRegistrationJointServerBirth.encode born.created, result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (RegistrationNativeOpenKeyKemEarlySource.reference setup.baseImpl setup.kem selected pairs publicKey challenge candidate)
          (RegistrationNativeG3NativeCheckedUniformSource.openProgram setup checks wire source route
            (RegistrationNativeMldsa.owned source born.native.credential) selected selectedAccept (setup.dh.publicKey scalar) serverKeyId bounds mode seed scalar
            (setup.joint.staticDh seed (setup.dh.publicKey scalar))
            (adversary ⟨setup.joint.publicKeys seed, born.native.credential.publicKey, serverKeyId⟩)
            (RegistrationNativeG3NativeStartupFields.word born.native.frontend)
            (RegistrationNativeG3NativeUniformAuditBound.ordinary world))).run' ((PqxdhLiveKemBirth.empty, none), ∅)) := by
  have cold := RegistrationNativeG3NativeStartupFields.initialized setup wire route source ensureInit identityIndex serverKeyId seed born world supported
  have compared := fixed_source setup checks wire source route (RegistrationNativeMldsa.owned source born.native.credential)
    seed scalar selected pairs publicKey challenge candidate selectedAccept serverKeyId bounds mode
    (adversary ⟨setup.joint.publicKeys seed, born.native.credential.publicKey, serverKeyId⟩) budget (bounded _) born.native.frontend world cold.2.2.2.2
  have mapped := LazyOracleDiscard.LawEq.map
    (fun result => some (PqxdhRegistrationJointServerBirth.encode born.created, result.1.1, (result.1.2, result.2))) compared
  simpa only [RegistrationNativeG3MaterializedTracedStartup.fullAfter, RegistrationNativeG3MaterializedTracedStartup.typedWork] using mapped

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedEarlySource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedEarlySource.fixed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedEarlySource.fixed_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedEarlySource.after_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedEarlySource.after_source
