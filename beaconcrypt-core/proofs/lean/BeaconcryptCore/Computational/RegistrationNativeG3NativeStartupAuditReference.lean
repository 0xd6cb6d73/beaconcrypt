-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupAuditSource

/-! The actual marked startup continuation is bounded at each literal candidate by the same original fixed early-provider client trace, retaining the entire reached World. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupAuditReference
open PqxdhServerAuthExperiment (Setup Checks)
variable {ι KemSK Value : Type} {base : OracleSpec ι}
attribute [local irreducible] uniformSample RegistrationNativeSuffixKeyPrf.value
private theorem reference_values {A P : Type}
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


/-- The actual successful audit continuation implies repetition in its same full original fixed-reference execution. -/
theorem after_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (route : RawCtxServerRouting.SenderDecoder)
    (serverKeyId : U64) (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1))
    (profile : RegistrationNativeSecretWordAliasOuter.Profile KemSK) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (born : RegistrationNativeHiddenStartup.Started source)
    (bounded : RegistrationNativeInterface.Respects budget
      (adversary ⟨setup.joint.publicKeys seed, born.native.credential.publicKey, serverKeyId⟩))
    (world : PqxdhRecordLiftWorld.State (budget.cap 4 + budget.cap 5))
    (unused : ∀ slot role, world.used slot role = false) :
    Pr{let marked ← (RegistrationNativeG3NativeStartupAuditSource.after setup checks wire source route serverKeyId seed scalar candidate
      (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val profile.pairs profile.publicKey profile.challenge candidate)
      none selected.val selectedAccept bounds mode adversary born world)}[marked = true] ≤
    Pr{let result ← ((simulateQ (RegistrationNativeOpenKeyKemEarlySource.reference setup.baseImpl setup.kem selected.val
      profile.pairs profile.publicKey profile.challenge candidate)
      (RegistrationNativeG3NativeCheckedUniformSource.openProgram setup checks wire source route
        (RegistrationNativeMldsa.owned source born.native.credential) selected.val selectedAccept (setup.dh.publicKey scalar) serverKeyId
        bounds mode seed scalar (setup.joint.staticDh seed (setup.dh.publicKey scalar))
        (adversary ⟨setup.joint.publicKeys seed, born.native.credential.publicKey, serverKeyId⟩)
        (RegistrationNativeG3NativeStartupFields.word born.native.frontend)
        (RegistrationNativeG3NativeUniformAuditBound.ordinary world))).run' ((PqxdhLiveKemBirth.empty, none), ∅))}[
      RegistrationNativeG3AuditRepeatOpenKey.Event setup seed scalar candidate result] := by
  rw [RegistrationNativeOpenKeyKemEarlySource.reference, reference_values]
  have point := RegistrationNativeG3AuditRepeatOpenKey.bound setup wire route
    (RegistrationNativeMldsa.owned source born.native.credential) seed scalar candidate checks source selected.val selectedAccept
    (setup.dh.publicKey scalar) serverKeyId bounds mode
    (adversary ⟨setup.joint.publicKeys seed, born.native.credential.publicKey, serverKeyId⟩) born.native.frontend budget bounded
    (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val profile.pairs profile.publicKey profile.challenge candidate)
    (RegistrationNativeHiddenInterpreter.initial none) world unused
  simp only [RegistrationNativeG3NativeStartupAuditSource.after, RegistrationNativeG3NativeCheckedUniformSource.openProgram,
    RegistrationNativeG3MaterializedRetainedLazy.client, RegistrationNativeG3MaterializedRetainedSource.ordinary,
    RegistrationNativeG3NativeUniformAuditBound.ordinary, RegistrationNativeHiddenInterpreter.initial,
    RegistrationNativeG3NativeStartupFields.word_eval] at point ⊢
  convert point using 1

end BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupAuditReference
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupAuditReference.after_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupAuditReference.after_bound
