-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedAliasSource
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemEarlyObservedUniform
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemTransport

/-! The initialized original native G2 uniform branch with a candidate-retaining pure final observer is the exact byte-view experiment of the full alias client. Every native query and target index stays in its original place. Original Respects derives all creation and no-reveal bills; the running alias client never receives the mathematical candidate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedUniformSource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhKemIndCca
open PqxdhInitializerSecrecy (kemAmbientImpl)
open RegistrationNativeG3NativeCheckedAliasSource (view aliasClient)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

abbrev Result (source : RegistrationNativeMldsa.Source) (Value : Type) :=
  (((Value × RegistrationNativeLedger.State) × RegistrationNativePublicFrontend.State source) × RegistrationNativeG2Trace.State)

/-- A cold original Server frontend contains no symbolic reference, so its native initial state is independent of the mathematical candidate. -/
theorem cold_eval {source : RegistrationNativeMldsa.Source} (before : RegistrationNativeSecretWordMessage.State source)
    (empty : before.server.sessions = []) (candidate : MlKemSharedSecret) :
    before.eval candidate = before.eval RegistrationNativeSecretWordMessage.zero := by
  simp only [RegistrationNativeSecretWordMessage.State.eval, RegistrationNativeSecretWordMessage.ServerState.eval,
    empty, List.map_nil]

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (source : RegistrationNativeMldsa.Source) (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (serverKeyId : U64)
  (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (target : Option PqxdhJointIdentity.DhOutput)
  (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
  (before : RegistrationNativeSecretWordMessage.State source)
  (ordinary : RegistrationNativePublicInterpreter.State n KemSK)

noncomputable def openProgram : OracleComp (RegistrationNativeOpenKey.Spec KemSK) (Result source Value) :=
  RegistrationNativeOpenKey.client setup.source (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
    (RegistrationNativeKeyFamilyPreparation.inside target)
    (RegistrationNativeOpenRetained.client setup wire route sign
      (RegistrationNativeG2Trace.program
        (RegistrationNativePublicFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId
          bounds mode work (before.eval RegistrationNativeSecretWordMessage.zero))) ordinary)

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

/-- Each fixed early challenge has precisely the complete original native frontend and chronology of the actual byte alias execution. -/
theorem fixed_source (empty : before.server.sessions = [])
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret) :
    (simulateQ (RegistrationNativeOpenKeyKemEarlySource.reference setup.baseImpl setup.kem selected pairs publicKey challenge candidate)
      (openProgram setup checks wire source route sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode seed scalar target work before ordinary)).run'
      ((PqxdhLiveKemBirth.empty, none), ∅) =
      view candidate <$> (simulateQ (RegistrationNativeSecretWordRecoveryBound.bytes setup.source candidate)
        (aliasClient setup checks wire source route sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode seed scalar
          target selected pairs publicKey challenge work before ordinary (RegistrationNativeSecretWordKemPool.empty, none))).run' ∅ := by
  have actual := RegistrationNativeG3NativeCheckedAliasSource.bytes_source setup checks wire source route sign selectedOwner selectedAccept publicPrekey serverKeyId
    bounds mode seed scalar target selected pairs publicKey challenge candidate work before ordinary (RegistrationNativeSecretWordKemPool.empty, none) empty
  simp only [RegistrationNativeG3NativeCheckedOpenClient.client, cold_eval before empty candidate] at actual
  rw [RegistrationNativeOpenKeyKemEarlySource.reference, reference_values]
  exact actual

private theorem native_bound (kind : RegistrationNativeKemBeaconFootprint.Kind)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work) :
    (simulateQ RegistrationNativeOpenKey.native
      (openProgram setup checks wire source route sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode seed scalar target work before ordinary)).IsQueryBoundP
      (RegistrationNativeKemCompilerFootprint.predicate RegistrationNativeOpenKey.Ambient KemSK kind)
      (if kind = .create then budget.create else 0) := by
  apply RegistrationNativeOpenKeyKemTransport.native_bound
  apply RegistrationNativeOpenKeyKemTransport.key_bound
  apply RegistrationNativeOpenKeyKemTransport.retained_bound
  apply RegistrationNativeG2Trace.program_bound
  exact RegistrationNativeOpenKeyKemPublic.run_bound (kind := kind) setup checks wire source sign selectedOwner selectedAccept
    publicPrekey serverKeyId bounds mode work budget bounded _

private theorem creates (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work) :
    (simulateQ RegistrationNativeOpenKey.native
      (openProgram setup checks wire source route sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode seed scalar target work before ordinary)).IsQueryBoundP
      (RegistrationNativeKemReservation.IsCreate (ambient := RegistrationNativeOpenKey.Ambient) (KemSK := KemSK)) budget.create := by
  have bill := native_bound setup checks wire source route sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode seed scalar target work before ordinary .create budget bounded
  simp only [ite_true] at bill
  apply OracleComp.IsQueryBoundP.of_imp _ bill
  intro query counted
  rcases query with query | (query | key)
  · exact counted.elim
  · cases query <;> simp_all [RegistrationNativeKemReservation.IsCreate, RegistrationNativeKemCompilerFootprint.predicate]
  · exact counted.elim

private theorem no_reveal (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work) :
    (simulateQ RegistrationNativeOpenKey.native
      (openProgram setup checks wire source route sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode seed scalar target work before ordinary)).IsQueryBoundP
      (RegistrationNativeKemPoolSource.IsReveal (ambient := RegistrationNativeOpenKey.Ambient) (KemSK := KemSK)) 0 := by
  have bill := native_bound setup checks wire source route sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode seed scalar target work before ordinary .reveal budget bounded
  simp only [reduceCtorEq, ite_false] at bill
  apply OracleComp.IsQueryBoundP.of_imp _ bill
  intro query counted
  rcases query with query | (query | key)
  · exact counted.elim
  · cases query <;> simp_all [RegistrationNativeKemPoolSource.IsReveal, RegistrationNativeKemCompilerFootprint.predicate]
  · exact counted.elim

/-- Original Respects supplies both actual native KEM resource certificates for the unchanged whole client; pure final candidate observations require no additional premise. -/
theorem resource_bounds (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work) :
    (simulateQ RegistrationNativeOpenKey.native
      (openProgram setup checks wire source route sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode seed scalar target work before ordinary)).IsQueryBoundP
        (RegistrationNativeKemReservation.IsCreate (ambient := RegistrationNativeOpenKey.Ambient) (KemSK := KemSK)) budget.create ∧
    (simulateQ RegistrationNativeOpenKey.native
      (openProgram setup checks wire source route sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode seed scalar target work before ordinary)).IsQueryBoundP
        (RegistrationNativeKemPoolSource.IsReveal (ambient := RegistrationNativeOpenKey.Ambient) (KemSK := KemSK)) 0 :=
  ⟨creates setup checks wire source route sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode seed scalar target work before ordinary budget bounded,
   no_reveal setup checks wire source route sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode seed scalar target work before ordinary budget bounded⟩

noncomputable def bytesView (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create + 1))
    (observe : MlKemSharedSecret → Result source Value → Bool) : ProbComp Bool := do
  let chosen ← simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen
  let others ← PqxdhLiveKemSelection.sampleFamily (simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen) budget.create
  let pair ← simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps chosen.1)
  RegistrationNativeSecretWordRecoveryBound.bytesView setup.source
    (fun candidate result => observe candidate (view candidate result.1))
    (aliasClient setup checks wire source route sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode seed scalar target
      selected.val (List.ofFn (selected.insertNth chosen others)) chosen.1 pair.1 work before ordinary
      (RegistrationNativeSecretWordKemPool.empty, none))

/-- The initialized actual early uniform G2 branch is the same complete byte-view alias observation, retaining the supplied challenge candidate and original selected target multiplicity. Original Respects discharges all internal resource bills. -/
theorem uniform_source (empty : before.server.sessions = [])
    (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (selected : Fin (budget.create + 1)) (observe : MlKemSharedSecret → Result source Value → Bool) :
    RegistrationNativeKemEarlyObservedGame.branch setup.baseImpl setup.kem
      (RegistrationNativeOpenKeyKemGame.other setup.baseImpl setup.kem) (pure ∅)
      (simulateQ RegistrationNativeOpenKey.native
        (openProgram setup checks wire source route sign selected.val selectedAccept publicPrekey serverKeyId bounds mode seed scalar target work before ordinary))
      observe budget.create selected false =ᵈ
      bytesView setup checks wire source route sign selected.val selectedAccept publicPrekey serverKeyId bounds mode seed scalar target work before ordinary budget selected observe := by
  have sourceEq := RegistrationNativeOpenKeyKemEarlyObservedUniform.uniform_source setup.baseImpl setup.kem
    (openProgram setup checks wire source route sign selected.val selectedAccept publicPrekey serverKeyId bounds mode seed scalar target work before ordinary)
    observe budget.create selected
    (creates setup checks wire source route sign selected.val selectedAccept publicPrekey serverKeyId bounds mode seed scalar target work before ordinary budget bounded)
    (no_reveal setup checks wire source route sign selected.val selectedAccept publicPrekey serverKeyId bounds mode seed scalar target work before ordinary budget bounded)
  refine sourceEq.trans ?_
  unfold RegistrationNativeOpenKeyKemEarlyObservedUniform.source bytesView
  apply _root_.EvalDistEq.bind_right
  intro chosen
  apply _root_.EvalDistEq.bind_right
  intro others
  apply _root_.EvalDistEq.bind_right
  intro pair
  unfold RegistrationNativeSecretWordRecoveryBound.bytesView
  apply _root_.EvalDistEq.bind_right
  intro candidate
  rw [fixed_source setup checks wire source route sign selected.val selectedAccept publicPrekey serverKeyId bounds mode seed scalar target work before ordinary empty]
  simp only [StateT.run'_eq, Functor.map_map]
  exact .rfl

end BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedUniformSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedUniformSource.cold_eval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedUniformSource.cold_eval
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedUniformSource.fixed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedUniformSource.fixed_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedUniformSource.uniform_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedUniformSource.uniform_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedUniformSource.resource_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedUniformSource.resource_bounds
