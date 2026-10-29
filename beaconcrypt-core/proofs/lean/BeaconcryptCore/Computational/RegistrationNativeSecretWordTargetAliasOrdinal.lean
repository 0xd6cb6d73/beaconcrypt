-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOrdinal
import BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedAliasSource

/-! The whole concrete alias client closes into the same monitored full-ledger target kernel for any stateless outer table. The final ordinal receipt therefore applies to every normalized finite-table component of the actual byte-cache source, while retaining the complete alias result. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAliasOrdinal
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (FreshBounds Mode Budget)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterpreter (Provider)
open PqxdhKemIndCca
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

def observed (result : RegistrationNativeSecretWordAliasClient.Result source n KemSK Value) :
    RegistrationNativeEvents.Observed Value (RegistrationNativeSecretWordTargetTracedSource.State n KemSK source) :=
  (result.1.1.1.1, (result.1.1.1.2, ((result.1.1.2, result.1.2), result.2)))

/-- Closing the same complete alias result is exactly the original monitored full-ledger kernel. -/
theorem closed_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (serverKeyId : U64) (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : RegistrationNativeSecretWordMessage.State source) (ordinary : RegistrationNativePublicInterpreter.State n KemSK)
    (kem : RegistrationNativeSecretWordKemProvider.State KemSK) :
    observed <$> simulateQ outer (RegistrationNativeSecretWordAliasClient.client setup checks wire source route sign input inside provider
      selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work before ordinary kem) =
      RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
        (RegistrationNativeSecretWordTargetTracedSource.typed setup checks wire route sign input inside provider outer
          selectedOwner selectedAccept publicPrekey) mode work
        ((before, RegistrationNativeSecretWordFrontendTrace.initial), RegistrationNativeSecretWordInterpreter.initial ordinary kem) := by
  have actual := RegistrationNativeSecretWordTargetTracedProgram.run_source setup checks wire route sign input inside provider outer
    selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work before RegistrationNativeSecretWordFrontendTrace.initial
    (RegistrationNativeSecretWordInterpreter.initial ordinary kem)
  simp only [RegistrationNativeSecretWordAliasClient.client, RegistrationNativeSecretWordInterpreter.execute,
    RegistrationNativeSecretWordFrontendTrace.program]
  rw [QueryImpl.simulateQ_mapStateTBase_run]
  change (fun (result : RegistrationNativeSecretWordAliasClient.Result source n KemSK Value) =>
    (result.1.1.1.1, (result.1.1.1.2, ((result.1.1.2, result.1.2), result.2)))) <$> _ = _
  simpa only [RegistrationNativeSecretWordTargetSource.implementation] using actual

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (pairs : List (MlKem768PublicKey × KemSK)) (chosen : MlKem768PublicKey × KemSK) (challenge : MlKem768Ciphertext)
  (outer : QueryImpl Combined ProbComp) (serverKeyId : U64) (bounds : FreshBounds) (mode : Mode)
  (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (budget : Budget)
  (selectedTarget : Fin budget.accept × Fin budget.capacity)
local notation "nativeInput" => RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar
local notation "nativeInside" => RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selectedTarget.2.val pairs chosen.1 challenge
local notation "client" => RegistrationNativeSecretWordAliasClient.client setup checks wire source route sign nativeInput nativeInside provider
  selectedTarget.2.val selectedTarget.1.val (setup.dh.publicKey scalar) serverKeyId bounds mode work

/-- Every actual stateless-table alias execution of a good target has the selected final ordinal of its same claimed handle. -/
theorem selected (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (chosenAt : pairs[selectedTarget.2.val]? = some chosen) (readback : RegistrationNativeWire.InitReadBack wire)
    (responseReadback : RegistrationNativeWire.ResponseReadBack wire)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (before : RegistrationNativeSecretWordMessage.State source)
    (initialCounter : before.parsedAccepts = 0) (ownersEmpty : before.beacons = [])
    (initialPin : PqxdhRefinement.absBytes before.server.pin.binding.identity_public_key = (setup.joint.publicKeys seed).ed25519.toList)
    (ordinary : RegistrationNativePublicInterpreter.State n KemSK) (candidate : MlKemSharedSecret)
    (result : RegistrationNativeSecretWordAliasClient.Result source n KemSK Value)
    (supported : result ∈ support (simulateQ outer (client before ordinary (RegistrationNativeSecretWordKemPool.empty, none))))
    (winning : RegistrationNativePrekeyEvents.GoodAt setup.source.crypto wire serverKeyId budget selectedTarget claim
      (result.1.1.1.1, (result.1.1.1.2, ()))) :
    RegistrationNativeInstallTarget.Claimed claim result.1.1.1.1 result.1.1.1.2
      (result.1.2.events.map (RegistrationNativeSecretWordCheckedTrace.event candidate))
      (fun message => ∀ bytes, RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar message = some bytes →
        RegistrationNativeSelectiveHiddenService.selected
          (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate bytes = true) := by
  have actual := Set.mem_image_of_mem observed supported
  rw [← support_map, closed_source setup checks wire route sign nativeInput nativeInside provider outer
    selectedTarget.2.val selectedTarget.1.val (setup.dh.publicKey scalar) serverKeyId bounds mode work before ordinary
      (RegistrationNativeSecretWordKemPool.empty, none)] at actual
  have path := (RegistrationNativeSecretWordTargetTracedPath.run setup checks wire route sign nativeInput nativeInside provider outer
    selectedTarget.2.val selectedTarget.1.val (setup.dh.publicKey scalar) serverKeyId bounds mode work
    ((before, RegistrationNativeSecretWordFrontendTrace.initial), RegistrationNativeSecretWordInterpreter.initial ordinary
      (RegistrationNativeSecretWordKemPool.empty, none)) (observed result) actual).1
  have good : RegistrationNativePrekeyEvents.GoodAt setup.source.crypto wire serverKeyId budget selectedTarget claim (observed result) := by
    simpa only [RegistrationNativePrekeyEvents.GoodAt, observed] using winning
  exact RegistrationNativeSecretWordTargetOrdinal.selected setup checks wire route sign seed scalar pairs chosen challenge outer serverKeyId bounds mode work budget
    selectedTarget bounded reserved chosenAt readback responseReadback claim
    ((before, RegistrationNativeSecretWordFrontendTrace.initial), RegistrationNativeSecretWordInterpreter.initial ordinary
      (RegistrationNativeSecretWordKemPool.empty, none)) initialCounter rfl ownersEmpty rfl initialPin candidate rfl (observed result) actual path good

/-- The actual stateful byte-cache good-target probability is bounded by its same-result native selected ordinal, using the exact normalized finite-table source. -/
theorem bytes_probability (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (chosenAt : pairs[selectedTarget.2.val]? = some chosen) (readback : RegistrationNativeWire.InitReadBack wire)
    (responseReadback : RegistrationNativeWire.ResponseReadBack wire)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (before : RegistrationNativeSecretWordMessage.State source)
    (initialCounter : before.parsedAccepts = 0) (ownersEmpty : before.beacons = [])
    (initialPin : PqxdhRefinement.absBytes before.server.pin.binding.identity_public_key = (setup.joint.publicKeys seed).ed25519.toList)
    (ordinary : RegistrationNativePublicInterpreter.State n KemSK) (candidate : MlKemSharedSecret) :
    Pr{let result ← (simulateQ (RegistrationNativeSecretWordRecoveryBound.bytes setup.source candidate)
      (client before ordinary (RegistrationNativeSecretWordKemPool.empty, none))).run' ∅}[
        RegistrationNativePrekeyEvents.GoodAt setup.source.crypto wire serverKeyId budget selectedTarget claim
          (result.1.1.1.1, (result.1.1.1.2, ()))] ≤
    Pr{let result ← (simulateQ (RegistrationNativeSecretWordRecoveryBound.bytes setup.source candidate)
      (client before ordinary (RegistrationNativeSecretWordKemPool.empty, none))).run' ∅}[
        RegistrationNativeInstallTarget.Claimed claim result.1.1.1.1 result.1.1.1.2
          (result.1.2.events.map (RegistrationNativeSecretWordCheckedTrace.event candidate))
          (fun message => ∀ bytes, RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar message = some bytes →
            RegistrationNativeSelectiveHiddenService.selected
              (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate bytes = true)] := by
  classical
  let actual := client before ordinary (RegistrationNativeSecretWordKemPool.empty, none)
  let : MeasurableSpace (RegistrationNativeSecretWordAliasClient.Result source n KemSK Value) := ⊤
  let : DiscreteMeasurableSpace (RegistrationNativeSecretWordAliasClient.Result source n KemSK Value) :=
    ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have sourceEq := _root_.EvalDistEq.of_evalDist_eq
    (RegistrationNativeSecretWordAliasTable.bytes_eager setup.source candidate actual).evalDist_eq
  rw [sourceEq.prEvent_eq, sourceEq.prEvent_eq]
  apply prEvent_mono_of_support
  intro result supported winning
  rw [mem_support_bind_iff] at supported
  obtain ⟨table, _sampled, called⟩ := supported
  exact selected setup checks wire route sign seed scalar pairs chosen challenge
    (RegistrationNativeSecretWordAliasTable.normalizedFixed table setup.source candidate) serverKeyId bounds mode work budget selectedTarget
    bounded reserved chosenAt readback responseReadback claim before initialCounter ownersEmpty initialPin ordinary candidate result called winning

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAliasOrdinal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAliasOrdinal.closed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAliasOrdinal.closed_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAliasOrdinal.selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAliasOrdinal.selected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAliasOrdinal.bytes_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAliasOrdinal.bytes_probability
