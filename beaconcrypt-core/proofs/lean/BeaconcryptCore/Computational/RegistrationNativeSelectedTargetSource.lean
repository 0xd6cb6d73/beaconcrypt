-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAliasOrdinal
import BeaconcryptCore.Computational.RegistrationNativeG3NativeTargetFixed
import BeaconcryptCore.Computational.RegistrationNativeG3NativeTargetStartup
import BeaconcryptCore.Computational.RegistrationNativeSelectedRecordTrace

/-! A ledger-only selector is retained through each actual good-target provenance step. The underlying alias theorem supplies a pointwise selected installation receipt on the same supported result; complete output laws preserve both the original ledger and chronological trace. No conjunction is inferred from an unselected probability inequality. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectedTargetSource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (Budget FreshBounds Mode)
open PqxdhKemIndCca
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (pairs : List (MlKem768PublicKey × KemSK)) (chosen : MlKem768PublicKey × KemSK) (challenge : MlKem768Ciphertext)
  (serverKeyId : U64) (bounds : FreshBounds) (mode : Mode)
  (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (budget : Budget)
  (selectedTarget : Fin budget.accept × Fin budget.capacity)
local notation "nativeInput" => RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar
local notation "nativeInside" => RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem (Fin.val (Prod.snd selectedTarget)) pairs (Prod.fst chosen) challenge
local notation "client" => RegistrationNativeSecretWordAliasClient.client setup checks wire source route sign nativeInput nativeInside provider
  (Fin.val (Prod.snd selectedTarget)) (Fin.val (Prod.fst selectedTarget)) (setup.dh.publicKey scalar) serverKeyId bounds mode work

/-- Finite-table source equality retains selection on the very result whose target receipt is proved pointwise. -/
theorem bytes_probability (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (chosenAt : pairs[selectedTarget.2.val]? = some chosen) (readback : RegistrationNativeWire.InitReadBack wire)
    (responseReadback : RegistrationNativeWire.ResponseReadBack wire)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (select : Value × RegistrationNativeLedger.State → Bool)
    (before : RegistrationNativeSecretWordMessage.State source)
    (initialCounter : before.parsedAccepts = 0) (ownersEmpty : before.beacons = [])
    (initialPin : PqxdhRefinement.absBytes before.server.pin.binding.identity_public_key = (setup.joint.publicKeys seed).ed25519.toList)
    (ordinary : RegistrationNativePublicInterpreter.State n KemSK) (candidate : MlKemSharedSecret) :
    Pr{let result ← (simulateQ (RegistrationNativeSecretWordRecoveryBound.bytes setup.source candidate)
      (client before ordinary (RegistrationNativeSecretWordKemPool.empty, none))).run' ∅}[
        RegistrationNativePrekeyEvents.GoodAt setup.source.crypto wire serverKeyId budget selectedTarget claim
          (result.1.1.1.1, (result.1.1.1.2, ())) ∧ select (result.1.1.1.1, result.1.1.1.2) = true] ≤
    Pr{let result ← (simulateQ (RegistrationNativeSecretWordRecoveryBound.bytes setup.source candidate)
      (client before ordinary (RegistrationNativeSecretWordKemPool.empty, none))).run' ∅}[
        RegistrationNativeInstallTarget.Claimed claim result.1.1.1.1 result.1.1.1.2
          (result.1.2.events.map (RegistrationNativeSecretWordCheckedTrace.event candidate))
          (fun message => ∀ bytes, RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar message = some bytes →
            RegistrationNativeSelectiveHiddenService.selected
              (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate bytes = true) ∧
          select (result.1.1.1.1, result.1.1.1.2) = true] := by
  classical
  let actual := client before ordinary (RegistrationNativeSecretWordKemPool.empty, none)
  let : MeasurableSpace (RegistrationNativeSecretWordAliasClient.Result source n KemSK Value) := ⊤
  let : DiscreteMeasurableSpace (RegistrationNativeSecretWordAliasClient.Result source n KemSK Value) := ⟨fun _ => trivial⟩
  have sourceEq := _root_.EvalDistEq.of_evalDist_eq
    (RegistrationNativeSecretWordAliasTable.bytes_eager setup.source candidate actual).evalDist_eq
  rw [sourceEq.prEvent_eq, sourceEq.prEvent_eq]
  apply prEvent_mono_of_support
  intro result supported winning
  rw [mem_support_bind_iff] at supported
  obtain ⟨table, _sampled, called⟩ := supported
  exact ⟨RegistrationNativeSecretWordTargetAliasOrdinal.selected setup checks wire route sign seed scalar pairs chosen challenge
    (RegistrationNativeSecretWordAliasTable.normalizedFixed table setup.source candidate) serverKeyId bounds mode work budget selectedTarget
    bounded reserved chosenAt readback responseReadback claim before initialCounter ownersEmpty initialPin ordinary candidate result called winning.1,
    winning.2⟩


/-- The complete fixed native source preserves the same ledger selector together with its proved final installation receipt. -/
theorem fixed_probability (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (chosenAt : pairs[selectedTarget.2.val]? = some chosen) (readback : RegistrationNativeWire.InitReadBack wire)
    (responseReadback : RegistrationNativeWire.ResponseReadBack wire)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (select : Value × RegistrationNativeLedger.State → Bool)
    (candidate : MlKemSharedSecret) (before : RegistrationNativeSecretWordMessage.State source)
    (ordinary : RegistrationNativePublicInterpreter.State n KemSK) (empty : before.server.sessions = [])
    (initialCounter : before.parsedAccepts = 0) (ownersEmpty : before.beacons = [])
    (initialPin : PqxdhRefinement.absBytes before.server.pin.binding.identity_public_key = (setup.joint.publicKeys seed).ed25519.toList) :
    Pr{let result ← (RegistrationNativeG3NativeTargetFixed.game setup checks wire source route sign serverKeyId bounds mode seed scalar
      work budget selectedTarget pairs chosen challenge candidate before ordinary)}[
      RegistrationNativeG3NativeTargetFixed.Good setup wire source serverKeyId budget selectedTarget claim result ∧
      select (result.1.1.1, result.1.1.2) = true] ≤
    Pr{let result ← (RegistrationNativeG3NativeTargetFixed.game setup checks wire source route sign serverKeyId bounds mode seed scalar
      work budget selectedTarget pairs chosen challenge candidate before ordinary)}[
      RegistrationNativeG3NativeTargetFixed.Hit setup source seed scalar candidate claim result ∧
      select (result.1.1.1, result.1.1.2) = true] := by
  rw [RegistrationNativeG3NativeTargetFixed.game, RegistrationNativeG3NativeCheckedUniformSource.fixed_source setup checks wire source route sign
    selectedTarget.2.val selectedTarget.1.val (setup.dh.publicKey scalar) serverKeyId bounds mode seed scalar
    (setup.joint.staticDh seed (setup.dh.publicKey scalar)) work before ordinary empty selectedTarget.2.val pairs chosen.1 challenge candidate]
  simp only [prEvent_map]
  have actual := bytes_probability setup checks wire route sign seed scalar pairs chosen challenge serverKeyId bounds mode work budget
    selectedTarget bounded reserved chosenAt readback responseReadback claim select before initialCounter ownersEmpty initialPin ordinary candidate
  simp only [RegistrationNativeG3NativeTargetFixed.Good, RegistrationNativeG3NativeTargetFixed.Hit,
    RegistrationNativeG3NativeCheckedAliasSource.view, Prod.map_def, id_eq,
    RegistrationNativeSecretWordCheckedTrace.state, RegistrationNativeG3NativeCheckedAliasSource.aliasClient]
  exact actual


/-- The same supported native startup installs the sampled identity in the actual root pin. -/
theorem startup_pin (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat)
    (identity : PqxdhJointIdentity.PublicIdentity) (born : RegistrationNativeHiddenStartup.Started source)
    (supported : some born ∈ support (RegistrationNativeHiddenStartup.start (n := n) setup source ensureInit identityIndex serverKeyId identity)) :
    PqxdhRefinement.absBytes born.native.frontend.server.pin.binding.identity_public_key = identity.ed25519.toList := by
  simp only [RegistrationNativeHiddenStartup.start, mem_support_bind_iff] at supported
  obtain ⟨constructed, _constructed, continued⟩ := supported
  cases built : constructed.1 with
  | none => simp only [built, mem_support_pure_iff] at continued; cases continued
  | some created =>
      simp only [built, mem_support_bind_iff] at continued
      obtain ⟨generated, _generated, continued⟩ := continued
      cases sampled : generated with
      | none => simp only [sampled, mem_support_pure_iff] at continued; cases continued
      | some credential =>
          simp only [sampled, mem_support_bind_iff] at continued
          obtain ⟨installed, _installed, returned⟩ := continued
          simp only [mem_support_pure_iff, Option.some.injEq] at returned
          cases returned
          exact PqxdhRootTableInitialization.rootArray_bytes identity.ed25519

variable (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)

/-- A same-result ledger selector survives actual effectful startup, complete-output source transport and final-ordinal provenance. -/
theorem after_probability (candidate : MlKemSharedSecret) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (select : Value × RegistrationNativeLedger.State → Bool)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (reserved : budget.create ≤ pairs.length) (chosenAt : pairs[selectedTarget.2.val]? = some chosen)
    (readback : RegistrationNativeWire.InitReadBack wire) (responseReadback : RegistrationNativeWire.ResponseReadBack wire)
    (born : RegistrationNativeHiddenStartup.Started source) (world : PqxdhRecordLiftWorld.State (budget.cap 4 + budget.cap 5))
    (supported : (some born, world) ∈ support (RegistrationNativeG3MaterializedTracedStartup.startup setup wire route source ensureInit identityIndex serverKeyId seed)) :
    Pr{let outcome ← (RegistrationNativeG3MaterializedTracedStartup.fullAfter setup checks wire route source serverKeyId seed scalar candidate
      (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selectedTarget.2.val pairs chosen.1 challenge candidate)
      none selectedTarget.2.val selectedTarget.1.val bounds mode adversary (some born, world))}[
      RegistrationNativeG3NativeTargetStartup.Good setup wire serverKeyId budget selectedTarget claim outcome ∧
        RegistrationNativeSelectedRecordTrace.outcomeSelected select outcome = true] ≤
    Pr{let outcome ← (RegistrationNativeG3MaterializedTracedStartup.fullAfter setup checks wire route source serverKeyId seed scalar candidate
      (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selectedTarget.2.val pairs chosen.1 challenge candidate)
      none selectedTarget.2.val selectedTarget.1.val bounds mode adversary (some born, world))}[
      RegistrationNativeSelectiveRecordTraceTarget.Hit setup seed scalar candidate claim outcome ∧
        RegistrationNativeSelectedRecordTrace.outcomeSelected select outcome = true] := by
  let Outcome := RegistrationNativeEntropyRun.Outcome (RegistrationNativePublicFrontend.State source × RegistrationNativeG2Trace.State) Value
  let : MeasurableSpace Outcome := ⊤
  let : DiscreteMeasurableSpace Outcome := ⟨fun _ => trivial⟩
  have sourceEq := _root_.EvalDistEq.of_evalDist_eq
    (RegistrationNativeG3MaterializedTracedEarlySource.after_source setup checks wire source route ensureInit identityIndex serverKeyId seed scalar
      selectedTarget.2.val pairs chosen.1 challenge candidate selectedTarget.1.val bounds mode adversary budget bounded born world supported).evalDist_eq
  rw [sourceEq.prEvent_eq, sourceEq.prEvent_eq]
  simp only [prEvent_map, RegistrationNativeG3NativeTargetStartup.Good, RegistrationNativeSelectiveRecordTraceTarget.Hit,
    RegistrationNativeSelectedRecordTrace.outcomeSelected, Option.elim_some]
  have cold := RegistrationNativeG3NativeStartupFields.initialized setup wire route source ensureInit identityIndex serverKeyId seed born world supported
  have openReached : some born ∈ support (RegistrationNativeHiddenStartup.start (n := budget.cap 4 + budget.cap 5)
      setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed)) := by
    apply OracleComp.support_simulateQ_run'_subset
      (CborRecordWorldSimulation.guarded setup (RegistrationNativeWire.ledgerCodec wire) route) _ PqxdhRecordLiftWorld.initial
    rw [StateT.run'_eq, support_map]
    exact ⟨(some born, world), supported, rfl⟩
  have pin := startup_pin setup serverKeyId ensureInit identityIndex (setup.joint.publicKeys seed) born openReached
  have compared := fixed_probability setup checks wire route
    (RegistrationNativeMldsa.owned source born.native.credential) seed scalar pairs chosen challenge serverKeyId bounds mode
    (adversary ⟨setup.joint.publicKeys seed, born.native.credential.publicKey, serverKeyId⟩) budget selectedTarget
    (bounded _) reserved chosenAt readback responseReadback claim select candidate
    (RegistrationNativeG3NativeStartupFields.word born.native.frontend) (RegistrationNativeG3NativeUniformAuditBound.ordinary world)
    (by simp only [RegistrationNativeG3NativeStartupFields.word, cold.1, List.map_nil]) cold.2.2.1 cold.2.1 pin
  simp only [RegistrationNativeG3NativeTargetFixed.game] at compared
  exact compared


/-- Averaging the actual startup branches retains the ledger selector on both the original good target and its selected receipt. -/
theorem startup_probability (candidate : MlKemSharedSecret) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (select : Value × RegistrationNativeLedger.State → Bool)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (reserved : budget.create ≤ pairs.length) (chosenAt : pairs[selectedTarget.2.val]? = some chosen)
    (readback : RegistrationNativeWire.InitReadBack wire) (responseReadback : RegistrationNativeWire.ResponseReadBack wire) :
    Pr{let outcome ← (RegistrationNativeG3MaterializedTracedStartup.fullGame (n := budget.cap 4 + budget.cap 5)
      setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate
      (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selectedTarget.2.val pairs chosen.1 challenge candidate)
      none selectedTarget.2.val selectedTarget.1.val bounds mode adversary)}[
      RegistrationNativeG3NativeTargetStartup.Good setup wire serverKeyId budget selectedTarget claim outcome ∧
        RegistrationNativeSelectedRecordTrace.outcomeSelected select outcome = true] ≤
    Pr{let outcome ← (RegistrationNativeG3MaterializedTracedStartup.fullGame (n := budget.cap 4 + budget.cap 5)
      setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate
      (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selectedTarget.2.val pairs chosen.1 challenge candidate)
      none selectedTarget.2.val selectedTarget.1.val bounds mode adversary)}[
      RegistrationNativeSelectiveRecordTraceTarget.Hit setup seed scalar candidate claim outcome ∧
        RegistrationNativeSelectedRecordTrace.outcomeSelected select outcome = true] := by
  unfold RegistrationNativeG3MaterializedTracedStartup.fullGame
  apply prEvent_bind_mono_of_forall_le_of_support
  intro initialized supported
  rcases initialized with ⟨_ | born, world⟩
  · simp only [RegistrationNativeG3MaterializedTracedStartup.fullAfter]
    exact le_rfl
  · exact after_probability setup checks wire route seed scalar pairs chosen challenge serverKeyId bounds mode budget selectedTarget
      ensureInit identityIndex adversary candidate claim select bounded reserved chosenAt readback responseReadback born world supported

end BeaconcryptCore.Computational.RegistrationNativeSelectedTargetSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectedTargetSource.bytes_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectedTargetSource.bytes_probability

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectedTargetSource.fixed_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectedTargetSource.fixed_probability

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectedTargetSource.startup_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectedTargetSource.startup_pin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectedTargetSource.after_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectedTargetSource.after_probability

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectedTargetSource.startup_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectedTargetSource.startup_probability
