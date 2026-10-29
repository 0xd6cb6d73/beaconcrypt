-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3NativeTargetFixed
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedEarlySource
import BeaconcryptCore.Computational.RegistrationNativeSelectiveRecordTraceTarget

/-! The fixed-candidate original good target supplies its final selected installation receipt in the actual complete known108 cold startup game. All cold roster, parser, session, Server pin and reached cache facts are derived from that same effectful startup. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3NativeTargetStartup
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (FreshBounds Mode Budget)
open PqxdhKemIndCca
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

private theorem start_pin (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
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
          obtain ⟨installed, _installed, digest, _hashed, returned⟩ := continued
          simp only [mem_support_pure_iff, Option.some.injEq] at returned
          cases returned
          exact PqxdhRootTableInitialization.rootArray_bytes identity.ed25519

def Good (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : Budget) (target : Fin budget.accept × Fin budget.capacity) (claim : Value → Option (Nat × Pqxdh.Bytes))
    {source : RegistrationNativeMldsa.Source}
    (outcome : RegistrationNativeEntropyRun.Outcome (RegistrationNativePublicFrontend.State source × RegistrationNativeG2Trace.State) Value) : Prop :=
  match outcome with
  | none => False
  | some finished => RegistrationNativePrekeyEvents.GoodAt setup.source.crypto wire serverKeyId budget target claim
      (finished.2.1.1, (finished.2.1.2, ()))

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (source : RegistrationNativeMldsa.Source) (route : RawCtxServerRouting.SenderDecoder)
  (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
  (bounds : FreshBounds) (mode : Mode)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
  (budget : Budget) (selectedTarget : Fin budget.accept × Fin budget.capacity)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (pairs : List (MlKem768PublicKey × KemSK)) (chosen : MlKem768PublicKey × KemSK) (challenge : MlKem768Ciphertext)
  (candidate : MlKemSharedSecret) (claim : Value → Option (Nat × Pqxdh.Bytes))
local notation "provider" => RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selectedTarget.2.val pairs chosen.1 challenge candidate
local notation "fullAfter" => RegistrationNativeG3MaterializedTracedStartup.fullAfter setup checks wire route source serverKeyId seed scalar candidate
  provider none selectedTarget.2.val selectedTarget.1.val bounds mode adversary
local notation "fullGame" => RegistrationNativeG3MaterializedTracedStartup.fullGame (n := budget.cap 4 + budget.cap 5)
  setup checks wire route source ensureInit identityIndex serverKeyId seed scalar candidate provider none selectedTarget.2.val selectedTarget.1.val bounds mode adversary

/-- Every same supported actual startup branch derives the original good target's final selected installation ordinal. -/
theorem after_probability (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (reserved : budget.create ≤ pairs.length) (chosenAt : pairs[selectedTarget.2.val]? = some chosen)
    (readback : RegistrationNativeWire.InitReadBack wire) (responseReadback : RegistrationNativeWire.ResponseReadBack wire)
    (born : RegistrationNativeHiddenStartup.Started source) (world : PqxdhRecordLiftWorld.State (budget.cap 4 + budget.cap 5))
    (supported : (some born, world) ∈ support (RegistrationNativeG3MaterializedTracedStartup.startup setup wire route source ensureInit identityIndex serverKeyId seed)) :
    Pr{let outcome ← fullAfter (some born, world)}[Good setup wire serverKeyId budget selectedTarget claim outcome] ≤
      Pr{let outcome ← fullAfter (some born, world)}[RegistrationNativeSelectiveRecordTraceTarget.Hit setup seed scalar candidate claim outcome] := by
  let Outcome := RegistrationNativeEntropyRun.Outcome (RegistrationNativePublicFrontend.State source × RegistrationNativeG2Trace.State) Value
  let : MeasurableSpace Outcome := ⊤
  let : DiscreteMeasurableSpace Outcome := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have sourceEq := _root_.EvalDistEq.of_evalDist_eq
    (RegistrationNativeG3MaterializedTracedEarlySource.after_source setup checks wire source route ensureInit identityIndex serverKeyId seed scalar
      selectedTarget.2.val pairs chosen.1 challenge candidate selectedTarget.1.val bounds mode adversary budget bounded born world supported).evalDist_eq
  rw [sourceEq.prEvent_eq, sourceEq.prEvent_eq]
  simp only [prEvent_map, Good, RegistrationNativeSelectiveRecordTraceTarget.Hit]
  have cold := RegistrationNativeG3NativeStartupFields.initialized setup wire route source ensureInit identityIndex serverKeyId seed born world supported
  have openReached : some born ∈ support (RegistrationNativeHiddenStartup.start (n := budget.cap 4 + budget.cap 5)
      setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed)) := by
    apply OracleComp.support_simulateQ_run'_subset
      (CborRecordWorldSimulation.guarded setup (RegistrationNativeWire.ledgerCodec wire) route) _ PqxdhRecordLiftWorld.initial
    rw [StateT.run'_eq, support_map]
    exact ⟨(some born, world), supported, rfl⟩
  have pin := start_pin setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed) born openReached
  have compared := RegistrationNativeG3NativeTargetFixed.probability setup checks wire source route
    (RegistrationNativeMldsa.owned source born.native.credential) serverKeyId bounds mode seed scalar
    (adversary ⟨setup.joint.publicKeys seed, born.native.credential.publicKey, serverKeyId⟩) budget selectedTarget pairs chosen challenge candidate
    (RegistrationNativeG3NativeStartupFields.word born.native.frontend) (RegistrationNativeG3NativeUniformAuditBound.ordinary world)
    (bounded _) reserved chosenAt readback responseReadback claim
    (by simp only [RegistrationNativeG3NativeStartupFields.word, cold.1, List.map_nil]) cold.2.2.1 cold.2.1 pin
  simp only [RegistrationNativeG3NativeTargetFixed.game] at compared
  convert compared using 1 <;> rfl

/-- Actual complete cold startup discharges every source fact needed for the original good target's selected final receipt. -/
theorem probability (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (reserved : budget.create ≤ pairs.length) (chosenAt : pairs[selectedTarget.2.val]? = some chosen)
    (readback : RegistrationNativeWire.InitReadBack wire) (responseReadback : RegistrationNativeWire.ResponseReadBack wire) :
    Pr{let outcome ← fullGame}[Good setup wire serverKeyId budget selectedTarget claim outcome] ≤
      Pr{let outcome ← fullGame}[RegistrationNativeSelectiveRecordTraceTarget.Hit setup seed scalar candidate claim outcome] := by
  unfold RegistrationNativeG3MaterializedTracedStartup.fullGame
  apply prEvent_bind_mono_of_forall_le_of_support
  intro initialized supported
  rcases initialized with ⟨_ | born, world⟩
  · simp only [RegistrationNativeG3MaterializedTracedStartup.fullAfter, ]
    exact le_rfl
  · exact after_probability setup checks wire source route ensureInit identityIndex serverKeyId bounds mode adversary budget selectedTarget
      seed scalar pairs chosen challenge candidate claim bounded reserved chosenAt readback responseReadback born world supported

end BeaconcryptCore.Computational.RegistrationNativeG3NativeTargetStartup
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeTargetStartup.after_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeTargetStartup.after_probability
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeTargetStartup.probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeTargetStartup.probability
