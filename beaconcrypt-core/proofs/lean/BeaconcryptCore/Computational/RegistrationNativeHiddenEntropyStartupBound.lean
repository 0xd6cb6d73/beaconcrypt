-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenEntropyStartup

/-! The fresh-byte theorem averages the actual effectful native startup. Successful branches obtain their joint allocation invariant from that reached constructor execution and continue with the same CTX/private cache. Failed startup has no fresh event. No caller-supplied invariant, startup simulation or pure Environment.start abstraction is used. -/
open OracleComp OracleSpec CoreModels ENNReal Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenEntropyStartupBound
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeHiddenInterpreter (Provider)
open PqxdhRecordLiftIdeal (CtxPrivate ctxInterpreter)
open RegistrationNativeHiddenEntropyStartup (run after run_start)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

/-- The complete actual native mode-P program has byte-accurate fresh entropy after its actual effectful initialization and ML pin hash. -/
theorem fresh_bytes (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (providerState : ProviderState)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (secret : CtxPrivate n) :
    𝒟[RegistrationNativeEntropyFresh.event claim <$>
      run (n := n) (fun _ => .random) id setup checks wire route source ensureInit identityIndex serverKeyId seed scalar provider providerState
        selectedOwner selectedAccept bounds .P adversary secret] {true} ≤ ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ := by
  rw [run_start, map_bind, ← prEvent_eq_evalDist_singleton _ true]
  apply prEvent_bind_le_of_forall_le_of_support
  intro started supported
  rcases started with ⟨⟨⟨initialized, shell⟩, control⟩, reached⟩
  cases initialized with
  | none => simp [after, RegistrationNativeEntropyFresh.event, RegistrationNativeEntropyFresh.FreshHit]
  | some born =>
      dsimp only [after]
      rw [prEvent_eq_evalDist_singleton]
      have valid := RegistrationNativeHiddenAllocationStartup.initialized setup ensureInit identityIndex serverKeyId
        (setup.joint.publicKeys seed) providerState
        (ctxInterpreter (fun _ => .random) id setup (RegistrationNativeWire.ledgerCodec wire))
        (RegistrationNativeWire.ledgerCodec wire) route secret born shell control reached supported
      exact RegistrationNativeHiddenEntropyRun.fresh_bytes setup checks wire route source born.native.credential seed scalar provider
        selectedOwner selectedAccept serverKeyId bounds
        (adversary ⟨setup.joint.publicKeys seed, born.native.credential.publicKey, serverKeyId⟩) claim born.created
        (born.native.frontend, RegistrationNativeHiddenInterpreter.initial providerState) shell control reached valid

/-- The literal cold native experiment inherits the same byte bound with no startup or allocation premise. -/
theorem initial_fresh_bytes (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (providerState : ProviderState)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) :
    𝒟[RegistrationNativeEntropyFresh.event claim <$>
      run (n := n) (fun _ => .random) id setup checks wire route source ensureInit identityIndex serverKeyId seed scalar provider providerState
        selectedOwner selectedAccept bounds .P adversary CtxPrivate.initial] {true} ≤ ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ :=
  fresh_bytes setup checks wire route source ensureInit identityIndex serverKeyId seed scalar provider providerState
    selectedOwner selectedAccept bounds adversary claim CtxPrivate.initial

end BeaconcryptCore.Computational.RegistrationNativeHiddenEntropyStartupBound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenEntropyStartupBound.fresh_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenEntropyStartupBound.fresh_bytes
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenEntropyStartupBound.initial_fresh_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenEntropyStartupBound.initial_fresh_bytes
