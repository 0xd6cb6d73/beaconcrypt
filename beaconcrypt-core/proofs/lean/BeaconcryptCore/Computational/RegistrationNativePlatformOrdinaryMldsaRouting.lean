-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaProfile
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperimentRouting
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableProgram
/-! The final runtime ML program adds only the derived public terminal publication gates to its established-record callbacks. The gate retains the complete private Native state and true-count ML table; its input is the public complete frame length. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaRouting
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformMldsaProgram (M)
open RegistrationNativePlatformOrdinaryGate (gate)
variable {n : Nat} {E Platform Native Value Next ι KemSK : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

private theorem lift_bind (work : StateT Native (StateT Platform ProbComp) Value)
    (next : Value → StateT Native (StateT Platform ProbComp) Next) :
    RegistrationNativePlatformMldsaProgram.lift (source := source) (work >>= next) = (RegistrationNativePlatformMldsaProgram.lift work >>= fun value => RegistrationNativePlatformMldsaProgram.lift (next value)) := by
  funext before previous
  simp only [RegistrationNativePlatformMldsaProgram.lift, RegistrationNativeMldsaProgram.liftState, RegistrationNativeMldsaProgram.lift,
    StateT.run_bind, simulateQ_bind]
  rfl

def after (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (work : StateT Native (M source Platform) (Option RawCtxSourceSend.Encrypted)) :
    StateT Native (M source Platform) (Option RawCtxSourceSend.Encrypted) := do
  let output ← work
  RegistrationNativePlatformMldsaProgram.lift (StateT.lift (gate reserve (fun value : RawCtxSourceSend.Encrypted => value.ciphertext.length) output))

private theorem lift_after (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (work : StateT (RegistrationNativeExperiment.State n KemSK source) (StateT Platform ProbComp) (Option RawCtxSourceSend.Encrypted)) :
    RegistrationNativePlatformMldsaProgram.lift (source := source) (RegistrationNativePlatformOrdinaryExperimentRouting.after reserve work) = after reserve (RegistrationNativePlatformMldsaProgram.lift work) := by
  unfold RegistrationNativePlatformOrdinaryExperimentRouting.after after
  exact lift_bind work _

def terminal (native : QueryImpl RegistrationNativeRawAdapter.TypedSpec
    (StateT (RegistrationNativeExperiment.State n KemSK source) (M source Platform)))
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) :
    QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT (RegistrationNativeExperiment.State n KemSK source) (M source Platform))
  | .inr (.serverSend keyId plaintext) => after reserve (native (.inr (.serverSend keyId plaintext)))
  | .inr (.beaconSend owner plaintext) => after reserve (native (.inr (.beaconSend owner plaintext)))
  | query => native query

/-- Exact free ML programs differ only by the actual public terminal writer gates on successful sends. -/
theorem handler [primitive : AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    RegistrationNativePlatformOrdinaryMldsaProfile.handler (n := n) setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer =
      terminal (RegistrationNativePlatformMldsaProfile.handler setup checks
        (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created credential view failure allocation
          reserveRegistration reservePeer erased helper writer) reserveFrame := by
  funext query
  cases query with
  | inl coin => rfl
  | inr query => cases query with
    | serverSend keyId plaintext =>
      change RegistrationNativePlatformMldsaProgram.lift _ = after reserveFrame (RegistrationNativePlatformMldsaProgram.lift _)
      rw [RegistrationNativePlatformOrdinaryExperimentRouting.server_send]
      exact lift_after reserveFrame _
    | beaconSend owner plaintext =>
      change RegistrationNativePlatformMldsaProgram.lift _ = after reserveFrame (RegistrationNativePlatformMldsaProgram.lift _)
      rw [RegistrationNativePlatformOrdinaryExperimentRouting.beacon_send]
      exact lift_after reserveFrame _
    | serverRaw raw =>
      exact congrArg (RegistrationNativePlatformMldsaProgram.lift (source := source))
        (RegistrationNativePlatformOrdinaryExperimentRouting.server_raw setup wire reserveFrame route raw)
    | beaconRaw owner raw =>
      exact congrArg (RegistrationNativePlatformMldsaProgram.lift (source := source))
        (RegistrationNativePlatformOrdinaryExperimentRouting.beacon_raw setup wire reserveFrame route owner raw)
    | _ => rfl

/-- Public reservation retains the literal private table, optional failure and complete reached Native state. -/
theorem table_after (real : RegistrationNativeMldsa.Source)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (work : StateT Native (M (RegistrationNativeMldsaOpaque.handleSource real) Platform) (Option RawCtxSourceSend.Encrypted))
    (before : Native) (previous : Platform) (pool : RegistrationNativeMldsaOpaque.Pool real) :
    RegistrationNativePlatformMldsaTableProgram.runState real (after reserve work) before previous pool = (do
      let result ← RegistrationNativePlatformMldsaTableProgram.runState real work before previous pool
      let gated ← (gate reserve (fun value : RawCtxSourceSend.Encrypted => value.ciphertext.length) result.1.1.1).run result.1.2
      pure (((gated.1, result.1.1.2), gated.2), result.2)) := by
  unfold after
  rw [RegistrationNativePlatformMldsaTableProgram.run_bind]
  apply bind_congr
  intro result
  rw [RegistrationNativePlatformMldsaTableProgram.run_lift]
  simp only [StateT.run_lift, bind_pure_comp]
  simp only [StateT.run_map, Functor.map_map]

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaRouting

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaRouting.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaRouting.handler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaRouting.table_after' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaRouting.table_after
