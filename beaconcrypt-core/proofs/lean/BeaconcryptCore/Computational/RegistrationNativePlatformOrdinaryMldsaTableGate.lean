-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaTableCallback
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaRouting
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableCallback
/-! The actual runtime table callback performs its public terminal reservation after the reached private Native/table execution. Failed publication retains both private coordinates. This is a concrete callback law rather than equality between complete profiles. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaTableGate
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformOrdinaryGate (gate)
variable {n : Nat} {Native Private Platform E ι KemSK : Type} {base : OracleSpec ι}

def after (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (work : StateT ((Native × Platform) × Private) ProbComp (Option RawCtxSourceSend.Encrypted)) :
    StateT ((Native × Platform) × Private) ProbComp (Option RawCtxSourceSend.Encrypted) := fun before => do
  let result ← work.run before
  let gated ← (gate reserve (fun value : RawCtxSourceSend.Encrypted => value.ciphertext.length) result.1).run result.2.1.2
  pure (gated.1, ((result.2.1.1, gated.2), result.2.2))

def terminal {source : RegistrationNativeMldsa.Source}
    (native : QueryImpl RegistrationNativeRawAdapter.TypedSpec
      (StateT (RegistrationNativePlatformMldsaTableCallback.State (n := n) (KemSK := KemSK) (Platform := Platform) source) ProbComp))
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) :
    QueryImpl RegistrationNativeRawAdapter.TypedSpec
      (StateT (RegistrationNativePlatformMldsaTableCallback.State (n := n) (KemSK := KemSK) (Platform := Platform) source) ProbComp)
  | .inr (.serverSend keyId plaintext) => after reserve (native (.inr (.serverSend keyId plaintext)))
  | .inr (.beaconSend owner plaintext) => after reserve (native (.inr (.beaconSend owner plaintext)))
  | query => native query

/-- Exact actual table callbacks retain advanced private state before the public terminal writer decision. -/
theorem callback [primitive : AdapterSealPrimitive.Operations]
    (source : RegistrationNativeMldsa.Source) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential (RegistrationNativeMldsaOpaque.handleSource source))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    RegistrationNativePlatformOrdinaryMldsaTableCallback.callback (n := n) source setup checks wire route representation created credential
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer =
      terminal (RegistrationNativePlatformMldsaTableCallback.callback source setup checks
        (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created credential view failure allocation
        reserveRegistration reservePeer erased helper writer) reserveFrame := by
  funext query before
  unfold RegistrationNativePlatformOrdinaryMldsaTableCallback.callback
  rw [RegistrationNativePlatformOrdinaryMldsaRouting.handler]
  cases query with
  | inl coin => rfl
  | inr query => cases query with
    | serverSend keyId plaintext =>
      simp only [RegistrationNativePlatformOrdinaryMldsaRouting.terminal, terminal]
      rw [RegistrationNativePlatformOrdinaryMldsaRouting.table_after source]
      simp only [map_bind, map_pure, after, RegistrationNativePlatformMldsaTableCallback.callback,
        StateT.run, bind_map_left, RegistrationNativePlatformOrdinaryMldsaTableCallback.arrange,
        RegistrationNativePlatformMldsaTableCallback.arrange]
      rfl
    | beaconSend owner plaintext =>
      simp only [RegistrationNativePlatformOrdinaryMldsaRouting.terminal, terminal]
      rw [RegistrationNativePlatformOrdinaryMldsaRouting.table_after source]
      simp only [map_bind, map_pure, after, RegistrationNativePlatformMldsaTableCallback.callback,
        StateT.run, bind_map_left, RegistrationNativePlatformOrdinaryMldsaTableCallback.arrange,
        RegistrationNativePlatformMldsaTableCallback.arrange]
      rfl
    | _ => rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaTableGate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaTableGate.callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaTableGate.callback
