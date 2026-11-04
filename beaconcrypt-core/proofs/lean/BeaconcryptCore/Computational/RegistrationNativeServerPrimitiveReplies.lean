-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeServerCollectorCuts

/-! The concrete Server backend exposes the actual generated scalar/public pair and its honest encapsulation support. Its classical getters and encapsulation retain the same private role state, so these receipts compose at the source collector cuts. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeServerPrimitiveReplies
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhBeaconPhase2Preparation (Word32 Ciphertext)
open PqxdhJointIdentity (IdentitySeed)
open RegistrationAgreementRoot (nativeOption)
variable {ι KemSK : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (seed : IdentitySeed)
local notation "Shared" => RawCtxSharedPrimitive.SharedState RegistrationServerRoleBackend.State
local notation "implementation" => RegistrationAgreementShared.implementation setup.source (RegistrationServerRoleBackend.native setup checks representation seed)

private theorem state_pure_apply {S A : Type} {m : Type → Type} [Monad m]
    (value : A) (before : S) : (pure value : StateT S m A) before = pure (value, before) := rfl
private theorem state_lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) : (StateT.lift work : StateT S m A) before = (fun value => (value, before)) <$> work := by
  change (work >>= fun value => pure (value, before)) = _
  exact bind_pure_comp _ _

def dhReply (before : RegistrationServerRoleBackend.State) (request : agreement.DhRequest) : core.option.Option Word32 :=
  match request.secret_role with
  | .LocalIdentity => nativeOption ((setup.joint.staticDh seed (PqxdhPhase2GapDhSource.peer request.public_key)).map PqxdhRootTableInitialization.rootArray)
  | .ServerEphemeral => nativeOption (before.ephemeral.bind fun scalar =>
      (PqxdhJointGapDh.sourceScalarDh setup.source.crypto scalar (PqxdhPhase2GapDhSource.peer request.public_key)).map PqxdhRootTableInitialization.rootArray)
  | _ => .None

/-- Source DH getters preserve their complete role/cache state and return their literal functional native value. -/
theorem dh (request : agreement.DhRequest) (before : Shared) :
    (implementation (.dh request)).run before = pure (dhReply setup seed before.1 request, before) := by
  cases role : request.secret_role <;>
    simp only [RegistrationAgreementShared.implementation, RegistrationAgreementShared.auxiliary,
      RegistrationServerRoleBackend.native, RegistrationServerRoleBackend.localBackend, role,
      StateT.run, state_pure_apply, map_pure, dhReply]

/-- The public conversion is the actual complete source conversion and changes no private scalar or cache. -/
theorem public_conversion (key : Word32) (before : Shared) :
    (implementation (.convertPublic key)).run before = pure (RegistrationPublicConversion.convert setup.source.crypto key, before) := by
  simp only [RegistrationAgreementShared.implementation, RegistrationAgreementShared.auxiliary,
    RegistrationServerRoleBackend.native, RegistrationServerRoleBackend.localBackend, StateT.run, state_pure_apply, map_pure]

/-- Native private-identity conversion uses the actual selected source seed and preserves all state. -/
theorem private_conversion (before : Shared) :
    (implementation (.convertSecret .LocalIdentity)).run before =
      pure (RegistrationServerRoleBackend.selectedConversion setup.source.crypto (setup.secretOfSeed seed), before) := by
  simp only [RegistrationAgreementShared.implementation, RegistrationAgreementShared.auxiliary,
    RegistrationServerRoleBackend.native, StateT.run, state_pure_apply, map_pure]

/-- An actual generated source ephemeral contains this exact sampled scalar, with the corresponding honest public key. -/
theorem generate (key : Word32) (before after : Shared)
    (supported : (.Some key, after) ∈ support ((implementation (.generate .ServerEphemeral)).run before)) :
    ∃ scalar ∈ support PqxdhJointGapDh.sampleScalar,
      key = PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar) ∧ after.1.ephemeral = some scalar ∧ after.2 = before.2 := by
  simp only [RegistrationAgreementShared.implementation, RegistrationAgreementShared.auxiliary,
    RegistrationServerRoleBackend.native, RegistrationServerRoleBackend.localBackend,
    PqxdhServerAuthExperiment.generateEphemeral, StateT.run, bind_pure_comp, Functor.map_map, support_map] at supported
  obtain ⟨scalar, sampled, same⟩ := supported
  have keyEq : PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar) = key :=
    Option.some.inj (congrArg Prod.fst same)
  have roleEq : some scalar = after.1.ephemeral :=
    congrArg (fun result : core.option.Option Word32 × Shared => result.2.1.ephemeral) same
  have cacheEq : before.2 = after.2 := congrArg (fun result : core.option.Option Word32 × Shared => result.2.2) same
  exact ⟨scalar, sampled, keyEq.symm, roleEq.symm, cacheEq.symm⟩

/-- The actual encapsulation getter samples the original KEM on its exact supplied public key and preserves the generated private scalar. -/
theorem encapsulate (key : Std.Array U8 1184#usize) (ciphertext : Ciphertext) (shared : Word32)
    (before after : Shared)
    (supported : (.Some (ciphertext, shared), after) ∈ support ((implementation (.encapsulate (.Some key))).run before)) :
    ∃ pair ∈ support (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps (RegistrationRootInput.pqKey key))),
      ciphertext = PqxdhAcceptedRegistration.ciphertextArray pair.1 ∧
      shared = PqxdhRootTableInitialization.rootArray pair.2 ∧ after = before := by
  simp only [RegistrationAgreementShared.implementation, RegistrationAgreementShared.auxiliary,
    RegistrationServerRoleBackend.native, RegistrationServerRoleBackend.localBackend, StateT.run] at supported
  split_ifs at supported with accepted
  · simp only [PqxdhServerAuthExperiment.encapsulate, state_lift_apply, simulateQ_map,
      Functor.map_map, support_map] at supported
    obtain ⟨pair, sampled, same⟩ := supported
    have replyEq : (PqxdhAcceptedRegistration.ciphertextArray pair.1, PqxdhRootTableInitialization.rootArray pair.2) = (ciphertext, shared) :=
      Option.some.inj (congrArg Prod.fst same)
    have stateEq : before = after := congrArg Prod.snd same
    exact ⟨pair, sampled, (congrArg Prod.fst replyEq).symm, (congrArg Prod.snd replyEq).symm, stateEq.symm⟩
  · simp only [state_pure_apply, map_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
    cases supported.1

end BeaconcryptCore.Computational.RegistrationNativeServerPrimitiveReplies

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPrimitiveReplies.dh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPrimitiveReplies.dh

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPrimitiveReplies.public_conversion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPrimitiveReplies.public_conversion

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPrimitiveReplies.private_conversion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPrimitiveReplies.private_conversion

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPrimitiveReplies.generate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPrimitiveReplies.generate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPrimitiveReplies.encapsulate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPrimitiveReplies.encapsulate
