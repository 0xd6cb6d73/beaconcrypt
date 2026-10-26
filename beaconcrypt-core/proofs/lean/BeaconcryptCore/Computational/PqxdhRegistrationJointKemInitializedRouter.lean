-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemCosts

/-! Complete actual initialized selected-KEM prechallenge simulator: constructor and unselected key generators are local, the chosen key is public-only, and every source command retains its native/owner result and interpreter histories. This is the source scheduling simulator consumed by the later selected-accept challenge cut, not that challenge reduction by itself. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemInitializedRouter
open PqxdhKemIndCca PqxdhPrivateKemSource PqxdhJointIdentity PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhRegistrationJointKemCommands (SourceSpec Budget Outcome program)
open PqxdhRegistrationJointServerBirth (ClientCreated)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A Result : Type}

abbrev Output (KemSK A Result : Type) :=
  Option (ClientCreated Unit × Outcome KemSK Result) × PqxdhDynamicKemJointSource.State KemSK × A

/-- The complete executable wrapper has only the challenger public key. It begins with empty private pools, runs actual generated/imported initialization, samples all unselected pairs locally and preserves the complete adaptive command continuation. -/
noncomputable def pre (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (client : OracleComp (SourceSpec KemSK) Result) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (target : MlKem768PublicKey) :
    OracleComp (MlKemCCAOracleSpec baseSpec) (Output KemSK A Result) := do
  let born ← ccaCoins ((simulateQ (PqxdhRegistrationJointServerBirth.impl setup ensureInit)
    (PqxdhRegistrationJointServerBirth.client setup.serverKeyId supplied)).run
      ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))
  match born.1 with
  | none => pure (none, (born.2.1.1, PqxdhDynamicKemRouter.empty), born.2.2)
  | some created => do
    let others ← ccaCoins (PqxdhLiveKemSelection.sampleFamily
      (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen) count)
    (fun result => (result.1.map (fun answer => (created, answer)), result.2, born.2.2)) <$>
      PqxdhRegistrationJointKemRouting.pre setup codec checks created.server.server.metadata.identityIndex
        created.publicIdentity client [] (PqxdhRegistrationJointInitializedAccept.initial created) selected.val
        (PqxdhDynamicKemRouter.selectedReservation selected target others) (born.2.1.1, PqxdhDynamicKemRouter.empty)

/-- Mathematical source interpretation of the same initializer, local reservation and complete command schedule, stopped only at the selected-secret disclosure. The chosen secret occurs only here and in the CCA interpreter. -/
noncomputable def stopped (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (client : OracleComp (SourceSpec KemSK) Result) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (chosen : MlKem768PublicKey × KemSK) :
    ProbComp (Output KemSK A Result) := do
  let born ← (simulateQ (PqxdhRegistrationJointServerBirth.impl setup ensureInit)
    (PqxdhRegistrationJointServerBirth.client setup.serverKeyId supplied)).run
      ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)
  match born.1 with
  | none => pure (none, (born.2.1.1, PqxdhDynamicKemRouter.empty), born.2.2)
  | some created => do
    let others ← PqxdhLiveKemSelection.sampleFamily
      (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen) count
    (fun result => (result.1.map (fun answer => (created, answer)), result.2, born.2.2)) <$>
      (((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected.val
        (List.ofFn (selected.insertNth chosen others)))
        (program setup codec checks created.server.server.metadata.identityIndex created.publicIdentity client []
          (PqxdhRegistrationJointInitializedAccept.initial created))).run).run
            (born.2.1.1, PqxdhDynamicKemRouter.empty))

/-- Complete initialized CCA interpretation equality, with exact generation order, origin, runtime, native state and both private histories. No chosen secret is an executable simulator input. -/
theorem source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (client : OracleComp (SourceSpec KemSK) Result) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (chosen : MlKem768PublicKey × KemSK) :
    evalKem setup.baseImpl setup.kem chosen.2 (pre setup codec checks ensureInit supplied client runtime count selected chosen.1) =
      stopped setup codec checks ensureInit supplied client runtime count selected chosen := by
  simp only [pre, stopped, evalKem, simulateQ_bind]
  rw [show simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
    (simulateQ (PqxdhStatefulPhase1EufCma.localKemPreChallengeImpl setup.kem chosen.2)
      (ccaCoins ((simulateQ (PqxdhRegistrationJointServerBirth.impl setup ensureInit)
        (PqxdhRegistrationJointServerBirth.client setup.serverKeyId supplied)).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)))) = _ from
    evalKem_coins setup.baseImpl setup.kem chosen.2 _]
  apply bind_congr
  rintro ⟨(_ | created), after⟩
  · rfl
  · simp only [simulateQ_bind]
    rw [show simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
      (simulateQ (PqxdhStatefulPhase1EufCma.localKemPreChallengeImpl setup.kem chosen.2)
        (ccaCoins (PqxdhLiveKemSelection.sampleFamily
          (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen) count))) = _ from
      evalKem_coins setup.baseImpl setup.kem chosen.2 _]
    apply bind_congr
    intro others
    simp only [simulateQ_map]
    have same := PqxdhRegistrationJointKemRouting.pre_source setup codec checks
      created.server.server.metadata.identityIndex created.publicIdentity client []
      (PqxdhRegistrationJointInitializedAccept.initial created) selected.val
      (List.ofFn (selected.insertNth chosen others)) chosen.1 chosen.2
      (by simpa only [List.nil_append, List.length_nil, Nat.zero_add, Prod.mk.eta] using PqxdhLiveKemSelection.selected_index [] selected chosen others)
      (after.1.1, PqxdhDynamicKemRouter.empty)
    rw [PqxdhDynamicKemRouter.selected_reservation] at same
    exact congrArg (fun work => (fun result => (result.1.map (fun answer => (created, answer)), result.2, after.2)) <$> work) same

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemInitializedRouter

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemInitializedRouter.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemInitializedRouter.source
