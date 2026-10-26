-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemCut

/-! The actual initialized source encapsulation cut is the prechallenge continuation of the ordinary selected-key KEM game. The executable prephase receives only the target public key and retains every local key, source continuation and private service history needed by its postphase. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemChallenge
open PqxdhKemIndCca PqxdhPrivateKemSource PqxdhJointIdentity PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhRegistrationJointKemCommands (SourceSpec Outcome)
open PqxdhRegistrationJointServerBirth (ClientCreated)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A Result : Type}

/-- Private reduction context records the complete failed initializer, or the actual ready Server, unselected local pairs, literal source cut and reached histories. It never stores the selected secret. -/
inductive Context (KemSK A Result : Type) (count : Nat) where
  | failed (state : PqxdhRegistrationJointServerPrefix.State KemSK A)
  | ready (created : ClientCreated Unit) (others : Fin count → MlKem768PublicKey × KemSK)
      (cut : Option (PqxdhRegistrationJointKemCut.Cut KemSK (Outcome KemSK Result)))
      (state : PqxdhDynamicKemJointSource.State KemSK) (runtime : A)

/-- The prephase runs actual initialization, all local reservations and the source command prefix up to the requested original encapsulation occurrence. A reveal stop or early completion remains in the saved result. -/
noncomputable def pre (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (client : OracleComp (SourceSpec KemSK) Result) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (occurrence : Nat) (target : MlKem768PublicKey) :
    OracleComp (MlKemCCAOracleSpec baseSpec) (Context KemSK A Result count) := do
  let born ← ccaCoins ((simulateQ (PqxdhRegistrationJointServerBirth.impl setup ensureInit)
    (PqxdhRegistrationJointServerBirth.client setup.serverKeyId supplied)).run
      ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))
  match born.1 with
  | none => pure (.failed born.2)
  | some created => do
    let others ← ccaCoins (PqxdhLiveKemSelection.sampleFamily
      (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen) count)
    let result ← (((simulateQ (PqxdhDynamicKemJointRouter.pre setup.joint setup.kem selected.val
      (PqxdhDynamicKemRouter.selectedReservation selected target others))
      (PqxdhRegistrationJointKemCut.scan setup
        (PqxdhRegistrationJointKemEncapsulation.commands setup codec checks
          created.server.server.metadata.identityIndex created.publicIdentity client []
          (PqxdhRegistrationJointInitializedAccept.initial created)) occurrence)).run).run
            (born.2.1.1, PqxdhDynamicKemRouter.empty))
    pure (.ready created others result.1 result.2 born.2.2)

/-- Mathematical stopped-source interpretation of the same actual initializer and literal encapsulation cut. Only this source interpreter receives the chosen key pair. -/
noncomputable def sourcePre (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (client : OracleComp (SourceSpec KemSK) Result) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (occurrence : Nat) (chosen : MlKem768PublicKey × KemSK) :
    ProbComp (Context KemSK A Result count) := do
  let born ← (simulateQ (PqxdhRegistrationJointServerBirth.impl setup ensureInit)
    (PqxdhRegistrationJointServerBirth.client setup.serverKeyId supplied)).run
      ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)
  match born.1 with
  | none => pure (.failed born.2)
  | some created => do
    let others ← PqxdhLiveKemSelection.sampleFamily
      (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen) count
    let result ← (((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected.val
      (List.ofFn (selected.insertNth chosen others)))
      (PqxdhRegistrationJointKemCut.scan setup
        (PqxdhRegistrationJointKemEncapsulation.commands setup codec checks
          created.server.server.metadata.identityIndex created.publicIdentity client []
          (PqxdhRegistrationJointInitializedAccept.initial created)) occurrence)).run).run
            (born.2.1.1, PqxdhDynamicKemRouter.empty))
    pure (.ready created others result.1 result.2 born.2.2)

/-- The complete executable source cut equals the original stopped cut under ordinary prechallenge interpretation, with every constructor/callback effect and reached history retained. -/
theorem pre_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (client : OracleComp (SourceSpec KemSK) Result) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (occurrence : Nat) (chosen : MlKem768PublicKey × KemSK) :
    evalKem setup.baseImpl setup.kem chosen.2
      (pre setup codec checks ensureInit supplied client runtime count selected occurrence chosen.1) =
      sourcePre setup codec checks ensureInit supplied client runtime count selected occurrence chosen := by
  simp only [pre, sourcePre, evalKem, simulateQ_bind]
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
    have same := PqxdhDynamicKemJointRouter.pre_program setup.baseImpl setup.joint setup.kem selected.val
      (List.ofFn (selected.insertNth chosen others)) chosen.1 chosen.2
      (by simpa only [List.nil_append, List.length_nil, Nat.zero_add, Prod.mk.eta] using
        PqxdhLiveKemSelection.selected_index [] selected chosen others)
      (PqxdhRegistrationJointKemCut.scan setup
        (PqxdhRegistrationJointKemEncapsulation.commands setup codec checks
          created.server.server.metadata.identityIndex created.publicIdentity client []
          (PqxdhRegistrationJointInitializedAccept.initial created)) occurrence)
      (after.1.1, PqxdhDynamicKemRouter.empty)
    rw [PqxdhDynamicKemRouter.selected_reservation] at same
    simpa only [evalKem, simulateQ_pure, bind_pure_comp] using congrArg
      (fun work => (fun result => Context.ready created others result.1 result.2 after.2) <$> work) same

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemChallenge

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemChallenge.pre_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemChallenge.pre_source
