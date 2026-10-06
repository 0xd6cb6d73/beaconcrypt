-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut

/-! The ordinary selected-key KEM prechallenge at the raw-accept ordinal. The prephase is `KemChallenge.pre` with its scanned program replaced by the KEM scan at occurrence zero of `AcceptKemCut.exposeAt`, in which only the encapsulation of the raw accept at the designated raw-accept ordinal is exposed. The constructor, the failed branch, the local reservations and the selected-first router are those of `KemChallenge.pre`; the saved context type, and therefore every postchallenge definition of `KemResume`, is unchanged. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawChallenge
open PqxdhKemIndCca PqxdhPrivateKemSource PqxdhJointIdentity PqxdhServerAuthExperiment
open PqxdhRegistrationJointKemCommands (SourceSpec)
open PqxdhRegistrationJointKemChallenge (Context)
open PqxdhRegistrationJointServerBirth (ClientCreated)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- The KEM scan at occurrence zero of the initialized source command program on the Boolean client `decisionClient decision work index`, with only the encapsulation of the raw accept at ordinal `index` exposed. -/
noncomputable def rawScan (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (index : Nat) (created : ClientCreated Unit) :=
  PqxdhRegistrationJointKemCut.scan setup
    (PqxdhRegistrationJointAcceptKemCut.exposeAt setup codec checks created.server.server.metadata.identityIndex
      created.publicIdentity (PqxdhRegistrationJointAcceptCutTag.decideTag decision) work index []
      (PqxdhRegistrationJointInitializedAccept.initial created)) 0

/-- The executable prephase at the raw-accept ordinal: actual initialization, all local reservations and the source command prefix up to the encapsulation of the selected raw accept. Every constructor branch, including failure, is handled exactly as in `KemChallenge.pre`. -/
noncomputable def preRaw (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (target : MlKem768PublicKey) :
    OracleComp (MlKemCCAOracleSpec baseSpec) (Context KemSK A Bool count) := do
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
      (rawScan setup codec checks decision work index created)).run).run
        (born.2.1.1, PqxdhDynamicKemRouter.empty))
    pure (.ready created others result.1 result.2 born.2.2)

/-- Mathematical stopped-source interpretation of the same initializer and raw-ordinal cut. Only this source interpreter receives the chosen key pair. -/
noncomputable def sourcePreRaw (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (chosen : MlKem768PublicKey × KemSK) :
    ProbComp (Context KemSK A Bool count) := do
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
      (rawScan setup codec checks decision work index created)).run).run
        (born.2.1.1, PqxdhDynamicKemRouter.empty))
    pure (.ready created others result.1 result.2 born.2.2)

/-- The executable raw-ordinal prephase under the ordinary prechallenge interpretation equals the stopped-source prephase, with every constructor/callback effect and reached history retained. -/
theorem preRaw_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (chosen : MlKem768PublicKey × KemSK) :
    evalKem setup.baseImpl setup.kem chosen.2
      (preRaw setup codec checks ensureInit supplied decision work runtime count selected index chosen.1) =
      sourcePreRaw setup codec checks ensureInit supplied decision work runtime count selected index chosen := by
  simp only [preRaw, sourcePreRaw, evalKem, simulateQ_bind]
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
      (rawScan setup codec checks decision work index created)
      (after.1.1, PqxdhDynamicKemRouter.empty)
    rw [PqxdhDynamicKemRouter.selected_reservation] at same
    simpa only [evalKem, simulateQ_pure, bind_pure_comp] using congrArg
      (fun work => (fun result => Context.ready created others result.1 result.2 after.2) <$> work) same

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawChallenge

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawChallenge.preRaw_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawChallenge.preRaw_source
