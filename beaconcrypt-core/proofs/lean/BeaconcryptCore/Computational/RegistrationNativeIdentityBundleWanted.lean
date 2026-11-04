-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTuplePublication
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxOneTimeMessageHistory
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSampleHistory
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityBundleWanted
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformIdentityCtxMain (Full interpret)
open RegistrationNativePlatformIdentityCtxSigningHistoryFrame (messages)
variable {A B : Type}
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
local notation "Main" => RegistrationNativePlatformIdentityCtxMain.beacon (n := n) (Platform := Platform) (source := source) setup checks representation created

/-- An actual successful bundle with a first one-time history crossing publishes that exact unsigned tuple, using one and the same captured scalar. -/
theorem bundle_vec (index : Nat) (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (before after : Full n KemSK Platform source) (bytes : alloc.vec.Vec U8)
    (supported : (.ok (some bytes),after) ∈ support ((interpret setup.joint
      (Main (RegistrationNativePlatformIdentityBundleRun.bundle setup index (RegistrationNativePlatformConcreteSource.writer reserve)))).run before))
    (identity : Nat) (wanted : Pqxdh.Bytes) (fresh : wanted ∉ messages identity before.2)
    (signed : wanted ∈ messages identity after.2)
    (oneTime : RegistrationNativeIdentitySigningRole.oneTime wanted=true) :
    ∃ owner scalar, before.1.1.beacons[index]?=some owner ∧ owner.identity.handle=identity ∧
      wanted=PqxdhEd25519EufCma.oneTimeMessage (setup.dh.publicKey scalar) ∧
      (PqxdhDeploymentTranscript.candidateOf (RegistrationNativeWire.ledgerCodec RegistrationNativePlatformConcreteSource.wire)
        (TranscriptAuthParts.absSlice bytes)).bind PqxdhDeploymentPublishedTuple.candidateTuple=
          some ⟨PqxdhPhase2InputBytes.word owner.prekeyPublic,setup.dh.publicKey scalar,owner.kemPublic⟩ := by
  rcases RegistrationNativePlatformIdentityCtxBundleDispatch.cut setup checks representation created index
    (RegistrationNativePlatformConcreteSource.writer reserve) before (.ok (some bytes),after) supported with rejected | captured
  · cases rejected
  · obtain ⟨owner,scalar,middle,found,picked,called⟩ := captured
    have freshAt : wanted ∉ messages identity middle.2 := by
      rcases picked with ⟨_phase,sampled⟩ | ⟨_phase,rfl⟩
      · have same := RegistrationNativePlatformIdentityCtxSampleHistory.history setup checks representation created
          PqxdhJointGapDh.sampleScalar before (scalar,middle) sampled identity
        exact fun old=>fresh (same ▸ old)
      · exact fresh
    obtain ⟨started,built,tagged⟩ := RegistrationNativeIdentitySigningRole.initial
      ⟨owner.pin.binding⟩ (RegistrationNativeIdentityFrontend.inputs owner)
      ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)⟩
    have message := RegistrationNativePlatformIdentityCtxOneTimeMessageHistory.bundled setup checks representation created
      index owner scalar (RegistrationNativePlatformConcreteSource.writer reserve) started built tagged middle (.ok (some bytes),after)
      called identity wanted freshAt signed oneTime
    have handle := RegistrationNativePlatformIdentityCtxSigningHistoryFrame.owner setup checks representation created index owner scalar
      (RegistrationNativePlatformConcreteSource.writer reserve) middle (.ok (some bytes),after) called identity wanted freshAt signed
    obtain ⟨tuple,operand⟩ := RegistrationNativePlatformIdentityCtxTuplePublication.bundled_started setup checks representation created
      index owner scalar reserve started built middle after bytes called
    exact ⟨owner,scalar,found,handle,message.trans operand,tuple⟩
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : X → Y) (work : StateT S m X) (before : S) :
    (change <$> work) before=Prod.map change id <$> work before := StateT.run_map change work before

private theorem interpret_map (joint : PqxdhJointIdentity.Primitives) (change : A → B)
    (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform source A) :
    interpret joint (change <$> work)=change <$> interpret joint work := by
  funext before
  simp only [RegistrationNativePlatformIdentityCtxMain.interpret,StateT.run,map_apply,simulateQ_map,Functor.map_map]
  rfl

/-- The public byte reply and its first successful signing history use the same captured unsigned tuple. -/
theorem bundle (index : Nat) (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (before after : Full n KemSK Platform source) (bytes : Pqxdh.Bytes)
    (supported : (.ok (some bytes),after) ∈ support ((interpret setup.joint
      (RegistrationNativePlatformIdentityCtxLifecycle.bundle setup checks representation created
        (RegistrationNativePlatformConcreteSource.writer reserve) index)).run before))
    (identity : Nat) (wanted : Pqxdh.Bytes) (fresh : wanted ∉ messages identity before.2)
    (signed : wanted ∈ messages identity after.2)
    (oneTime : RegistrationNativeIdentitySigningRole.oneTime wanted=true) :
    ∃ owner scalar, before.1.1.beacons[index]?=some owner ∧ owner.identity.handle=identity ∧
      wanted=PqxdhEd25519EufCma.oneTimeMessage (setup.dh.publicKey scalar) ∧
      (PqxdhDeploymentTranscript.candidateOf (RegistrationNativeWire.ledgerCodec RegistrationNativePlatformConcreteSource.wire)
        bytes).bind PqxdhDeploymentPublishedTuple.candidateTuple=
          some ⟨PqxdhPhase2InputBytes.word owner.prekeyPublic,setup.dh.publicKey scalar,owner.kemPublic⟩ := by
  rw [RegistrationNativePlatformIdentityCtxLifecycle.bundle,interpret_map,StateT.run_map,support_map] at supported
  obtain ⟨⟨raw,finished⟩,called,same⟩ := supported
  have afterEq : finished=after := congrArg Prod.snd same
  subst finished
  have replied := congrArg Prod.fst same
  cases raw with
  | fail error | div => cases replied
  | ok optional => cases optional with
    | none => cases replied
    | some encoded =>
        have bytesEq : TranscriptAuthParts.absSlice encoded=bytes := Option.some.inj (RustM.ok.inj replied)
        rw [←bytesEq]
        exact bundle_vec setup checks representation created index reserve before after encoded called identity wanted fresh signed oneTime

end BeaconcryptCore.Computational.RegistrationNativeIdentityBundleWanted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBundleWanted.bundle_vec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBundleWanted.bundle_vec
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBundleWanted.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBundleWanted.bundle
