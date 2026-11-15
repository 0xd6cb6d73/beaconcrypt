-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBundleFieldSupport
import BeaconcryptCore.Computational.RegistrationNativePlatformNativeInitEncoder
/-! Actual successful native Init publication returns the captured owner's literal identity and fixed prekey bytes. The concrete source serializer is retained, and joint native/platform packing keeps every failure and poststate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformNativeBundleFields
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPackedState (pack)
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "concrete" => RegistrationNativePlatformConcreteSource.writer reserve
local notation "writer" => RegistrationNativePlatformNativeInitEncoder.writer (n := n) (KemSK := KemSK) (source := source) reserve
noncomputable def handler : QueryImpl (RegistrationNativePlatformGenericBundle.Spec E n KemSK) (StateT (Native × Platform) ProbComp) :=
  fun query => pack (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source concrete query)
noncomputable def trusted : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (StateT (Native × Platform) ProbComp) :=
  fun query => pack (RegistrationNativePlatformExperiment.trusted coins setup checks representation created source query)

private theorem encoding (view : registration.InitView) (bytes : alloc.vec.Vec U8)
    (possible : RegistrationNativePlatformPublicationSupport.Possible
      (RegistrationNativePlatformGenericBundle.encoderWith (source := source) (Auxiliary := RegistrationServerRoleBackend.State) writer view) (.ok (.Some bytes))) :
    core.option.Option.Some (RegistrationNativeSourceWriterReadback.initVector view) = .Some bytes := by
  obtain ⟨owners,env,before,result,supported,returned⟩ := possible
  exact congrArg core.option.Option.Some
    (RegistrationNativePlatformNativeInitEncoder.encoder reserve view owners env before result supported bytes returned).symm

/-- The packed actual native dictionary is the literal source generic controller, with every reached private/platform coordinate. -/
theorem program_source (index : Nat) (owners : RegistrationNativeBeaconFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) (before : Native × Platform) :
    ((((RegistrationNativePlatformGenericBundle.bundle (trusted coins setup checks representation created) setup source
      (RegistrationNativePlatformGenericBundle.encoderWith writer) index).run owners).run env).run before) =
      (simulateQ (handler coins setup checks representation created reserve)
        (((RegistrationNativePlatformGenericBundle.program E setup source index).run owners).run env)).run before := by
  have equation := congrArg (fun work => ((work.run owners).run env).run before)
    (RegistrationNativePlatformGenericBundle.program_evaluate
      (Auxiliary := RegistrationServerRoleBackend.State) (handler (n := n) coins setup checks representation created reserve) setup source index)
  exact equation.symm

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before

private theorem vec_success (reply : RustM (Option (alloc.vec.Vec U8))) (bytes : Pqxdh.Bytes)
    (returned : (do let optional ← reply; .ok (optional.map TranscriptAuthParts.absSlice)) = .ok (some bytes)) :
    ∃ vector, reply = .ok (some vector) ∧ TranscriptAuthParts.absSlice vector = bytes := by
  cases reply with
  | fail error | div => cases returned
  | ok optional => cases optional with
    | none => cases returned
    | some vector => exact ⟨vector,rfl,Option.some.inj (RustM.ok.inj returned)⟩

/-- The literal current native bundle's concrete bytes carry its actual captured owner, without a whole writer or callback law. -/
theorem bundle (index : Nat) (before after : Native) (previous next : Platform) (bytes : Pqxdh.Bytes)
    (supported : ((.ok (some bytes),after),next) ∈ support
      (((RegistrationNativePlatformExperiment.bundle coins setup checks representation created source concrete index).run before).run previous)) :
    ∃ owner packet,before.beacons[index]? = some owner ∧
      RegistrationNativeWire.readInit RegistrationNativePlatformConcreteSource.wire bytes = some packet ∧
      (PqxdhRefinement.absBytes packet.pre_key).drop 64 = PqxdhEd25519EufCma.prekeyMessage (PqxdhPhase2InputBytes.word owner.prekeyPublic) ∧
      PqxdhEd25519EufCma.parseIdentity (PqxdhRefinement.absBytes packet.identity_key) =
        some (setup.joint.publicKeys owner.identitySeed).ed25519 := by
  simp only [RegistrationNativePlatformExperiment.bundle,StateT.run,bind_pure_comp,map_apply,support_map] at supported
  obtain ⟨actual,called,equal⟩ := supported
  have returned := congrArg (fun value => value.1.1) equal
  obtain ⟨vector,vectorReply,vectorBytes⟩ := vec_success actual.1.1.1.1 bytes returned
  have packed : (actual.1.1,(actual.1.2,actual.2)) ∈ support
      ((simulateQ (handler coins setup checks representation created reserve)
        (((RegistrationNativePlatformGenericBundle.program E setup source index).run before.beacons).run
          (RegistrationWorldAgreementCompiler.erase before.server.world))).run (before,previous)) := by
    unfold handler
    rw [← RegistrationNativePlatformPackedState.simulate_pack]
    simp only [pack,StateT.run,support_map]
    exact Set.mem_image_of_mem _ called
  rw [← program_source] at packed
  obtain ⟨owner,packet,found,decoded,prekey,identity⟩ := RegistrationNativePlatformBundleFieldSupport.bundle writer
    (encoding (n := n) (KemSK := KemSK) reserve) setup (trusted coins setup checks representation created) index
    before.beacons (RegistrationWorldAgreementCompiler.erase before.server.world) (before,previous)
    (actual.1.1,(actual.1.2,actual.2)) vector vectorReply packed
  exact ⟨owner,packet,found,vectorBytes ▸ decoded,prekey,identity⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformNativeBundleFields
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformNativeBundleFields.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformNativeBundleFields.program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformNativeBundleFields.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformNativeBundleFields.bundle
