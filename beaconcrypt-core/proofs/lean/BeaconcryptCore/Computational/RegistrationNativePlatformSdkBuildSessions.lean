-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkServer
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! Response completion operates on the already moved source token. Its pin, peer-presence, reservation, record and publication stages preserve every session slot, including rejected and failed outcomes. The World-local completion type itself prevents a finisher from modifying the session table. -/
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkBuildSessions
variable {n : Nat} {P A B : Type}
local notation "State"=>RegistrationServerFrontendCompiler.State n
private def Keeps (work : StateT State (StateT P ProbComp) A) : Prop :=
  ∀before previous result,result∈support ((work.run before).run previous) → result.1.2.sessions=before.sessions
private theorem pure_keeps (value : A) : Keeps (n:=n) (P:=P) (pure value) := by
  intro before previous result supported
  simp only [StateT.run_pure,support_pure,Set.mem_singleton_iff] at supported
  subst result
  rfl
private theorem bind_keeps (work : StateT State (StateT P ProbComp) A)
    (next : A → StateT State (StateT P ProbComp) B) (first : Keeps work) (later : ∀value,Keeps (next value)) :
    Keeps (work>>=next) := by
  intro before previous result supported
  simp only [StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨middle,called,continued⟩:=supported
  exact (later middle.1.1 middle.1.2 middle.2 result continued).trans (first before previous middle called)
private theorem lift_keeps (work : StateT P ProbComp A) : Keeps (n:=n) (StateT.lift work) := by
  intro before previous result supported
  simp only [StateT.run_lift,bind_pure_comp,StateT.run_map,support_map] at supported
  obtain ⟨inner,_called,equal⟩:=supported
  cases equal
  rfl
private theorem world_keeps (work : StateT (RegistrationServerRootCompiler.Local n) (StateT P ProbComp) A) :
    Keeps (RegistrationNativePlatformServerSdk.world work) := by
  intro before previous result supported
  change result∈support (((fun inner=>(inner.1,{before with world:=inner.2})) <$>work.run before.world).run previous) at supported
  rw [StateT.run_map,support_map] at supported
  obtain ⟨inner,_called,equal⟩:=supported
  cases equal
  rfl
variable {Encoded : Type}
private theorem commit_keeps (result : RustM (RegistrationWorldServerCompletion.Result Encoded)) :
    Keeps (n:=n) (P:=P) (RegistrationNativePlatformServerSdk.commit result) := by
  intro before previous after supported
  cases result with
  | fail error | div=>exact pure_keeps _ before previous after supported
  | ok result=>
    cases result with
    | Err previousControl=>
      change after∈support (pure ((.ok none,{before with control:=previousControl}),previous)) at supported
      simp only [support_pure,Set.mem_singleton_iff] at supported
      subst after
      rfl
    | Ok published=>
      change after∈support (pure ((.ok (some (published.key_id,published.encoded)),{before with control:=published.control}),previous)) at supported
      simp only [support_pure,Set.mem_singleton_iff] at supported
      subst after
      rfl
private theorem initial_keeps (finish : RegistrationNativePlatformCompletionSdk.Completion n (StateT P ProbComp) Encoded)
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    Keeps (RegistrationNativePlatformCompletionSdk.fromInitial finish control pending) :=
  bind_keeps _ _ (world_keeps _) commit_keeps
private theorem occupancy_keeps (reserve : StateT P ProbComp Bool)
    (finish : RegistrationNativePlatformCompletionSdk.Completion n (StateT P ProbComp) Encoded)
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (occupied : Bool) :
    Keeps (RegistrationNativePlatformCompletionSdk.afterOccupancy (StateT.lift reserve) finish control lookup occupied) := by
  unfold RegistrationNativePlatformCompletionSdk.afterOccupancy
  split
  · exact pure_keeps _
  · exact pure_keeps _
  · exact pure_keeps _
  · apply bind_keeps _ _ (lift_keeps reserve)
    intro admitted
    split
    · exact initial_keeps _ _ _
    · exact pure_keeps _
private theorem after_pin_keeps (reserve : StateT P ProbComp Bool)
    (present : U64 → StateT State (StateT P ProbComp) Bool) (presentKept : ∀key,Keeps (present key))
    (finish : RegistrationNativePlatformCompletionSdk.Completion n (StateT P ProbComp) Encoded)
    (control : pqxdh.ServerState) (token : peer.ConsumedRegistration) (application : Slice U8)
    (pinResult : RustM (core.option.Option session.ServerAuthenticationPin)) :
    Keeps (RegistrationNativePlatformCompletionSdk.afterPin (StateT.lift reserve) present finish control token application pinResult) := by
  unfold RegistrationNativePlatformCompletionSdk.afterPin
  split
  · exact pure_keeps _
  · exact pure_keeps _
  · exact pure_keeps _
  · split
    · exact pure_keeps _
    · exact pure_keeps _
    · exact pure_keeps _
    · split
      · exact pure_keeps _
      · exact pure_keeps _
      · split
        · apply bind_keeps _ _ (presentKept _)
          intro occupied
          exact occupancy_keeps reserve finish control _ occupied
        · exact pure_keeps _
private theorem pin_keeps (coins : QueryImpl unifSpec (StateT P ProbComp)) :
    Keeps (n:=n) (RegistrationNativePlatformSourceBuild.pin coins) := by
  intro before previous result supported
  change result∈support (((fun inner=>(inner.1,{before with world:={before.world with world:=(inner.2,before.world.world.2)}})) <$>
    simulateQ coins ((RegistrationNativeServerPinRecompute.native before.pin.binding before.pin.public_key).run before.world.world.1)).run previous) at supported
  rw [StateT.run_map,support_map] at supported
  obtain ⟨inner,_called,equal⟩:=supported
  cases equal
  rfl

theorem complete (coins : QueryImpl unifSpec (StateT P ProbComp)) (reserve : StateT P ProbComp Bool)
    (finish : RegistrationNativePlatformCompletionSdk.Completion n (StateT P ProbComp) Encoded)
    (token : peer.ConsumedRegistration) (application : Slice U8) (before : State) (previous : P)
    (result : (RustM (Option (U64×Encoded))×State)×P)
    (supported : result∈support (((RegistrationNativePlatformCompletionSdk.complete
      (RegistrationNativePlatformSourceBuild.pin coins) (StateT.lift reserve)
      (RegistrationNativePlatformCompletionSdk.nativePresent coins) finish token application).run before).run previous)) :
    result.1.2.sessions=before.sessions := by
  have kept : Keeps (RegistrationNativePlatformCompletionSdk.complete
      (RegistrationNativePlatformSourceBuild.pin coins) (StateT.lift reserve)
      (RegistrationNativePlatformCompletionSdk.nativePresent coins) finish token application) := by
    unfold RegistrationNativePlatformCompletionSdk.complete
    apply bind_keeps _ _
    · intro current next after called
      simp only [StateT.run_get,StateT.run_pure,support_pure,Set.mem_singleton_iff] at called
      subst after
      rfl
    · intro current
      exact bind_keeps _ _ (pin_keeps coins) fun pinResult=>
        after_pin_keeps reserve _ (fun _=>world_keeps _) finish current.control token application pinResult
  exact kept before previous result supported

variable {KemSK : Type} {source : RegistrationNativeMldsa.Source}
theorem native_complete (coins : QueryImpl unifSpec (StateT P ProbComp)) (reserve : StateT P ProbComp Bool)
    (finish : RegistrationNativePlatformCompletionSdk.Completion n (StateT P ProbComp) Encoded)
    (token : peer.ConsumedRegistration) (application : Slice U8)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : P)
    (result : (RustM (Option (U64×Encoded))×RegistrationNativeExperiment.State n KemSK source)×P)
    (supported : result∈support (((RegistrationNativePlatformExperiment.server
      (RegistrationNativePlatformCompletionSdk.complete (RegistrationNativePlatformSourceBuild.pin coins) (StateT.lift reserve)
        (RegistrationNativePlatformCompletionSdk.nativePresent coins) finish token application)).run before).run previous)) :
    result.1.2.server.sessions=before.server.sessions := by
  rw [BeaconcryptCore.Refinement.AdapterPublicServerSourceLens.server_run,StateT.run_map,support_map] at supported
  obtain ⟨inner,called,equal⟩:=supported
  cases equal
  exact complete coins reserve finish token application before.server previous inner called
end BeaconcryptCore.Computational.RegistrationNativePlatformSdkBuildSessions

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkBuildSessions.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkBuildSessions.complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkBuildSessions.native_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkBuildSessions.native_complete
