-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBundleKemResources
import BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedHandler
import BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedProfile
/-! The complete corrected initialized indexed-KEM program has the exact original API bills qCreate, qAccept and qFinish for private births, encapsulations and decapsulations respectively. All other callbacks and startup cost zero in these classes, while preserving the complete client, pool, platform and failed-operation effects. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BeaconcryptCore.Computational.RegistrationNativePlatformSourceAccept.authenticate
  BeaconcryptCore.Computational.RegistrationNativePlatformSourceBuild.pin
namespace BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources
open BeaconcryptCore.Refinement
open RegistrationNativeKemResourceFootprint (Kind)
open RegistrationNativeKemResourceCaps (Counted)
open RegistrationNativeKemCountedProgram (Spec)
open RegistrationNativePlatformKemCountedProgram (M inject lift)
variable {I KemSK State Platform A B : Type} {n : Nat} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

abbrev Bounded (kind : Kind) (cap : Nat) (work : StateT State (M KemSK Platform) A) : Prop :=
  ∀ before previous, ((work.run before).run previous).IsQueryBoundP (Counted kind) cap

theorem pure_bound (kind : Kind) (cap : Nat) (value : A) : Bounded kind cap (pure value : StateT State (M KemSK Platform) A) := fun _ _ => isQueryBoundP_pure _ _ _
theorem bind_bound (kind : Kind) (work : StateT State (M KemSK Platform) A) (next : A → StateT State (M KemSK Platform) B)
    (first later : Nat) (bounded : Bounded kind first work) (continued : ∀ value, Bounded kind later (next value)) :
    Bounded kind (first + later) (work >>= next) := by
  intro before previous
  simp only [StateT.run_bind]
  exact isQueryBoundP_bind (bounded before previous) (fun result _ => continued result.1.1 result.1.2 result.2)

theorem bind_left (kind : Kind) (work : StateT State (M KemSK Platform) A) (next : A → StateT State (M KemSK Platform) B)
    (cap : Nat) (bounded : Bounded kind 0 work) (continued : ∀ value, Bounded kind cap (next value)) :
    Bounded kind cap (work >>= next) := by
  simpa only [Nat.zero_add] using bind_bound kind work next 0 cap bounded continued

theorem inject_bound (kind : Kind) (work : StateT State (OracleComp (Spec KemSK)) A) (cap : Nat)
    (bounded : RegistrationNativeKemResourceCaps.Bounded kind cap work) : Bounded kind cap (inject work : StateT State (M KemSK Platform) A) := by
  intro before previous
  change ((StateT.lift (work.run before) : M KemSK Platform (A × State)).run previous).IsQueryBoundP (Counted kind) cap
  simpa only [StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff] using bounded before

theorem lift_free (kind : Kind) (work : StateT State (StateT Platform ProbComp) A) : Bounded kind 0 (lift (KemSK := KemSK) work) :=
  fun before previous => RegistrationNativeKemResourceCaps.liftState_free kind (work.run before) previous

theorem ordinary_server_free (kind : Kind) (work : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) A) :
    Bounded kind 0 (RegistrationNativePlatformKemCountedAccept.ordinaryServer (KemSK := KemSK) (source := source) work) := by
  intro before previous
  change ((Prod.map id (fun after => { before with server := after }) <$>
    ((RegistrationNativePlatformKemCountedProgram.lift work).run before.server)).run previous).IsQueryBoundP (Counted kind) 0
  rw [StateT.run_map, isQueryBoundP_map_iff]
  exact lift_free kind work before.server previous

theorem get_free (kind : Kind) : Bounded kind 0 (get : StateT State (M KemSK Platform) State) := by
  intro before previous
  change (pure ((before, before), previous) : OracleComp (Spec KemSK) _).IsQueryBoundP _ 0
  trivial

theorem modify_free (kind : Kind) (changeState : State → State) : Bounded kind 0 (modify changeState : StateT State (M KemSK Platform) Unit) := by
  intro before previous
  change (pure (((), changeState before), previous) : OracleComp (Spec KemSK) _).IsQueryBoundP _ 0
  trivial

theorem afterAuthentication (kind : Kind) (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    Bounded kind (if kind = .encapsulate then 1 else 0)
      (RegistrationNativePlatformKemCountedAccept.afterAuthentication (source := source) setup checks reserve representation created packet authenticated) := by
  unfold RegistrationNativePlatformKemCountedAccept.afterAuthentication
  apply bind_left kind _ _ _ (get_free kind)
  intro before
  by_cases replay : before.server.consumed.contains (RegistrationReplaySchedule.identifier authenticated) = true
  · simp only [replay, ite_true]
    exact pure_bound kind _ _
  · simp only [replay]
    apply bind_left kind _ _ _ (ordinary_server_free kind _)
    intro allocated
    cases allocated with
    | false =>
        simp only [Bool.false_eq_true, ite_false]
        exact pure_bound kind _ _
    | true =>
        simp only [ite_true]
        apply bind_bound kind _ _ _ 0 (inject_bound kind _ _ (RegistrationNativeKemResourceCaps.agree kind setup checks representation created authenticated))
        intro result
        cases result with
        | fail error | div => exact pure_bound kind 0 _
        | ok effect => cases effect <;> first | exact ordinary_server_free kind _ | exact pure_bound kind 0 _

theorem afterPin (kind : Kind) (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec A B)
    (checks : PqxdhServerAuthExperiment.Checks) (reserve : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket) (pin : RustM (core.option.Option session.ServerAuthenticationPin)) :
    Bounded kind (if kind = .encapsulate then 1 else 0)
      (RegistrationNativePlatformKemCountedAccept.afterPin (source := source) setup codec checks reserve route representation created packet pin) := by
  unfold RegistrationNativePlatformKemCountedAccept.afterPin
  cases pin with
  | fail error | div => exact pure_bound kind _ _
  | ok optional => cases optional with
    | none => exact pure_bound kind _ _
    | some pin =>
        apply bind_left kind _ _ _ (ordinary_server_free kind _)
        intro checked
        cases checked with
        | fail error | div => exact pure_bound kind _ _
        | ok result => rcases result with ⟨events, outcome⟩; cases outcome <;> first
            | exact afterAuthentication kind setup checks reserve representation created packet _
            | exact pure_bound kind _ _

theorem accept (kind : Kind) (setup : PqxdhServerAuthExperiment.Setup base KemSK) (codec : PqxdhServerAuthExperiment.Codec A B)
    (checks : PqxdhServerAuthExperiment.Checks) (reserve : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket) :
    Bounded kind (if kind = .encapsulate then 1 else 0)
      (RegistrationNativePlatformKemCountedAccept.accept (source := source) setup codec checks reserve route representation created packet) := by
  unfold RegistrationNativePlatformKemCountedAccept.accept
  exact bind_left kind _ _ _ (ordinary_server_free kind _)
    (afterPin kind setup codec checks reserve route representation created packet)

def apiClass : Kind → Fin 12
  | .birth => 1
  | .encapsulate => 3
  | .decapsulate => 5

variable [primitive : AdapterSealPrimitive.Operations]
variable {E : Type}
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

theorem handler (kind : Kind) (query : RegistrationNativeRawAdapter.TypedSpec.Domain) :
    Bounded kind (if RegistrationNativeRawAdapter.kind query = apiClass kind then 1 else 0)
      (RegistrationNativePlatformKemCountedHandler.handler (n := n) setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer erased helper writer query) := by
  cases query with
  | inl coin => cases kind <;> exact lift_free _ _
  | inr query => cases query with
    | create edPin mlPin keyId =>
        cases kind <;> exact inject_bound _ _ _ (RegistrationNativeKemResourceCaps.create _ setup checks representation created edPin mlPin keyId)
    | bundle owner =>
        cases kind <;> exact RegistrationNativePlatformBundleKemResources.counted_program _ setup checks representation created writer owner
    | accept packet =>
        cases kind <;> exact bind_left _ _ _ _ (modify_free _ _)
          (fun _ => accept _ setup (RegistrationNativeWire.ledgerCodec wire) checks (StateT.lift reserveRegistration) route representation created packet)
    | build session application =>
        cases kind <;> exact lift_free _ _
    | finish owner packet =>
        cases kind <;> exact inject_bound _ _ _ (RegistrationNativeKemResourceCaps.finish _ setup checks representation created wire owner packet)
    | hmac key message => cases kind <;> exact pure_bound _ _ _
    | _ => cases kind <;> exact lift_free _ _

theorem typed (kind : Kind) (work : OracleComp RegistrationNativeRawAdapter.TypedSpec A) (cap : Nat)
    (bounded : work.IsQueryBoundP (fun query => RegistrationNativeRawAdapter.kind query = apiClass kind) cap) :
    Bounded kind cap (simulateQ
      (RegistrationNativePlatformKemCountedHandler.handler (n := n) setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer erased helper writer) work) :=
  RegistrationNativePlatformQueryBounds.simulate_bound _ (Counted kind) _
    (handler setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer kind)
    work cap bounded

omit primitive in
def allowance (kind : Kind) (budget : PqxdhDeploymentInterface.Budget) : Nat := budget.cap (apiClass kind).castSucc.castSucc

omit primitive in
theorem wrap_cost (kind : Kind) (bounds : PqxdhDeploymentInterface.FreshBounds) (full : Fin 14) :
    PqxdhDeploymentCompileSecrecy.wrapCost bounds (apiClass kind) full =
      if full = (apiClass kind).castSucc.castSucc then 1 else 0 := by
  cases kind <;> fin_cases full <;> rfl

omit primitive in
theorem wrap_sum (kind : Kind) (bounds : PqxdhDeploymentInterface.FreshBounds) (budget : PqxdhDeploymentInterface.Budget) :
    (∑ full, PqxdhDeploymentCompileSecrecy.wrapCost bounds (apiClass kind) full * budget.cap full) = allowance kind budget := by
  simp [wrap_cost, allowance]

theorem compiled (kind : Kind) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget work) :
    Bounded kind (allowance kind budget) (simulateQ
      (RegistrationNativePlatformKemCountedHandler.handler (n := n) setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer erased helper writer)
      (RegistrationNativeFullCompiler.compile setup.source.crypto wire created.server.server.metadata.sender bounds mode work)) := by
  apply typed setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer
  simpa only [wrap_sum] using RegistrationNativeFullCompiler.compile_bound setup.source.crypto wire
    created.server.server.metadata.sender bounds mode work budget bounded (apiClass kind)

omit primitive in
theorem ordinary_free (kind : Kind) (work : ProbComp A) :
    (RegistrationNativeKemCountedProgram.lift (KemSK := KemSK) work).IsQueryBoundP (Counted kind) 0 := by
  cases kind with
  | birth => exact RegistrationNativeKemCountedBirthCaps.ordinary_free work
  | encapsulate => exact RegistrationNativeKemCountedCaps.ordinary_free .encapsulate work
  | decapsulate => exact RegistrationNativeKemCountedCaps.ordinary_free .decapsulate work

omit primitive in
theorem allowance_birth (budget : PqxdhDeploymentInterface.Budget) : allowance .birth budget = budget.create := rfl
omit primitive in
theorem allowance_encapsulate (budget : PqxdhDeploymentInterface.Budget) : allowance .encapsulate budget = budget.accept := rfl
omit primitive in
theorem allowance_decapsulate (budget : PqxdhDeploymentInterface.Budget) : allowance .decapsulate budget = budget.finish := rfl

theorem initialized (kind : Kind) (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) A)
    (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publicInput, RegistrationNativeInterface.Respects budget (adversary publicInput)) (previous : Platform) :
    ((RegistrationNativePlatformKemCountedProfile.program (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation
      reserveRegistration reservePeer erased helper writer bounds mode adversary).run previous).IsQueryBoundP (Counted kind) (allowance kind budget) := by
  unfold RegistrationNativePlatformKemCountedProfile.program
  rw [StateT.run_bind, StateT.run_lift]
  rw [← Nat.zero_add (allowance kind budget)]
  apply isQueryBoundP_bind (n := 0) (m := allowance kind budget)
  · simpa only [bind_pure_comp, isQueryBoundP_map_iff] using ordinary_free (KemSK := KemSK) kind
      (RegistrationNativePlatformKemCountedProfile.start (n := n) setup source ensureInit identityIndex serverKeyId)
  · intro initialized _
    cases initialized.1 with
    | none => exact isQueryBoundP_pure _ _ _
    | some initial =>
        simp only [bind_pure_comp, StateT.run_map, isQueryBoundP_map_iff]
        exact compiled setup checks wire route representation initial.created initial.credential view failure allocation
          reserveRegistration reservePeer erased helper writer kind bounds mode (adversary initial.public) budget
          (bounded initial.public) initial.state initialized.2

end BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.pure_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.pure_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.bind_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.bind_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.bind_left' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.bind_left

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.inject_bound' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.inject_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.lift_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.lift_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.ordinary_server_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.ordinary_server_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.get_free' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.get_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.modify_free' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.modify_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.afterAuthentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.afterAuthentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.afterPin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.afterPin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.accept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.handler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.typed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.wrap_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.wrap_cost

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.wrap_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.wrap_sum

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.compiled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.compiled

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.ordinary_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.ordinary_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.allowance_birth' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.allowance_birth

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.allowance_encapsulate' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.allowance_encapsulate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.allowance_decapsulate' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.allowance_decapsulate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemHandlerResources.initialized
