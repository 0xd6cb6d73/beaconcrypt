-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationCore
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeEntropy

/-! Closing the concrete frontend and thin backend is an actual stateful compiler. These finite source equations retain both complete local states and expose the exact shared-World effect and record surfaces before full-ledger composition. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyEffects
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (WorldSpec EnvEffects effectLift)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativePlatformSelectiveEntropyEnvironment (State)
variable {n : Nat} {ι KemSK ProviderState Platform Value Next : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

noncomputable def close (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (work : RegistrationNativePlatformPublicFrontend.M n KemSK Platform source Value) :
    StateT (State n KemSK ProviderState Platform source) (OracleComp (WorldSpec n)) Value := fun before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (RegistrationNativePlatformSelectiveEntropyBackend.handler setup wire sign seed scalar candidate provider) (work.run before.1)).run before.2

/-- The stateful closure runs the literal frontend before returning both actual local poststates. -/
theorem close_run (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (work : RegistrationNativePlatformPublicFrontend.M n KemSK Platform source Value)
    (before : State n KemSK ProviderState Platform source) :
    (close setup wire sign seed scalar candidate provider work).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (RegistrationNativePlatformSelectiveEntropyBackend.handler setup wire sign seed scalar candidate provider)
          (work.run before.1)).run before.2 := rfl

/-- Closing pure frontend work preserves both actual local states without a World effect. -/
theorem pure_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (value : Value) :
    close (source := source) (n := n) (Platform := Platform) setup wire sign seed scalar candidate provider (pure value) = pure value := by
  funext before
  simp only [close, StateT.run_pure, simulateQ_pure, map_pure]
  rfl

/-- Actual sequential frontend work closes with the same state and callback order. -/
theorem bind_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (work : RegistrationNativePlatformPublicFrontend.M n KemSK Platform source Value)
    (next : Value → RegistrationNativePlatformPublicFrontend.M n KemSK Platform source Next) :
    close setup wire sign seed scalar candidate provider (work >>= next) =
      (close setup wire sign seed scalar candidate provider work >>= fun value => close setup wire sign seed scalar candidate provider (next value)) := by
  apply StateT.ext
  intro before
  simp only [StateT.run_bind, close_run, simulateQ_bind, map_bind, bind_map_left]

/-- The actual frontend environment effect reaches the same shared World directly and retains both local states. -/
theorem effect_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (query : (EnvEffects n).Domain)
    (before : State n KemSK ProviderState Platform source) :
    (close setup wire sign seed scalar candidate provider (RegistrationNativePlatformPublicFrontend.executeLocal (StateT.lift (RegistrationNativePlatformPublicFrontend.effect query)))).run before =
      (fun reply => (reply, before)) <$> effectLift query := by
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (RegistrationNativePlatformSelectiveEntropyBackend.handler setup wire sign seed scalar candidate provider)
      ((RegistrationNativePlatformPublicFrontend.executeLocal
        (StateT.lift (RegistrationNativePlatformPublicFrontend.effect query))).run before.1)).run before.2 = _
  rfl


/-- Sequential closure is exact for any adaptive source capability tree. -/
theorem close_program {J : Type} {spec : OracleSpec J}
    (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (implementation : QueryImpl spec (RegistrationNativePlatformPublicFrontend.M n KemSK Platform source))
    (work : OracleComp spec Value) :
    close setup wire sign seed scalar candidate provider (simulateQ implementation work) =
      simulateQ (fun query => close setup wire sign seed scalar candidate provider (implementation query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, pure_source]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, bind_source]
    congr 1
    funext reply
    exact ih reply

def liftPlatform (work : StateT Platform ProbComp Value) :
    StateT (State n KemSK ProviderState Platform source) ProbComp Value := fun before =>
  (fun result => (result.1, ((before.1.1, result.2), before.2))) <$> work.run before.1.2

def platformWork (work : StateT Platform ProbComp Value) :
    RegistrationNativePlatformPublicFrontend.M n KemSK Platform source Value := fun before =>
  (fun result => (result.1, (before.1, result.2))) <$>
    (RegistrationNativePlatformPublicFrontend.platformFull work).run before.2

private theorem coin_program (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (work : ProbComp Value) (before : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) :
    (simulateQ (RegistrationNativePlatformSelectiveEntropyBackend.handler setup wire sign seed scalar candidate provider)
      (simulateQ RegistrationNativePlatformPublicFrontend.publicCoin work)).run before =
      (fun value => (value, before)) <$> simulateQ PqxdhRecordLiftInterface.coinLift work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativePlatformPublicFrontend.publicCoin,
      RegistrationNativePlatformSelectiveEntropyBackend.handler, StateT.run_bind,
      StateT.run_lift, bind_pure_comp, bind_map_left, map_bind]
    apply bind_congr
    intro reply
    exact ih reply

private theorem map_apply {S V W : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : V → W) (work : StateT S m V) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- The literal source platform sampler becomes only public World coins and retains the complete source/private poststate. -/
theorem platform_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (work : StateT Platform ProbComp Value) :
    close (n := n) (KemSK := KemSK) (ProviderState := ProviderState) (source := source)
      setup wire sign seed scalar candidate provider (platformWork work) =
      RegistrationNativePlatformGatedRecordInterface.closed (liftPlatform work) := by
  funext before
  have actual := coin_program setup wire sign seed scalar candidate provider (work.run before.1.2) before.2
  have observed := congrArg (Functor.map (fun result =>
    (result.1.1, ((before.1.1, result.1.2), result.2)))) actual
  simpa only [close, platformWork, RegistrationNativePlatformPublicFrontend.platformFull,
    RegistrationNativePlatformGatedRecordInterface.closed, liftPlatform,
    StateT.run, simulateQ_map, map_apply, Functor.map_map, Prod.map_def, id_eq] using observed


private theorem bind_apply {S V W : Type} {m : Type → Type} [Monad m]
    (work : StateT S m V) (next : V → StateT S m W) (before : S) :
    (work >>= next) before = work before >>= fun result => next result.1 result.2 := rfl
private theorem pure_apply {S V : Type} {m : Type → Type} [Monad m] (value : V) (before : S) :
    (pure value : StateT S m V) before = pure (value, before) := rfl

def gateWork {Failure Output : Type}
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (size : Output → Nat) (output : Option Output) :
    RegistrationNativePlatformPublicFrontend.M n KemSK Platform source (Option Output) := fun before =>
  (fun result => (result.1, (before.1, result.2))) <$>
    (RegistrationNativePlatformOrdinaryGate.gate
      (fun amount => RegistrationNativePlatformPublicFrontend.platformFull (reserve amount)) size output).run before.2

/-- Post-send reservation is the same literal public capacity service in both complete states. -/
theorem gate_source {Failure Output : Type}
    (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (size : Output → Nat) (output : Option Output) :
    close (n := n) (KemSK := KemSK) (source := source) setup wire sign seed scalar candidate provider (gateWork reserve size output) =
      RegistrationNativePlatformGatedRecordInterface.closed
        (RegistrationNativePlatformOrdinaryGate.gate (fun amount => liftPlatform (reserve amount)) size output) := by
  cases output with
  | none => rfl
  | some value =>
    funext before
    simp only [close, gateWork, RegistrationNativePlatformOrdinaryGate.gate,
      RegistrationNativePlatformPublicFrontend.platformFull, RegistrationNativePlatformGatedRecordInterface.closed,
      liftPlatform, bind_apply, StateT.run, simulateQ_bind, simulateQ_map,
      map_bind, bind_map_left, map_apply, Functor.map_map, Prod.map_def, id_eq]
    have first := coin_program setup wire sign seed scalar candidate provider ((reserve (size value)).run before.1.2) before.2
    simp only [StateT.run] at first
    rw [first]
    simp only [bind_map_left]
    apply bind_congr
    intro result
    cases result.1 <;> rfl

/-- The actual direct record capability retains every public and private local state. -/
theorem record_leaf (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (query : PqxdhRecordLiftInterface.RecordQuery) (before : State n KemSK ProviderState Platform source) :
    (close setup wire sign seed scalar candidate provider
      (StateT.lift (RegistrationNativePlatformPublicFrontend.old (.inr query)))).run before =
      (fun result => (result, before)) <$>
        ((WorldSpec n).query (.inr (.inr query)) : OracleComp (WorldSpec n) _) := by
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyEffects

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyEffects.close_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyEffects.close_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyEffects.pure_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyEffects.pure_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyEffects.bind_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyEffects.bind_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyEffects.effect_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyEffects.effect_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyEffects.close_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyEffects.close_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyEffects.platform_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyEffects.platform_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyEffects.gate_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyEffects.gate_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyEffects.record_leaf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyEffects.record_leaf
