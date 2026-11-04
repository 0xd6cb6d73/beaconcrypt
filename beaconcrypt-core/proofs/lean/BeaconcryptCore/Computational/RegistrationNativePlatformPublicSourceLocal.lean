-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceExecution
import BeaconcryptCore.Computational.RegistrationNativePlatformServerAcceptMemo
/-! The new local query language is interpreted by the actual indexed source dictionary. The proof rearranges one common platform state beside the private World, pool and memo, without replacing effectful callbacks by a fixed result function. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceLocal
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePublicSourceEffects (Extra Private close toPrivate fromPrivate)
open RegistrationNativePublicSourceCallbacks (services remember)
open RegistrationNativePlatformPublicSourceExecution (handler)
variable {n : Nat} {ι KemSK Platform Value : Type} {base : OracleSpec ι}

/-- External draws leave all native private counters untouched. -/
def external : QueryImpl unifSpec (StateT Platform ProbComp) := fun query => StateT.lift (unifSpec.query query)

private theorem external_run (work : ProbComp Value) (before : Platform) :
    (simulateQ external work).run before = (fun value => (value, before)) <$> work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query continuation ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, external, StateT.run_bind, StateT.run_lift,
        bind_assoc, pure_bind, ih, map_bind]

private theorem local_tree (selected : Bool)
    (query : (RegistrationNativeKemReferenceCompiler.Spec n KemSK).Domain) :
    simulateQ RegistrationNativePlatformPublicFrontend.embedLocal
      (RegistrationNativePlatformPublicFrontend.localQuery selected query) =
    simulateQ RegistrationNativePlatformPublicFrontend.old
      (RegistrationNativePublicFrontend.liftLocal selected query) := by
  rcases query with message | message | query | query
  · rfl
  · rfl
  · cases query <;> rfl
  · cases query <;> cases selected <;> rfl

private theorem old_program (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value) :
    simulateQ (handler setup wire route sign)
      (simulateQ RegistrationNativePlatformPublicFrontend.old work) =
    simulateQ (RegistrationNativePublicInterpreter.handler setup wire route sign) work := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  simp only [QueryImpl.compose, RegistrationNativePlatformPublicFrontend.old, simulateQ_spec_query, handler]

/-- The actual source leaf dictionary interprets every new local request, including the selected indexed getter route. -/
theorem local_query (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (selected : Bool) (query : (RegistrationNativeKemReferenceCompiler.Spec n KemSK).Domain)
    (before : RegistrationNativePublicInterpreter.State n KemSK) :
    Prod.map id toPrivate <$> (close setup seed scalar
      (simulateQ (handler setup wire route sign)
        (simulateQ RegistrationNativePlatformPublicFrontend.embedLocal
          (RegistrationNativePlatformPublicFrontend.localQuery selected query)))).run before =
      (RegistrationNativePublicSourceCallbacks.implementation setup wire route sign seed scalar query).run (toPrivate before) := by
  rw [local_tree, old_program]
  exact RegistrationNativePublicSourceCallbacks.query_source setup wire route sign seed scalar selected query before

noncomputable def interpret (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : RegistrationNativePlatformPublicFrontend.Base n KemSK Platform Value) :
    StateT (Private n KemSK) (StateT Platform ProbComp) Value := fun before previous =>
  (fun result => ((result.1.1, toPrivate result.2), result.1.2)) <$>
    (close setup seed scalar (simulateQ (handler setup wire route sign)
      (simulateQ RegistrationNativePlatformPublicFrontend.embedLocal (work.run previous)))).run (fromPrivate before)

private theorem lift_apply (work : OracleComp (RegistrationNativePlatformPublicFrontend.LocalSpec n KemSK) Value)
    (previous : Platform) :
    (StateT.lift work : RegistrationNativePlatformPublicFrontend.Base n KemSK Platform Value).run previous =
      (fun value => (value, previous)) <$> work := by
  rw [StateT.run_lift, bind_pure_comp]

private theorem close_map {A B : Type} (setup : Setup base KemSK)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (observe : A → B) (work : RegistrationNativePublicInterpreter.M n KemSK A)
    (before : RegistrationNativePublicInterpreter.State n KemSK) :
    (close setup seed scalar (observe <$> work)).run before =
      Prod.map observe id <$> (close setup seed scalar work).run before := by
  change simulateQ (RegistrationNativeSourceRoot.handler setup.source setup.hmac setup.joint setup.dh seed scalar)
      ((observe <$> work).run before) = Prod.map observe id <$>
    simulateQ (RegistrationNativeSourceRoot.handler setup.source setup.hmac setup.joint setup.dh seed scalar) (work.run before)
  rw [StateT.run_map, simulateQ_map]
  rfl

private theorem private_layout (before : Private n KemSK) : toPrivate (fromPrivate before) = before := by
  cases before
  rfl

/-- A local query under the new compiler is the actual source dictionary lifted through the same external platform state. -/
theorem handler_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (selected : Bool) (query : (RegistrationNativeKemReferenceCompiler.Spec n KemSK).Domain) :
    interpret (Platform := Platform) setup wire route sign seed scalar (RegistrationNativePlatformPublicFrontend.localHandler selected query) =
      RegistrationNativePlatformInterpret.state (external (Platform := Platform))
        (RegistrationNativePublicSourceCallbacks.implementation setup wire route sign seed scalar query) := by
  funext before previous
  change ((interpret setup wire route sign seed scalar (RegistrationNativePlatformPublicFrontend.localHandler selected query)).run before).run previous = _
  have actual := congrArg (fun work => (fun result => ((result.1, result.2), previous)) <$> work)
    (local_query setup wire route sign seed scalar selected query (fromPrivate before))
  change (fun result => ((result.1.1, toPrivate result.2), result.1.2)) <$>
    (close setup seed scalar (simulateQ (handler setup wire route sign)
      (simulateQ RegistrationNativePlatformPublicFrontend.embedLocal
        ((StateT.lift (RegistrationNativePlatformPublicFrontend.localQuery selected query) :
          RegistrationNativePlatformPublicFrontend.Base n KemSK Platform _).run previous)))).run (fromPrivate before) =
    (simulateQ external ((RegistrationNativePublicSourceCallbacks.implementation setup wire route sign seed scalar query).run before)).run previous
  rw [lift_apply, simulateQ_map, simulateQ_map, close_map, external_run]
  simpa only [Functor.map_map, private_layout, Prod.map_def, id_eq] using actual


/-- Rearranging the shared platform and private source state preserves pure returns. -/
theorem interpret_pure (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) (value : Value) :
    interpret (Platform := Platform) (n := n) setup wire route sign seed scalar (pure value) = pure value := by
  funext before previous
  simp only [interpret, StateT.run, StateT.monad_pure_def, StateT.pure, simulateQ_pure, close, map_pure, private_layout]

/-- Adaptive local continuations retain one reached private source state and one persistent platform state. -/
theorem interpret_bind {Next : Type} (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : RegistrationNativePlatformPublicFrontend.Base n KemSK Platform Value)
    (continuation : Value → RegistrationNativePlatformPublicFrontend.Base n KemSK Platform Next) :
    interpret setup wire route sign seed scalar (work >>= continuation) =
      (interpret setup wire route sign seed scalar work >>= fun value =>
        interpret setup wire route sign seed scalar (continuation value)) := by
  funext before previous
  simp only [interpret, simulateQ_bind, close, StateT.run, StateT.monad_bind_def,
    StateT.bind, simulateQ_bind, map_bind, bind_map_left, RegistrationNativePublicSourceEffects.layout]


/-- Whole adaptive indexed query programs use the same actual source leaf dictionary after state rearrangement. -/
theorem interpret_simulate (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (selected : Bool) (work : OracleComp (RegistrationNativeKemReferenceCompiler.Spec n KemSK) Value) :
    interpret (Platform := Platform) setup wire route sign seed scalar
      (simulateQ (RegistrationNativePlatformPublicFrontend.localHandler selected) work) =
    simulateQ (fun query => RegistrationNativePlatformInterpret.state external
      (RegistrationNativePublicSourceCallbacks.implementation setup wire route sign seed scalar query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => exact interpret_pure setup wire route sign seed scalar value
  | query_bind query continuation ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, interpret_bind, handler_source, ih]

private theorem close_simulate {Index : Type} {spec : OracleSpec Index}
    (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (implementation : QueryImpl spec (RegistrationNativePublicInterpreter.M n KemSK))
    (work : OracleComp spec Value) (before : RegistrationNativePublicInterpreter.State n KemSK) :
    (close setup seed scalar (simulateQ implementation work)).run before =
      (simulateQ (fun query => close setup seed scalar (implementation query)) work).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => rfl
  | query_bind query continuation ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, close, StateT.run,
        StateT.monad_bind_def, StateT.bind, simulateQ_bind]
      apply bind_congr
      rintro ⟨value, current⟩
      exact ih value current

private theorem coin_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : ProbComp Value) (before : RegistrationNativePublicInterpreter.State n KemSK) :
    (close setup seed scalar (simulateQ (handler setup wire route sign)
      (simulateQ RegistrationNativePlatformPublicFrontend.embedLocal
        (simulateQ RegistrationNativePlatformPublicFrontend.localCoin work)))).run before =
      (fun value => (value, before)) <$> work := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose, close_simulate]
  have same : (fun query => close setup seed scalar
      ((handler setup wire route sign ∘ₛ RegistrationNativePlatformPublicFrontend.embedLocal ∘ₛ
        RegistrationNativePlatformPublicFrontend.localCoin) query)) =
      (external (Platform := RegistrationNativePublicInterpreter.State n KemSK)) := by
    funext query state
    simp only [QueryImpl.compose, RegistrationNativePlatformPublicFrontend.localCoin,
      RegistrationNativePlatformPublicFrontend.embedLocal, RegistrationNativePlatformPublicFrontend.publicCoin,
      simulateQ_spec_query, handler, close, external, StateT.run]
    rfl
  rw [same]
  exact external_run work before

/-- Stateful public platform work is interpreted literally, without adding a native private counter or memo effect. -/
theorem interpret_platform (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : StateT Platform ProbComp Value) :
    interpret (n := n) setup wire route sign seed scalar
      (RegistrationNativePlatformPublicFrontend.platform (KemSK := KemSK) work) = StateT.lift work := by
  funext before previous
  change (fun result => ((result.1.1, toPrivate result.2), result.1.2)) <$>
    (close setup seed scalar (simulateQ (handler setup wire route sign)
      (simulateQ RegistrationNativePlatformPublicFrontend.embedLocal
        (simulateQ RegistrationNativePlatformPublicFrontend.localCoin (work.run previous))))).run (fromPrivate before) = _
  rw [coin_source]
  simp only [Functor.map_map, StateT.lift, bind_pure_comp, private_layout]
  exact (StateT.run_map (fun value => (value, before)) work previous).symm

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceLocal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceLocal.local_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceLocal.local_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceLocal.handler_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceLocal.handler_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceLocal.interpret_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceLocal.interpret_pure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceLocal.interpret_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceLocal.interpret_bind

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceLocal.interpret_simulate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceLocal.interpret_simulate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceLocal.interpret_platform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceLocal.interpret_platform
