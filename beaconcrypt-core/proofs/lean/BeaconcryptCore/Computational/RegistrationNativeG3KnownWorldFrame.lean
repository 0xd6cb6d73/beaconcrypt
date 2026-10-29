-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrameCore
import BeaconcryptCore.Computational.RegistrationNativeWorldViewRecords
import BeaconcryptCore.Computational.RegistrationNativeKemWorldRecordUniform

/-! The actual common native World does not read the bookkeeping erased by the G3 semantic view. The exclusion is exactly hidden-reference installation, which intentionally reads the persistent seed cache and earlier role uses. All concrete records, populated AD, CTX state, raw attempts, owners and produced frames remain visible in the view. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrame
open PqxdhRecordLiftWorld (State)
open PqxdhRecordLiftInterface (WorldSpec)
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeG3KnownWorldFrameCore (Allowed)
variable {n : Nat} {ι KemSK Reader Response Value : Type} {base : OracleSpec ι}

def view (before : State n) : State n := RegistrationNativeKemWorldUniform.mask
  (RegistrationNativeWorldView.project (RegistrationNativeHiddenWorldInstall.view before))

theorem view_idempotent (before : State n) : view (view before) = view before := by
  simp only [view, RegistrationNativeKemWorldUniform.mask, RegistrationNativeWorldView.project,
    RegistrationNativeWorldView.eraseNative, RegistrationWorldCoinCompiler.eraseCoin,
    RegistrationNativeHiddenWorldInstall.view, Function.update_idem]

theorem handler_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : (WorldSpec n).Domain) (quiet : Allowed query) (before : State n) :
    Prod.map id view <$> (PqxdhRecordLiftWorld.handler setup codec route query).run before =
      Prod.map id view <$> (PqxdhRecordLiftWorld.handler setup codec route query).run (view before) := by
  have seeds := congrArg (fun distribution => Prod.map id view <$> distribution)
    (RegistrationNativeG3KnownWorldFrameCore.handler_input setup codec route query quiet before)
  have native := congrArg (fun distribution => Prod.map id view <$> distribution)
    (RegistrationNativeWorldViewRecords.handler_input setup codec route query (RegistrationNativeHiddenWorldInstall.view before))
  have uniform := congrArg (fun distribution => Prod.map id view <$> distribution)
    (RegistrationNativeKemWorldRecordUniform.handler_input setup codec route query
      (RegistrationNativeWorldView.project (RegistrationNativeHiddenWorldInstall.view before)))
  simp only [Functor.map_map, Prod.map_def, id_eq, view, RegistrationNativeKemWorldUniform.mask,
    RegistrationNativeWorldView.project, RegistrationNativeWorldView.eraseNative,
    RegistrationWorldCoinCompiler.eraseCoin, RegistrationNativeHiddenWorldInstall.view, Function.update_idem] at seeds native uniform ⊢
  exact seeds.trans (native.trans uniform)

private noncomputable def normalized (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) : QueryImpl (WorldSpec n) (StateT (State n) ProbComp) :=
  fun query state => Prod.map id view <$> (PqxdhRecordLiftWorld.handler setup codec route query).run state

private theorem program_normalized (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (WorldSpec n) Value)
    (quiet : AllQueriesSatisfy work Allowed) (before : State n) :
    Prod.map id view <$> (simulateQ (PqxdhRecordLiftWorld.handler setup codec route) work).run before =
      (simulateQ (normalized setup codec route) work).run (view before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_def, id_eq]
  | query_bind query next ih =>
      obtain ⟨allowed, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp quiet
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      change _ = (Prod.map id view <$> (PqxdhRecordLiftWorld.handler setup codec route query).run (view before)) >>= _
      rw [← handler_input setup codec route query allowed before, bind_map_left]
      exact bind_congr fun result => ih result.1 (later result.1) result.2

/-- Every actual adaptive common World program retains the same complete semantic outcome under the G3 input view. -/
theorem program_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (WorldSpec n) Value)
    (quiet : AllQueriesSatisfy work Allowed) (before : State n) :
    Prod.map id view <$> (simulateQ (PqxdhRecordLiftWorld.handler setup codec route) work).run before =
      Prod.map id view <$> (simulateQ (PqxdhRecordLiftWorld.handler setup codec route) work).run (view before) := by
  have first := program_normalized setup codec route work quiet before
  have second := program_normalized setup codec route work quiet (view before)
  rw [view_idempotent] at second
  exact first.trans second.symm

end BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrame.view_idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrame.view_idempotent
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrame.handler_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrame.handler_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrame.program_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3KnownWorldFrame.program_input
