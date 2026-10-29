-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawNativeMiddle

/-! The complete public native interpreter and the independently defined raw middle handler agree after resetting only the unused analysis ghosts. Registration uses its canonical source codec, while records use the actual optional wire writer and native admission. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawNativePublic
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentBackend (RegImpl XState handlerWith)
open PqxdhDeploymentIdealCut (unghost)
open PqxdhDeploymentIdealParams (Target Params)
open CborRawPublicState (Public toMemory)
open CborRawMiddleSimulation (Native)
variable {ι KemSK Reader Response Bk : Type} {baseSpec : OracleSpec ι} {n : Nat}

private theorem nonrecord_forward (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (reg : RegImpl KemSK Bk n) (query : Spec.Domain)
    (registration : CborSplitCompiler.recordCommand query = false) :
    CborRawGuardedJoin.nativeHandler setup codec route reg query = handlerWith setup codec route reg query := by
  rcases query with coin | command
  · rfl
  · cases command
    case serverSend => simp [CborSplitCompiler.recordCommand] at registration
    case serverRaw => simp [CborSplitCompiler.recordCommand] at registration
    case beaconSend => simp [CborSplitCompiler.recordCommand] at registration
    case beaconRaw => simp [CborSplitCompiler.recordCommand] at registration
    all_goals rfl

section Native
variable (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)

noncomputable def native :=
  CborRawEnvironmentRun.handler setup (CborTaggedSimulation.boundaryWire wire parse) (CborRawCompile.route parse)
    (PqxdhDeploymentIdealSteps.idealReg setup (CborRawCompile.sourceCodec wire parse) (CborRawCompile.route parse)
      checks target parameters created)

def reset (state : Public × Native KemSK) : Public × Native KemSK := (state.1, unghost state.2)

/-- Public registration adaptation is the same native registration step, including its actual reply and full private poststate. -/
theorem registration_step (query : Spec.Domain) (registration : CborSplitCompiler.recordCommand query = false)
    (state : Public × Native KemSK) :
    (fun value => (value.1, reset value.2)) <$>
        (native setup wire parse checks target parameters created query).run state =
      (CborRawMiddleSimulation.registration setup wire parse checks target parameters created query).run state := by
  have selectedRegistration : CborSplitCompiler.recordCommand (CborRawPublicClient.request state.1 query) = false := by
    change CborSplitCompiler.recordCommand (CborRawMiddleRegistration.request (toMemory state.1) query) = false
    rw [CborRawMiddleSimulation.request_record]
    exact registration
  rw [native, CborRawEnvironmentRun.handler_run,
    nonrecord_forward setup (CborTaggedSimulation.boundaryWire wire parse) (CborRawCompile.route parse) _ _
      selectedRegistration,
    CborRawNativeMiddle.backend_nonrecord setup (CborTaggedSimulation.boundaryWire wire parse)
      (CborRawCompile.sourceCodec wire parse) (CborRawCompile.route parse) _ _ selectedRegistration]
  simp only [CborRawMiddleSimulation.registration, StateT.run, Functor.map_map,
    CborRawPublicClient.request, CborRawPublicClient.reply, CborRawPublicClient.next, reset, bind_pure_comp]

/-- Established records have the same public state, actual native writer/admission outcome and complete private state. -/
theorem record_step (query : Spec.Domain) (record : CborSplitCompiler.recordCommand query = true)
    (state : Public × Native KemSK) :
    (fun value => (value.1, reset value.2)) <$>
        (native setup wire parse checks target parameters created query).run state =
      (CborRawMiddleSimulation.records setup wire parse checks created query).run state := by
  rcases state with ⟨publicState, current⟩
  cases publicState with
  | mk log lastId =>
    have original := CborRawNativeMiddle.record_native setup wire parse checks created.seed
      (PqxdhDeploymentIdealSteps.idealReg setup (CborRawCompile.sourceCodec wire parse) (CborRawCompile.route parse)
        checks target parameters created) query record current
    have decorated := congrArg (fun program => (fun value => (value.1, ((⟨log, lastId⟩ : Public), value.2))) <$>
      program) original
    simp only [Functor.map_map] at decorated
    rw [native, CborRawEnvironmentRun.handler_run]
    rcases query with coin | command
    · simp [CborSplitCompiler.recordCommand] at record
    · cases command
      all_goals try simp only [CborSplitCompiler.recordCommand, Bool.false_eq_true] at record
      all_goals simpa only [Functor.map_map, CborRawPublicClient.request, CborRawPublicClient.reply,
            CborRawPublicClient.next, CborRawMiddleRegistration.request, CborRawMiddleRegistration.reply,
            CborRawMiddleRegistration.assignment, CborRegistrationPublicLog.update, PqxdhDeploymentCompile.logReply,
            CborRawPublicState.toMemory, CborRawMiddleSimulation.records, CborRawMiddleSimulation.withBase,
            StateT.run, reset, id_eq] using decorated

/-- The complete guarded/public interpreter's protocol and private-state image is the raw middle handler. -/
theorem step (query : Spec.Domain) (state : Public × Native KemSK) :
    (fun value => (value.1, reset value.2)) <$>
        (native setup wire parse checks target parameters created query).run state =
      (CborRawMiddleSimulation.handler setup wire parse checks target parameters created query).run state := by
  cases record : CborSplitCompiler.recordCommand query with
  | false =>
      simpa only [CborRawMiddleSimulation.handler, record, Bool.false_eq_true, ite_false] using
        registration_step setup wire parse checks target parameters created query record state
  | true =>
      simpa only [CborRawMiddleSimulation.handler, record, ite_true] using
        record_step setup wire parse checks target parameters created query record state

/-- The registration handler never reads the unused legacy analysis ghosts that it resets on output. -/
theorem registration_reset (query : Spec.Domain) (state : Public × Native KemSK) :
    (CborRawMiddleSimulation.registration setup wire parse checks target parameters created query).run state =
      (CborRawMiddleSimulation.registration setup wire parse checks target parameters created query).run (reset state) := by
  let memory := toMemory state.1
  let decorate : Spec.Range (CborRawMiddleRegistration.request memory query) × Native KemSK →
      Spec.Range query × (Public × Native KemSK) := fun value =>
    (CborRawMiddleRegistration.reply memory query value.1,
      (⟨CborRegistrationPublicLog.update state.1.log (CborRawMiddleRegistration.request memory query) value.1,
        CborRawMiddleRegistration.assignment memory query value.1⟩, value.2))
  have erased := PqxdhDeploymentIdealCut.idealStep_unghost setup (CborRawCompile.sourceCodec wire parse)
    (CborRawCompile.route parse) checks target parameters created (CborRawMiddleRegistration.request memory query) state.2
  have decorated := congrArg (fun program => decorate <$> program) erased
  simpa only [decorate, memory, CborRawMiddleSimulation.registration, reset, StateT.run, Functor.map_map,
    Prod.map_apply, Prod.map_fst, Prod.map_snd, id_eq, bind_pure_comp] using decorated

/-- Every record and registration step is independent of those reset analysis fields. -/
theorem handler_reset (query : Spec.Domain) (state : Public × Native KemSK) :
    (CborRawMiddleSimulation.handler setup wire parse checks target parameters created query).run state =
      (CborRawMiddleSimulation.handler setup wire parse checks target parameters created query).run (reset state) := by
  cases record : CborSplitCompiler.recordCommand query with
  | false =>
      simpa only [CborRawMiddleSimulation.handler, record, Bool.false_eq_true, ite_false] using
        registration_reset setup wire parse checks target parameters created query state
  | true =>
      simp only [CborRawMiddleSimulation.handler, record, ite_true]
      rfl

/-- Exact complete protocol/private-state execution of every adaptive native program in the independently defined raw middle model. Only the stated unused analysis ghosts are reset. -/
theorem run {Result : Type} (work : OracleComp Spec Result) (state : Public × Native KemSK) :
    Prod.map id reset <$>
        (simulateQ (native setup wire parse checks target parameters created) work).run state =
      (simulateQ (CborRawMiddleSimulation.handler setup wire parse checks target parameters created) work).run
        (reset state) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (native setup wire parse checks target parameters created)
    (CborRawMiddleSimulation.handler setup wire parse checks target parameters created) reset
    (fun query current => (step setup wire parse checks target parameters created query current).trans
      (handler_reset setup wire parse checks target parameters created query current)) work state

end Native
end BeaconcryptCore.Computational.CborRawNativePublic

/-- info: 'BeaconcryptCore.Computational.CborRawNativePublic.registration_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawNativePublic.registration_step
/-- info: 'BeaconcryptCore.Computational.CborRawNativePublic.record_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawNativePublic.record_step
/-- info: 'BeaconcryptCore.Computational.CborRawNativePublic.step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawNativePublic.step

/-- info: 'BeaconcryptCore.Computational.CborRawNativePublic.registration_reset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawNativePublic.registration_reset

/-- info: 'BeaconcryptCore.Computational.CborRawNativePublic.handler_reset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawNativePublic.handler_reset

/-- info: 'BeaconcryptCore.Computational.CborRawNativePublic.run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawNativePublic.run
