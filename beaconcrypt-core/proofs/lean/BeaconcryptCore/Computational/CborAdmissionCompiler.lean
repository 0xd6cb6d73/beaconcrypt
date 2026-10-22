-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborAdmissionSubstitution
import BeaconcryptCore.Computational.CborAdmissionSend
import BeaconcryptCore.Computational.CborAdmissionPreload
import BeaconcryptCore.Computational.PqxdhDeploymentCompileInvariant
import BeaconcryptCore.Computational.PqxdhRegistrationScheduleState

/-! A source14 compiler can decide CBOR admission using the existing kernel reads and the last publicly returned assignment. Kernel reads remain private proof devices. A loaded kernel is cached before invoking the existing local record compiler, so admission introduces no additional kernel read. This module develops operational compiler correspondence; security-event and classwise-budget transport require their own checked joins. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborAdmissionCompiler
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentRecordCache (SourceSpec)
variable {ι KemSK Reader Response X : Type} {baseSpec : OracleSpec ι}

structure Local where
  copies : PqxdhDeploymentCompile.Local
  lastId : Std.U64

def Local.empty (serverId : Std.U64) : Local := ⟨PqxdhDeploymentCompile.Local.empty, serverId⟩

def merge (memory : Local) (native : PqxdhRegistrationSchedule.State KemSK) :
    PqxdhDeploymentNative.State KemSK := PqxdhDeploymentCompile.merge memory.copies native

structure Good (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (memory : Local) (native : PqxdhRegistrationSchedule.State KemSK) : Prop where
  nativeGood : PqxdhDeploymentCompileInvariant.Good setup codec memory.copies native
  lastId : memory.lastId = native.shared.2.server.control.last_key_id

def liftExisting {Result : Type}
    (work : StateT PqxdhDeploymentCompile.Local (OracleComp (SourceSpec KemSK)) Result) :
    StateT Local (OracleComp (SourceSpec KemSK)) Result := fun memory =>
  (fun result => (result.1, { memory with copies := result.2 })) <$> work.run memory.copies

def buildPayload (lastId : Std.U64) (payload : Option Pqxdh.Bytes) : Option Pqxdh.Bytes :=
  if CborSizing.responseLen ((payload.getD [0xff]).length + 88) (lastId.val + 1) ≤ CborSizing.maxMessageSize
  then payload else some []

/-- Even an oversized build issues the moved-token operation once, with empty application data. -/
noncomputable def build (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (session : Nat) (payload : Option Pqxdh.Bytes) :
    StateT Local (OracleComp (SourceSpec KemSK)) (Option PqxdhServerRegistrationPublication.Response) := fun memory =>
  (fun result => (result.1, ⟨result.2, (result.1.map PqxdhServerRegistrationPublication.Response.keyId).getD memory.lastId⟩)) <$>
    (PqxdhDeploymentCompile.compileImpl setup codec route (.inr (.build session (buildPayload memory.lastId payload)))).run
      memory.copies

/-- The existing peer read is cached before the local compiler can perform any record primitive. -/
noncomputable def serverSend (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (keyId : Std.U64) (plaintext : Pqxdh.Bytes) :
    StateT Local (OracleComp (SourceSpec KemSK)) (Option RawCtxSourceSend.Encrypted) := fun memory => do
  let kernel ← PqxdhDeploymentCompile.peerKernel memory.copies keyId
  match kernel with
  | none => pure (none, memory)
  | some current =>
      let loaded : PqxdhDeploymentCompile.Local :=
        { memory.copies with peers := Function.update memory.copies.peers keyId (some current) }
      if CborProductionBoundary.nextFits plaintext.length current.refined.control.send_sequence.val setup.serverKeyId.val then
        (fun result => (result.1, { memory with copies := result.2 })) <$>
          (PqxdhDeploymentCompile.serverLocal setup codec route (.inl (plaintext, keyId))).run loaded
      else pure (none, { memory with copies := loaded })

/-- An owner read and its existing public reconstruction supply the exact established sender and send counter. -/
noncomputable def beaconSend (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (index : Nat) (plaintext : Pqxdh.Bytes) :
    StateT Local (OracleComp (SourceSpec KemSK)) (Option RawCtxSourceSend.Encrypted) := fun memory =>
  if index < memory.copies.log.owners.length then do
    let kernel ← PqxdhDeploymentCompile.ownerKernel memory.copies index
    match kernel, PqxdhDeploymentCompile.ownerView codec memory.copies.log index with
    | some current, some view =>
        let loaded : PqxdhDeploymentCompile.Local :=
          { memory.copies with owners := Function.update memory.copies.owners index (some current) }
        if CborProductionBoundary.nextFits plaintext.length current.refined.control.send_sequence.val view.1.val then
          (fun result => (result.1, { memory with copies := result.2 })) <$>
            (PqxdhDeploymentCompile.beaconLocal setup codec index (.inl plaintext)).run loaded
        else pure (none, { memory with copies := loaded })
    | _, _ => pure (none, memory)
  else pure (none, memory)

noncomputable def compileImpl (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) : QueryImpl Spec (StateT Local (OracleComp (SourceSpec KemSK)))
  | .inr (.build session payload) => build setup codec route session payload
  | .inr (.serverSend keyId plaintext) => serverSend setup codec route keyId plaintext
  | .inr (.beaconSend index plaintext) => beaconSend setup codec index plaintext
  | query => liftExisting (PqxdhDeploymentCompile.compileImpl setup codec route query)

noncomputable def compile (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp Spec X) : OracleComp (SourceSpec KemSK) (X × Local) :=
  (simulateQ (compileImpl setup codec route) work).run (Local.empty setup.serverKeyId)

/-- Fixed-codec admission is separated from the registration codec representation join. -/
noncomputable def nativeHandler (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed) :
    QueryImpl Spec (StateT (PqxdhDeploymentNative.State KemSK) ProbComp) :=
  CborCommandFilter.handler CborProductionBoundary.allowed CborProductionBoundary.reject
    (PqxdhDeploymentNative.handler setup codec checks route seed)

theorem allowed_build (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (session : Nat) (payload : Option Pqxdh.Bytes) (memory : Local)
    (native : PqxdhRegistrationSchedule.State KemSK) (good : Good setup codec memory native) :
    CborProductionBoundary.allowed (.inr (.build session payload)) (merge memory native) =
      decide (CborSizing.responseLen ((payload.getD [0xff]).length + 88) (memory.lastId.val + 1) ≤
        CborSizing.maxMessageSize) := by
  simp only [CborProductionBoundary.allowed, merge, PqxdhDeploymentCompile.merge, good.lastId]
  rfl

theorem build_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (session : Nat) (payload : Option Pqxdh.Bytes) (memory : Local) :
    (build setup codec route session payload).run memory =
      (fun result => (result.1,
        (⟨result.2, (result.1.map PqxdhServerRegistrationPublication.Response.keyId).getD memory.lastId⟩ : Local))) <$>
      (PqxdhDeploymentCompile.compileImpl setup codec route
        (.inr (.build session (buildPayload memory.lastId payload)))).run memory.copies := rfl

/-- The source execution retains the forwarded build's exact reply, updated public log and complete native state. -/
theorem build_source_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed) (session : Nat) (payload : Option Pqxdh.Bytes)
    (memory : Local) (native : PqxdhRegistrationSchedule.State KemSK) :
    (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks seed)
      ((build setup codec route session payload).run memory)).run native =
      (fun result => ((result.1,
        (⟨{ memory.copies with log := (PqxdhDeploymentCompile.logReply memory.copies.log
            (.build session (buildPayload memory.lastId payload)) result.1) },
          (result.1.map PqxdhServerRegistrationPublication.Response.keyId).getD memory.lastId⟩ : Local)), result.2)) <$>
        (PqxdhRegistrationSchedule.handler setup codec checks seed
          (.inr (.build session (buildPayload memory.lastId payload)))).run native := by
  simp only [build_run, simulateQ_map, StateT.run_map, PqxdhDeploymentCompile.compileImpl]
  rw [PqxdhDeploymentCompileStep.forwardLogged_run setup codec checks seed
    (.build session (buildPayload memory.lastId payload)) (.build session (buildPayload memory.lastId payload))
    id memory.copies native]
  simp only [Functor.map_map, id_eq]

/-- Build compilation forwards the selected native operation and merges its complete poststate. -/
theorem build_native_exact (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed) (session : Nat) (payload : Option Pqxdh.Bytes)
    (memory : Local) (native : PqxdhRegistrationSchedule.State KemSK) (good : Good setup codec memory native) :
    (fun result => (result.1.1, merge result.1.2 result.2)) <$>
      (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks seed)
        ((build setup codec route session payload).run memory)).run native =
      (PqxdhDeploymentNative.handler setup codec checks route seed
        (.inr (.build session (buildPayload memory.lastId payload)))).run (merge memory native) := by
  have old :=
    PqxdhDeploymentCompileStep.step_merge setup codec checks route seed
      (.inr (.build session (buildPayload memory.lastId payload))) memory.copies native
      (PqxdhDeploymentCompileInvariant.good_inv setup codec memory.copies native good.nativeGood)
  rw [PqxdhDeploymentCompileStep.compiledImpl_run] at old
  simpa only [build_run, simulateQ_map, StateT.run_map, Functor.map_map, merge, Prod.map_apply, id_eq] using old

/-- The oversized-build compiler exactly implements early rejection, including token consumption. -/
theorem build_step_exact (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed) (session : Nat) (payload : Option Pqxdh.Bytes)
    (memory : Local) (native : PqxdhRegistrationSchedule.State KemSK) (good : Good setup codec memory native) :
    (fun result => (result.1.1, merge result.1.2 result.2)) <$>
      (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks seed)
        ((build setup codec route session payload).run memory)).run native =
      (nativeHandler setup codec checks route seed (.inr (.build session payload))).run (merge memory native) := by
  rw [build_native_exact setup codec checks route seed session payload memory native good]
  change _ = if CborProductionBoundary.allowed (.inr (.build session payload)) (merge memory native) then
    (PqxdhDeploymentNative.handler setup codec checks route seed (.inr (.build session payload))).run (merge memory native)
    else pure (CborProductionBoundary.reject (.inr (.build session payload)) (merge memory native))
  rw [allowed_build setup codec session payload memory native good]
  by_cases fits : CborSizing.responseLen ((payload.getD [0xff]).length + 88) (memory.lastId.val + 1) ≤
      CborSizing.maxMessageSize <;>
    simp only [buildPayload, fits, decide_true, decide_false, Bool.false_eq_true, ite_false, ite_true]
  case pos => rw [ite_eq_left fits]
  case neg =>
    rw [ite_eq_right fits]
    exact CborAdmissionSubstitution.deployment_build_empty setup codec checks route seed session (merge memory native)

end BeaconcryptCore.Computational.CborAdmissionCompiler

/-- info: 'BeaconcryptCore.Computational.CborAdmissionCompiler.allowed_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionCompiler.allowed_build
/-- info: 'BeaconcryptCore.Computational.CborAdmissionCompiler.build_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionCompiler.build_run
/-- info: 'BeaconcryptCore.Computational.CborAdmissionCompiler.build_source_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionCompiler.build_source_run
/-- info: 'BeaconcryptCore.Computational.CborAdmissionCompiler.build_native_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionCompiler.build_native_exact
/-- info: 'BeaconcryptCore.Computational.CborAdmissionCompiler.build_step_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionCompiler.build_step_exact
