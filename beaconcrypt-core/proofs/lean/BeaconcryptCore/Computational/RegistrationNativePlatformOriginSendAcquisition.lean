-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeTails
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginSealRetention
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedFields
/-! A newly retained seal in an actual single native callback identifies its literal hidden sealing request, selected coordinate and real reserve continuation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendAcquisition
open CtxRomAuth
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode ctxInterpreter)
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativePlatformOriginNativeTails (source Envelope)
open RegistrationNativePlatformOriginReserveContinuationBound (continued)
variable {n : Nat} {I KemSK Platform Failure Reader Response A : Type} {base : OracleSpec I}

structure Receipt (service : QueryImpl (ServiceSpec n) (StateT (CtxPrivate n) ProbComp))
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure)) (beforeP : Platform)
    (work : OracleComp (ServiceSpec n) A) (before : CtxPrivate n) (result : A × CtxPrivate n)
    (label : Label n) (entry : CtxSuccessfulSeal) where
  pending : PqxdhRecordLiftProtocol.Sealing n
  tag : PqxdhDeploymentInterface.FrameTag
  after : Option RawCtxSourceSend.Encrypted → Platform → A
  form : work=(do
    let _ ← ((ServiceSpec n).query (.lookup pending.material) : OracleComp (ServiceSpec n) _)
    let reply ← ((ServiceSpec n).query (.sealing pending) : OracleComp (ServiceSpec n) _)
    continued reserve (fun output state=>pure (after output state)) beforeP tag reply)
  looked : Unit × CtxPrivate n
  lookupCalled : looked∈support ((service (.lookup pending.material)).run before)
  sealed : Option RawCtxSourceSend.Encrypted × CtxPrivate n
  sealCalled : sealed∈support ((service (.sealing pending)).run looked.2)
  tailCalled : result∈support ((simulateQ service
    (continued reserve (fun output state=>pure (after output state)) beforeP tag sealed.1)).run sealed.2)
  material : pending.material=label
  fresh : entry∉(looked.2.keys label).1.successfulSeals
  inserted : entry∈(sealed.2.keys label).1.successfulSeals

private theorem coins_quiet {X : Type} (work : ProbComp X) :
    (simulateQ (RegistrationNativePlatformOriginGateSource.coins (n := n)) work).AllQueriesSatisfy
      (fun query=>¬RegistrationNativePlatformOriginSourceTails.Sealing query) := by
  induction work using OracleComp.inductionOn with
  | pure value=>trivial
  | query_bind query next ih=>
    simp only [simulateQ_bind,simulateQ_spec_query,RegistrationNativePlatformOriginGateSource.coins,bind_assoc,
      allQueriesSatisfy_query_bind_iff]
    refine ⟨?_,fun _=>⟨?_,fun reply=>ih reply⟩⟩
    all_goals rintro ⟨pending,impossible⟩;cases impossible
private theorem continued_quiet (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (after : Option RawCtxSourceSend.Encrypted → Platform → A) (before : Platform)
    (tag : PqxdhDeploymentInterface.FrameTag) (reply : Option RawCtxSourceSend.Encrypted) :
    (continued (n := n) reserve (fun output state=>pure (after output state)) before tag reply).AllQueriesSatisfy
      (fun query=>¬RegistrationNativePlatformOriginSourceTails.Sealing query) := by
  unfold continued
  rw [allQueriesSatisfy_query_bind_iff]
  refine ⟨?_,fun _=>?_⟩
  · rintro ⟨pending,impossible⟩;cases impossible
  · exact allQueriesSatisfy_bind (coins_quiet _) (fun _=>by trivial)

variable (modes : Label n → KeyMode) (ideal : ∀label,modes label≠.real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup base KemSK) (codec : Codec Reader Response)
local notation "service" => ctxInterpreter modes replace setup codec
include ideal in
/-- A new entry in the literal source envelope occurs at that same supported sealing request and its actual material coordinate; the full reserve suffix remains attached. -/
theorem envelope (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure)) (beforeP : Platform)
    (work : OracleComp (ServiceSpec n) A) (form : Envelope reserve beforeP work)
    (before : CtxPrivate n) (result : A × CtxPrivate n)
    (supported : result∈support ((simulateQ service work).run before))
    (label : Label n) (entry : CtxSuccessfulSeal)
    (absent : entry∉(before.keys label).1.successfulSeals) (present : entry∈(result.2.keys label).1.successfulSeals) :
    Nonempty (Receipt service reserve beforeP work before result label entry) := by
  obtain ⟨pending,tag,after,form⟩ := form
  have called := supported
  rw [form,simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at called
  obtain ⟨looked,lookupCalled,later⟩ := called
  rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at later
  obtain ⟨sealed,sealCalled,tailCalled⟩ := later
  have lookupKeeps := (PqxdhRecordFactsOriginReceive.lookup_preserves modes replace setup codec pending.material before looked lookupCalled).1
  have fresh : entry∉(looked.2.keys label).1.successfulSeals := by rw [lookupKeeps];exact absent
  have tailKeeps := RegistrationNativePlatformOriginSealRetention.program modes ideal replace setup codec _
    (continued_quiet reserve after beforeP tag sealed.1) sealed.2 result tailCalled label
  have inserted : entry∈(sealed.2.keys label).1.successfulSeals := by rw [←tailKeeps];exact present
  have material : pending.material=label := by
    by_contra different
    have other := PqxdhRecordLiftCtxHybrid.sealing_other modes replace setup codec pending looked.2 sealed sealCalled label (Ne.symm different)
    exact fresh ((congrArg (fun state=>state.1.successfulSeals) other) ▸ inserted)
  exact ⟨⟨pending,tag,after,form,looked,lookupCalled,sealed,sealCalled,tailCalled,material,fresh,inserted⟩⟩

include ideal in
/-- Every new dictionary entry in the complete actual native callback derives its original hidden-send envelope and same supported sealing receipt, with all nonsealing branches excluded. -/
theorem query (env : PqxdhRecordLiftInterface.Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (route : RawCtxServerRouting.SenderDecoder) (query : PqxdhDeploymentInterface.Spec.Domain)
    (beforeP : Platform) (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n)
    (before : CtxPrivate n)
    (result : ((((PqxdhDeploymentInterface.Spec.Range query × Platform) × CborRecordWorldClient.Shell) × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n))
    (supported : result∈support ((simulateQ service (source env reserve codec route (PqxdhDeploymentInterface.Spec.query query) beforeP shell control)).run before))
    (label : Label n) (entry : CtxSuccessfulSeal)
    (absent : entry∉(before.keys label).1.successfulSeals) (present : entry∈(result.2.keys label).1.successfulSeals) :
    Nonempty (Receipt service reserve beforeP (source env reserve codec route (PqxdhDeploymentInterface.Spec.query query) beforeP shell control)
      before result label entry) := by
  rcases RegistrationNativePlatformOriginNativeTails.normalform env reserve codec route query beforeP shell control with quiet|form
  · have kept := RegistrationNativePlatformOriginSealRetention.program modes ideal replace setup codec _ quiet before result supported label
    exact (absent (kept ▸ present)).elim
  · exact envelope modes ideal replace setup codec reserve beforeP _ form before result supported label entry absent present
private theorem coins_base {X : Type} (work : ProbComp X) :
    (simulateQ (RegistrationNativePlatformOriginGateSource.coins (n := n)) work).AllQueriesSatisfy
      RegistrationNativePlatformOriginErasedFields.BaseOnly := by
  induction work using OracleComp.inductionOn with
  | pure value=>trivial
  | query_bind query next ih=>
    simp only [simulateQ_bind,simulateQ_spec_query,RegistrationNativePlatformOriginGateSource.coins,bind_assoc,
      allQueriesSatisfy_query_bind_iff]
    exact ⟨by trivial,fun _=>⟨by trivial,fun reply=>ih reply⟩⟩
private theorem continued_base (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (after : Option RawCtxSourceSend.Encrypted → Platform → A) (before : Platform)
    (tag : PqxdhDeploymentInterface.FrameTag) (reply : Option RawCtxSourceSend.Encrypted) :
    (continued (n := n) reserve (fun output state=>pure (after output state)) before tag reply).AllQueriesSatisfy
      RegistrationNativePlatformOriginErasedFields.BaseOnly := by
  unfold continued
  rw [allQueriesSatisfy_query_bind_iff]
  exact ⟨by trivial,fun _=>allQueriesSatisfy_bind (coins_base _) (fun _=>by trivial)⟩
local notation "erasedService" => PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec

/-- The named erased source retains the same exact sealing-coordinate receipt and actual reserve suffix at arbitrary reached private state. -/
theorem envelope_erased (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure)) (beforeP : Platform)
    (work : OracleComp (ServiceSpec n) A) (form : Envelope reserve beforeP work)
    (before : CtxPrivate n) (result : A × CtxPrivate n)
    (supported : result∈support ((simulateQ erasedService work).run before))
    (label : Label n) (entry : CtxSuccessfulSeal)
    (absent : entry∉(before.keys label).1.successfulSeals) (present : entry∈(result.2.keys label).1.successfulSeals) :
    Nonempty (Receipt erasedService reserve beforeP work before result label entry) := by
  obtain ⟨pending,tag,after,form⟩ := form
  have called := supported
  rw [form,simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at called
  obtain ⟨looked,lookupCalled,later⟩ := called
  rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at later
  obtain ⟨sealed,sealCalled,tailCalled⟩ := later
  have lookupKeeps := RegistrationNativePlatformOriginErasedFields.base_call modes replace setup codec
    (.lookup pending.material) (by trivial) before looked lookupCalled
  have fresh : entry∉(looked.2.keys label).1.successfulSeals := by rw [lookupKeeps];exact absent
  have tailKeeps := RegistrationNativePlatformOriginErasedFields.program modes replace setup codec _
    (continued_base reserve after beforeP tag sealed.1) sealed.2 result tailCalled
  have inserted : entry∈(sealed.2.keys label).1.successfulSeals := by rw [←tailKeeps];exact present
  have material : pending.material=label := by
    by_contra different
    have other := RegistrationNativePlatformOriginErasedFields.sealing_other modes replace setup codec pending looked.2 sealed sealCalled label (Ne.symm different)
    exact fresh ((congrArg (fun state=>state.1.successfulSeals) other) ▸ inserted)
  exact ⟨⟨pending,tag,after,form,looked,lookupCalled,sealed,sealCalled,tailCalled,material,fresh,inserted⟩⟩

include ideal in
/-- Actual acquisition under the explicitly uniform-normalized private-cache interpretation derives the full same-source receipt; the normalization law excludes the otherwise nonsealing branches. -/
theorem query_erased (env : PqxdhRecordLiftInterface.Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (route : RawCtxServerRouting.SenderDecoder) (query : PqxdhDeploymentInterface.Spec.Domain)
    (beforeP : Platform) (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n)
    (before : CtxPrivate n)
    (result : ((((PqxdhDeploymentInterface.Spec.Range query × Platform) × CborRecordWorldClient.Shell) × PqxdhRecordLiftProtocol.Control n) × CtxPrivate n))
    (supported : result∈support ((simulateQ erasedService (source env reserve codec route (PqxdhDeploymentInterface.Spec.query query) beforeP shell control)).run
      (PqxdhRecordFactsCounter.zeroCtx before)))
    (label : Label n) (entry : CtxSuccessfulSeal)
    (absent : entry∉(before.keys label).1.successfulSeals) (present : entry∈(result.2.keys label).1.successfulSeals) :
    Nonempty (Receipt erasedService reserve beforeP (source env reserve codec route (PqxdhDeploymentInterface.Spec.query query) beforeP shell control)
      (PqxdhRecordFactsCounter.zeroCtx before) result label entry) := by
  rcases RegistrationNativePlatformOriginNativeTails.normalform env reserve codec route query beforeP shell control with quiet|form
  · have kept := RegistrationNativePlatformOriginSealRetention.erased modes ideal replace setup codec _ quiet before result supported label
    exact (absent (kept ▸ present)).elim
  · exact envelope_erased modes replace setup codec reserve beforeP _ form (PqxdhRecordFactsCounter.zeroCtx before) result supported label entry absent present
include ideal in
theorem envelope_given (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure)) (beforeP : Platform)
    (work : OracleComp (ServiceSpec n) A) (pending : PqxdhRecordLiftProtocol.Sealing n)
    (tag : PqxdhDeploymentInterface.FrameTag) (after : Option RawCtxSourceSend.Encrypted → Platform → A)
    (form : work=(do
      let _ ← ((ServiceSpec n).query (.lookup pending.material) : OracleComp (ServiceSpec n) _)
      let reply ← ((ServiceSpec n).query (.sealing pending) : OracleComp (ServiceSpec n) _)
      continued reserve (fun output state=>pure (after output state)) beforeP tag reply))
    (before : CtxPrivate n) (result : A × CtxPrivate n)
    (supported : result∈support ((simulateQ service work).run before))
    (label : Label n) (entry : CtxSuccessfulSeal)
    (absent : entry∉(before.keys label).1.successfulSeals) (present : entry∈(result.2.keys label).1.successfulSeals) :
    Nonempty {receipt : Receipt service reserve beforeP work before result label entry // receipt.after=after} := by
  have called := supported
  rw [form,simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at called
  obtain ⟨looked,lookupCalled,later⟩ := called
  rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at later
  obtain ⟨sealed,sealCalled,tailCalled⟩ := later
  have lookupKeeps := (PqxdhRecordFactsOriginReceive.lookup_preserves modes replace setup codec pending.material before looked lookupCalled).1
  have fresh : entry∉(looked.2.keys label).1.successfulSeals := by rw [lookupKeeps];exact absent
  have tailKeeps := RegistrationNativePlatformOriginSealRetention.program modes ideal replace setup codec _
    (continued_quiet reserve after beforeP tag sealed.1) sealed.2 result tailCalled label
  have inserted : entry∈(sealed.2.keys label).1.successfulSeals := by rw [←tailKeeps];exact present
  have material : pending.material=label := by
    by_contra different
    have other := PqxdhRecordLiftCtxHybrid.sealing_other modes replace setup codec pending looked.2 sealed sealCalled label (Ne.symm different)
    exact fresh ((congrArg (fun state=>state.1.successfulSeals) other) ▸ inserted)
  exact ⟨⟨⟨pending,tag,after,form,looked,lookupCalled,sealed,sealCalled,tailCalled,material,fresh,inserted⟩,rfl⟩⟩

theorem envelope_erased_given (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure)) (beforeP : Platform)
    (work : OracleComp (ServiceSpec n) A) (pending : PqxdhRecordLiftProtocol.Sealing n)
    (tag : PqxdhDeploymentInterface.FrameTag) (after : Option RawCtxSourceSend.Encrypted → Platform → A)
    (form : work=(do
      let _ ← ((ServiceSpec n).query (.lookup pending.material) : OracleComp (ServiceSpec n) _)
      let reply ← ((ServiceSpec n).query (.sealing pending) : OracleComp (ServiceSpec n) _)
      continued reserve (fun output state=>pure (after output state)) beforeP tag reply))
    (before : CtxPrivate n) (result : A × CtxPrivate n)
    (supported : result∈support ((simulateQ erasedService work).run before))
    (label : Label n) (entry : CtxSuccessfulSeal)
    (absent : entry∉(before.keys label).1.successfulSeals) (present : entry∈(result.2.keys label).1.successfulSeals) :
    Nonempty {receipt : Receipt erasedService reserve beforeP work before result label entry // receipt.after=after} := by
  have called := supported
  rw [form,simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at called
  obtain ⟨looked,lookupCalled,later⟩ := called
  rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at later
  obtain ⟨sealed,sealCalled,tailCalled⟩ := later
  have lookupKeeps := RegistrationNativePlatformOriginErasedFields.base_call modes replace setup codec
    (.lookup pending.material) (by trivial) before looked lookupCalled
  have fresh : entry∉(looked.2.keys label).1.successfulSeals := by rw [lookupKeeps];exact absent
  have tailKeeps := RegistrationNativePlatformOriginErasedFields.program modes replace setup codec _
    (continued_base reserve after beforeP tag sealed.1) sealed.2 result tailCalled
  have inserted : entry∈(sealed.2.keys label).1.successfulSeals := by rw [←tailKeeps];exact present
  have material : pending.material=label := by
    by_contra different
    have other := RegistrationNativePlatformOriginErasedFields.sealing_other modes replace setup codec pending looked.2 sealed sealCalled label (Ne.symm different)
    exact fresh ((congrArg (fun state=>state.1.successfulSeals) other) ▸ inserted)
  exact ⟨⟨⟨pending,tag,after,form,looked,lookupCalled,sealed,sealCalled,tailCalled,material,fresh,inserted⟩,rfl⟩⟩


abbrev SendResult (n : Nat) (Platform : Type) :=
  ((Option RawCtxSourceSend.Encrypted × Platform) × CborRecordWorldClient.Shell) × PqxdhRecordLiftProtocol.Control n
private theorem send_form (env : PqxdhRecordLiftInterface.Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (route : RawCtxServerRouting.SenderDecoder) (handle : PqxdhDeploymentInterface.Handle) (plaintext : Pqxdh.Bytes)
    (beforeP : Platform) (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n) :
    (source env reserve codec route (PqxdhDeploymentSecrecy.send handle plaintext) beforeP shell control).AllQueriesSatisfy
      (fun request=>¬RegistrationNativePlatformOriginSourceTails.Sealing request) ∨
    RegistrationNativePlatformOriginNativeTails.ReplyEnvelope reserve beforeP
      (source env reserve codec route (PqxdhDeploymentSecrecy.send handle plaintext) beforeP shell control) := by
  cases handle with
  | peer keyId=>exact RegistrationNativePlatformOriginNativeTails.server_reply_form env reserve codec route beforeP shell control keyId plaintext
  | owner index=>exact RegistrationNativePlatformOriginNativeTails.beacon_reply_form env reserve codec route beforeP shell control index plaintext


include ideal in
/-- The actual original send receipt retains the native optional output and reached platform state exactly, beside its fixed advanced cursor and control. -/
theorem send (env : PqxdhRecordLiftInterface.Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (route : RawCtxServerRouting.SenderDecoder) (handle : PqxdhDeploymentInterface.Handle) (plaintext : Pqxdh.Bytes)
    (beforeP : Platform) (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n)
    (before : CtxPrivate n) (result : SendResult n Platform × CtxPrivate n)
    (supported : result∈support ((simulateQ service
      (source env reserve codec route (PqxdhDeploymentSecrecy.send handle plaintext) beforeP shell control)).run before))
    (label : Label n) (entry : CtxSuccessfulSeal)
    (absent : entry∉(before.keys label).1.successfulSeals) (present : entry∈(result.2.keys label).1.successfulSeals) :
    Nonempty {receipt : Receipt service reserve beforeP
      (source env reserve codec route (PqxdhDeploymentSecrecy.send handle plaintext) beforeP shell control)
      before result label entry // ∃advancedShell advancedControl,∀output reachedP,
        receipt.after output reachedP=(((output,reachedP),advancedShell),advancedControl)} := by
  rcases send_form codec env reserve route handle plaintext beforeP shell control with quiet|form
  · have kept := RegistrationNativePlatformOriginSealRetention.program modes ideal replace setup codec _ quiet before result supported label
    exact (absent (kept ▸ present)).elim
  · obtain ⟨pending,tag,advancedShell,advancedControl,form⟩ := form
    obtain ⟨⟨receipt,afterEq⟩⟩ := envelope_given modes ideal replace setup codec reserve beforeP _ pending tag
      (fun output reachedP=>(((output,reachedP),advancedShell),advancedControl)) form before result supported label entry absent present
    refine ⟨⟨receipt,advancedShell,advancedControl,?_⟩⟩
    intro output reachedP
    rw [afterEq]


include ideal in
/-- The actual normalized private-cache send receipt retains the native optional output and reached platform state exactly, beside its fixed advanced cursor and control. -/
theorem send_erased (env : PqxdhRecordLiftInterface.Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (route : RawCtxServerRouting.SenderDecoder) (handle : PqxdhDeploymentInterface.Handle) (plaintext : Pqxdh.Bytes)
    (beforeP : Platform) (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n)
    (before : CtxPrivate n) (result : SendResult n Platform × CtxPrivate n)
    (supported : result∈support ((simulateQ erasedService
      (source env reserve codec route (PqxdhDeploymentSecrecy.send handle plaintext) beforeP shell control)).run (PqxdhRecordFactsCounter.zeroCtx before)))
    (label : Label n) (entry : CtxSuccessfulSeal)
    (absent : entry∉(before.keys label).1.successfulSeals) (present : entry∈(result.2.keys label).1.successfulSeals) :
    Nonempty {receipt : Receipt erasedService reserve beforeP
      (source env reserve codec route (PqxdhDeploymentSecrecy.send handle plaintext) beforeP shell control)
      (PqxdhRecordFactsCounter.zeroCtx before) result label entry // ∃advancedShell advancedControl,∀output reachedP,
        receipt.after output reachedP=(((output,reachedP),advancedShell),advancedControl)} := by
  rcases send_form codec env reserve route handle plaintext beforeP shell control with quiet|form
  · have kept := RegistrationNativePlatformOriginSealRetention.erased modes ideal replace setup codec _ quiet before result supported label
    exact (absent (kept ▸ present)).elim
  · obtain ⟨pending,tag,advancedShell,advancedControl,form⟩ := form
    obtain ⟨⟨receipt,afterEq⟩⟩ := envelope_erased_given modes replace setup codec reserve beforeP _ pending tag
      (fun output reachedP=>(((output,reachedP),advancedShell),advancedControl)) form (PqxdhRecordFactsCounter.zeroCtx before) result supported label entry absent present
    refine ⟨⟨receipt,advancedShell,advancedControl,?_⟩⟩
    intro output reachedP
    rw [afterEq]

end BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendAcquisition

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendAcquisition.envelope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendAcquisition.envelope
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendAcquisition.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendAcquisition.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendAcquisition.envelope_erased' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendAcquisition.envelope_erased

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendAcquisition.query_erased' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendAcquisition.query_erased

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendAcquisition.envelope_given' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendAcquisition.envelope_given

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendAcquisition.envelope_erased_given' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendAcquisition.envelope_erased_given

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendAcquisition.send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendAcquisition.send

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendAcquisition.send_erased' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendAcquisition.send_erased
