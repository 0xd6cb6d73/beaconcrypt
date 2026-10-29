-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentRecords

/-! Missing native owners stutter in the actual cursor-filtered Protocol interpreter as well as the actual frontend. These concrete equations preserve the complete private interpreter state and introduce no dummy record effect or reset counter. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenMissingRecord
open PqxdhServerAuthExperiment (Codec)
open PqxdhRecordLiftInterface (WorldSpec)
variable {n : Nat} {Reader Response Secret : Type}

/-- Advancing an absent public cursor keeps the entire shell unchanged. -/
theorem cursor_missing (shell : CborRecordWorldClient.Shell) (index : Nat) (plaintext : Pqxdh.Bytes)
    (missing : shell.owners index = none) : CborRecordWorldClient.advanceOwner shell index plaintext = shell := by
  unfold CborRecordWorldClient.advanceOwner
  simp only [missing, Option.map_none]
  have same : Function.update shell.owners index none = shell.owners := by
    funext other
    by_cases equal : other = index
    · subst other
      simp only [Function.update_self, missing]
    · exact Function.update_of_ne equal _ _
  rw [same]

/-- Missing owner sends perform no Protocol service call and preserve every reached private primitive field. -/
theorem send_missing (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (index : Nat) (plaintext : Pqxdh.Bytes)
    (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n) (secret : Secret)
    (missing : control.owners[index]? = none) (cursor : shell.owners index = none) :
    CborRawRecordOriginFlatten.interpret service codec route
      ((WorldSpec n).query (.inr (.inr (.inr (index, .inl plaintext)))) : OracleComp (WorldSpec n) _)
      shell control secret = pure (((none, shell), control), secret) := by
  let request : (WorldSpec n).Domain := .inr (.inr (.inr (index, .inl plaintext)))
  have filtered : (CborRecordWorldClient.handler request).run shell =
      (fun reply => (reply, CborRecordWorldClient.next request reply shell)) <$>
        ((WorldSpec n).query request : OracleComp (WorldSpec n) _) := by
    simp only [CborRecordWorldClient.handler, StateT.run, request, CborRecordWorldClient.refusal, cursor,
      CborRecordWorldClient.forward]
  have native : (PqxdhRecordLiftProtocol.handler codec.frameRead route request).run control = pure (none, control) := by
    change (PqxdhRecordLiftProtocol.beaconStep codec.frameRead index (.inl plaintext)).run control = _
    simp only [PqxdhRecordLiftProtocol.beaconStep, StateT.run, missing, PqxdhDeploymentNative.absent]
  change CborRawRecordOriginFlatten.interpret service codec route ((WorldSpec n).query request) shell control secret = _
  unfold CborRawRecordOriginFlatten.interpret
  rw [simulateQ_spec_query, filtered]
  simp only [simulateQ_map, StateT.run_map, simulateQ_spec_query, native, map_pure, simulateQ_pure, StateT.run_pure,
    request, CborRecordWorldClient.next, cursor_missing shell index plaintext cursor]


/-- Missing owner raw receives perform no Protocol service call and preserve every counter and private cache. -/
theorem raw_missing (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (index : Nat) (raw : Pqxdh.Bytes)
    (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n) (secret : Secret)
    (missing : control.owners[index]? = none) :
    CborRawRecordOriginFlatten.interpret service codec route
      ((WorldSpec n).query (.inr (.inr (.inr (index, .inr raw)))) : OracleComp (WorldSpec n) _)
      shell control secret = pure (((.None, shell), control), secret) := by
  let request : (WorldSpec n).Domain := .inr (.inr (.inr (index, .inr raw)))
  have filtered : (CborRecordWorldClient.handler request).run shell =
      (fun reply => (reply, shell)) <$> ((WorldSpec n).query request : OracleComp (WorldSpec n) _) := by
    simp only [CborRecordWorldClient.handler, StateT.run, request, CborRecordWorldClient.refusal,
      CborRecordWorldClient.forward, CborRecordWorldClient.next]
  have native : (PqxdhRecordLiftProtocol.handler codec.frameRead route request).run control = pure (.None, control) := by
    change (PqxdhRecordLiftProtocol.beaconStep codec.frameRead index (.inr raw)).run control = _
    simp only [PqxdhRecordLiftProtocol.beaconStep, StateT.run, missing, PqxdhDeploymentNative.absent]
  change CborRawRecordOriginFlatten.interpret service codec route ((WorldSpec n).query request) shell control secret = _
  unfold CborRawRecordOriginFlatten.interpret
  rw [simulateQ_spec_query, filtered]
  simp only [simulateQ_map, StateT.run_map, simulateQ_spec_query, native, map_pure, simulateQ_pure, StateT.run_pure]


end BeaconcryptCore.Computational.RegistrationNativeHiddenMissingRecord
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenMissingRecord.cursor_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenMissingRecord.cursor_missing
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenMissingRecord.send_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenMissingRecord.send_missing
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenMissingRecord.raw_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenMissingRecord.raw_missing
