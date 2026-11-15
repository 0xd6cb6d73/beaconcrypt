-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordOriginFlatten

/-! Actual startup and Server installation derive safe control before the original secrecy ledger begins. These facts interpret the concrete cursor and Protocol programs and retain arbitrary private state. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawRecordOriginStartup
open PqxdhRecordLiftInterface (Environment)
open PqxdhRecordLiftProtocol (ServiceSpec Control)
open PqxdhRecordLiftProtocolHistory (Safe)
open PqxdhServerAuthExperiment (Codec)
open CborRawRecordOriginFlatten (startup install interpret)
variable {n : Nat} {Reader Response E S : Type}

private abbrev RecordAd := Aeneas.Std.Array Aeneas.Std.U8 151#usize

/-- Every actual startup result has safe compiled record control, independently of private service answers. -/
theorem startup_safe (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (env : Environment n E) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (secret : S)
    (result : (((Option (PqxdhLiveServerConstruction.Created RecordAd × E) × CborRecordWorldClient.Shell) × Control n) × S))
    (supported : result ∈ support (startup service env codec route secret)) : Safe result.1.2 :=
  (PqxdhRecordLiftProtocolHistory.interpreted_schedule service codec.frameRead route _ _
    PqxdhRecordLiftProtocolHistory.initial_safe secret result supported).1

/-- Actual cursor-aware Server installation preserves the safe reached control with complete private state retained. -/
theorem install_safe (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (created : PqxdhLiveServerConstruction.Created RecordAd) (shell : CborRecordWorldClient.Shell)
    (control : Control n) (safe : Safe control) (secret : S)
    (result : (CborRecordWorldClient.Shell × Control n) × S)
    (supported : result ∈ support (install service codec route created shell control secret)) : Safe result.1.2 := by
  rw [install, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact (PqxdhRecordLiftProtocolHistory.interpreted_schedule service codec.frameRead route _ control safe secret inner reached).1

end BeaconcryptCore.Computational.CborRawRecordOriginStartup

/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginStartup.startup_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginStartup.startup_safe
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginStartup.install_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginStartup.install_safe
