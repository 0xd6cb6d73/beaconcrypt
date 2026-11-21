-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityMain

/-! Original CE designation can name an owner created after an acceptance. The ordinary joint reduction therefore checks every successful native accept against every final generated alias. The source interpretation treats these retrospective reports as ghost operations. A changed fixed prekey remains unissued even in the final signing history. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityFinalReports
variable {source : RegistrationNativeMldsa.Source}

def packets (wire : RegistrationNativeWire.Wire) (transcript : List RegistrationNativeInterface.Entry) :
    List beaconcrypt_core.registration.InitPacket :=
  transcript.filterMap fun entry => match entry with
    | ⟨.inl (.inr (.accept raw)), some _⟩ => RegistrationNativeWire.readInit wire raw
    | _ => none

def reports (wire : RegistrationNativeWire.Wire) (transcript : List RegistrationNativeInterface.Entry)
    (owners : RegistrationNativeIdentityFrontend.State source) : List PqxdhJointPhase1Reports.CandidateReport :=
  (packets wire transcript).flatMap fun packet => RegistrationNativeIdentityMain.reports packet owners

theorem packet_member (wire : RegistrationNativeWire.Wire) (transcript : List RegistrationNativeInterface.Entry)
    (raw : Pqxdh.Bytes) (session : Nat) (packet : beaconcrypt_core.registration.InitPacket)
    (accepted : (⟨.inl (.inr (.accept raw)), some session⟩ : RegistrationNativeInterface.Entry) ∈ transcript)
    (decoded : RegistrationNativeWire.readInit wire raw = some packet) : packet ∈ packets wire transcript := by
  exact List.mem_filterMap.mpr ⟨_, accepted, decoded⟩

theorem report_member (wire : RegistrationNativeWire.Wire) (transcript : List RegistrationNativeInterface.Entry)
    (owners : RegistrationNativeIdentityFrontend.State source) (packet : beaconcrypt_core.registration.InitPacket)
    (packetPresent : packet ∈ packets wire transcript) (report : PqxdhJointPhase1Reports.CandidateReport)
    (reported : report ∈ RegistrationNativeIdentityMain.reports packet owners) : report ∈ reports wire transcript owners :=
  List.mem_flatMap.mpr ⟨packet, packetPresent, reported⟩

end BeaconcryptCore.Computational.RegistrationNativeIdentityFinalReports

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityFinalReports.packet_member' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityFinalReports.packet_member
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityFinalReports.report_member' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityFinalReports.report_member
