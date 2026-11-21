-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRecordHiddenInstall

/-! The actual cursor-aware interpreted World exposes successful hidden installation and exact origin persistence for either physical role. The private service is arbitrary; only literal supported source operations and reached states are used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeRecordHiddenWorld
open PqxdhRecordLiftInterface (WorldSpec EnvEffects Slot PeerBinding BeaconShell effectLift)
open PqxdhRecordLiftProtocol (Control)
variable {n : Nat} {Reader Response Secret Value : Type}

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := by
  change (work before >>= fun result => pure (observe result.1, result.2)) = _
  rw [bind_pure_comp]
  rfl

/-- The real cursor forwards the same administrative reply and Protocol poststate after its genuine charge. -/
theorem effect_source (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (query : (EnvEffects n).Domain) (shell : CborRecordWorldClient.Shell) (before : Control n) (secret : Secret)
    (result : (((EnvEffects n).Range query × CborRecordWorldClient.Shell) × Control n) × Secret)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret service codec route (effectLift query) shell before secret)) :
    (result.1.1.1, result.1.2) ∈ support ((PqxdhRecordLiftProtocol.effects query).run before) := by
  have original : result.1 ∈ support
      ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
        ((simulateQ CborRecordWorldClient.handler (effectLift query)).run shell)).run before) := by
    apply OracleComp.support_simulateQ_run'_subset service _ secret
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst supported
  simp only [effectLift, simulateQ_spec_query, CborRecordWorldClient.handler, StateT.run,
    CborRecordWorldClient.refusal, CborRecordWorldClient.forward,
    simulateQ_map, state_map_apply, Prod.map_def, id_eq] at original
  change result.1 ∈ support ((fun reached => ((reached.1,
    CborRecordWorldClient.next (.inr (.inl query)) reached.1 shell), reached.2)) <$>
    (PqxdhRecordLiftProtocol.effects query).run before) at original
  rw [support_map] at original
  obtain ⟨reached, called, returned⟩ := original
  have equal : reached = (result.1.1.1, result.1.2) := congrArg (fun value => (value.1.1, value.2)) returned
  rw [← equal]
  exact called

private theorem uncharge (query : (PqxdhRecordLiftInterface.CapabilitySpec n).Domain) (before after : Control n)
    (reply : (PqxdhRecordLiftInterface.CapabilitySpec n).Range query)
    (supported : (reply, after) ∈ support ((PqxdhRecordLiftProtocol.effects (.inr query)).run before)) :
    (reply, after) ∈ support ((PqxdhRecordLiftProtocol.capability query).run before) := by
  simp only [PqxdhRecordLiftProtocol.effects, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨charged, reached, continued⟩ := supported
  have same := PqxdhRecordLiftProtocolHistory.lift_control (.charge (PqxdhRecordLiftInterface.effectKind (.inr query))) before charged reached
  rw [same] at continued
  exact continued

/-- Successful actual cursor-aware Server installation stores its exact hidden slot. -/
theorem server (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (keyId : U64) (binding : PeerBinding) (slot : Slot n)
    (shell : CborRecordWorldClient.Shell) (before : Control n) (secret : Secret)
    (result : ((Bool × CborRecordWorldClient.Shell) × Control n) × Secret)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret service codec route
      (effectLift (.inr (.installServer keyId binding (.hidden slot)))) shell before secret))
    (success : result.1.1.1 = true) : PqxdhRecordLiftIdeal.handleSlot result.1.2 (.peer keyId) = some slot := by
  have original := effect_source service codec route (.inr (.installServer keyId binding (.hidden slot))) shell before secret result supported
  rw [success] at original
  exact RegistrationNativeRecordHiddenInstall.server keyId binding slot before result.1.2
    (uncharge (.installServer keyId binding (.hidden slot)) before result.1.2 true original)

/-- Successful actual cursor-aware Beacon installation stores its exact hidden slot at the physical owner. -/
theorem beacon (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (owner : Nat) (beacon : BeaconShell) (slot : Slot n)
    (shell : CborRecordWorldClient.Shell) (before : Control n) (secret : Secret)
    (result : ((Bool × CborRecordWorldClient.Shell) × Control n) × Secret)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret service codec route
      (effectLift (.inr (.installBeacon owner beacon (.hidden slot)))) shell before secret))
    (success : result.1.1.1 = true) : PqxdhRecordLiftIdeal.handleSlot result.1.2 (.owner owner) = some slot := by
  have original := effect_source service codec route (.inr (.installBeacon owner beacon (.hidden slot))) shell before secret result supported
  rw [success] at original
  exact RegistrationNativeRecordHiddenInstall.beacon owner beacon slot before result.1.2
    (uncharge (.installBeacon owner beacon (.hidden slot)) before result.1.2 true original)

end BeaconcryptCore.Computational.RegistrationNativeRecordHiddenWorld

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordHiddenWorld.effect_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordHiddenWorld.effect_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordHiddenWorld.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordHiddenWorld.server
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordHiddenWorld.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordHiddenWorld.beacon
