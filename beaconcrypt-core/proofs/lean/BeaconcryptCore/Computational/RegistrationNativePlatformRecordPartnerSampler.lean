-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealPhysical
import BeaconcryptCore.Computational.PqxdhRecordLiftFlat
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSampler
open PqxdhRecordLiftInterface (WorldSpec coinLift)
variable {n : Nat} {Reader Response Secret A : Type}
variable (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
local notation "State" => RegistrationNativePlatformLorIdealPhysical.State n Secret
local notation "implementation" => RegistrationNativePlatformLorIdealPhysical.implementation service codec route

private theorem map_apply {T X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT T m X) (before : T) :
    (f <$> work) before=Prod.map f id <$> work before := StateT.run_map f work before

private theorem bind_apply {T X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT T m X) (next : X → StateT T m Y) (before : T) :
    (work >>= next) before=(do let result ← work before;next result.1 result.2) := rfl

private theorem lift_apply {T X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (before : T) :
    (StateT.lift work : StateT T m X) before=(fun value => (value,before)) <$>work := by
  change (work >>=fun value=>pure (value,before))=_
  exact bind_pure_comp _ _

private theorem coin_frame (coin : unifSpec.Domain) (before : State)
    (result : unifSpec.Range coin × State)
    (supported : result∈support ((simulateQ implementation (coinLift coin)).run before)) :
    result.2.1=before.1 ∧ result.2.2.1=before.2.1 := by
  simp only [coinLift,simulateQ_spec_query,RegistrationNativePlatformLorIdealPhysical.implementation,
    CborRawRecordOriginFlatten.interpret,CborRecordWorldClient.handler,CborRecordWorldClient.refusal,
    CborRecordWorldClient.forward,CborRecordWorldClient.next,simulateQ_map,simulateQ_spec_query,
    PqxdhRecordLiftProtocol.handler,PqxdhRecordLiftProtocol.effects,StateT.run,
    support_map] at supported
  obtain ⟨inner,_called,equal⟩ := supported
  subst result
  simp only [map_apply,bind_apply,lift_apply,bind_map_left,
    simulateQ_bind,simulateQ_map,simulateQ_spec_query,support_map] at _called
  obtain ⟨charged,called,rfl⟩ := _called
  rw [mem_support_bind_iff] at called
  obtain ⟨afterCharge,_charge,afterCoin⟩ := called
  rw [support_map] at afterCoin
  obtain ⟨coinResult,_coin,rfl⟩ := afterCoin
  exact ⟨rfl,rfl⟩

/-- Reduction-owned sampling preserves the exact cursor and control while retaining every physical private coin charge and warmed cache. -/
theorem frame (sample : ProbComp A) (before : State) (result : A × State)
    (supported : result∈support ((simulateQ implementation (simulateQ coinLift sample)).run before)) :
    result.2.1=before.1 ∧result.2.2.1=before.2.1 := by
  induction sample using OracleComp.inductionOn generalizing before result with
  | pure value=>
    simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
    cases supported
    exact ⟨rfl,rfl⟩
  | query_bind coin next ih=>
    simp only [simulateQ_bind,StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨middle,called,continued⟩ := supported
    have initial := coin_frame service codec route coin before middle called
    have later := ih middle.1 middle.2 result continued
    exact ⟨later.1.trans initial.1,later.2.trans initial.2⟩
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSampler
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSampler.frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSampler.frame
