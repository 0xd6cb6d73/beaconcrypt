-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSampler
import BeaconcryptCore.Computational.PqxdhKemIndCca
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureCandidateDraw
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftIdeal (CtxPrivate)
open PqxdhRecordLiftInterface (coinLift)
variable {n : Nat} {I KemSK Reader Response : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
local notation "State"=>RegistrationNativePlatformLorIdealPhysical.State n (CtxPrivate n)
local notation "physical"=>RegistrationNativePlatformLorIdealPhysical.implementation
  (PqxdhRecordLiftIdeal.ctxInterpreter (fun _=>PqxdhRecordLiftIdeal.KeyMode.random) id setup codec) codec route

def charge (before : State) : State :=
  let counts:=before.2.2.base.primitive.1
  let updated : PqxdhRecordLiftWorld.Counts:=⟨counts.uniform+1,counts.native,
    Function.update counts.effects .coin (counts.effects .coin+1)⟩
  (before.1,before.2.1,{before.2.2 with base:={before.2.2.base with primitive:=(updated,before.2.2.base.primitive.2)}})
private theorem map_apply {T X Y : Type} {m : Type→Type} [Monad m] [LawfulMonad m]
    (f : X→Y) (work : StateT T m X) (before : T) : (f <$>work) before=Prod.map f id <$>work before :=StateT.run_map f work before
private theorem bind_apply {T X Y : Type} {m : Type→Type} [Monad m]
    (work : StateT T m X) (next : X→StateT T m Y) (before : T) :
    (work>>=next) before=(do let result←work before;next result.1 result.2) :=rfl
private theorem lift_apply {T X : Type} {m : Type→Type} [Monad m] [LawfulMonad m]
    (work : m X) (before : T) : (StateT.lift work : StateT T m X) before=(fun value=>(value,before)) <$>work :=by
  change (work>>=fun value=>pure (value,before))=_
  exact bind_pure_comp _ _
/-- An actual reduction-owned coin draws its original reply and deterministically charges only the same reached physical counters. -/
theorem coin (request : unifSpec.Domain) (before : State) :
    (simulateQ physical (coinLift request)).run before=(fun reply=>(reply,charge before)) <$> (unifSpec.query request:ProbComp _) := by
  simp only [coinLift,simulateQ_spec_query,RegistrationNativePlatformLorIdealPhysical.implementation,
    CborRawRecordOriginFlatten.interpret,CborRecordWorldClient.handler,CborRecordWorldClient.refusal,
    CborRecordWorldClient.forward,CborRecordWorldClient.next,simulateQ_map,
    PqxdhRecordLiftProtocol.handler,PqxdhRecordLiftProtocol.effects,StateT.run,map_apply,bind_apply,lift_apply,
    PqxdhRecordLiftIdeal.ctxInterpreter,PqxdhRecordLiftIdeal.onBase,PqxdhRecordLiftProtocol.interpreter,
    PqxdhRecordLiftProtocol.sampled,PqxdhRecordLiftWorld.countCoin,simulateQ_bind,
    map_bind,bind_map_left,bind_pure_comp,pure_bind,Functor.map_map,map_pure,PqxdhRecordLiftInterface.effectKind,charge,Prod.map,id_eq]
private theorem byte (before : State) :
    (simulateQ physical (simulateQ coinLift ($ᵗ UInt8))).run before=(fun reply=>(reply,charge before)) <$> ($ᵗ UInt8) := by
  change (simulateQ physical (simulateQ coinLift (UInt8.ofFin <$> (unifSpec.query 255 : ProbComp (Fin 256))))).run before=(fun reply=>(reply,charge before)) <$> (UInt8.ofFin <$> (unifSpec.query 255 : ProbComp (Fin 256)))
  rw [simulateQ_map,simulateQ_map,StateT.run_map,simulateQ_spec_query,coin setup codec route]
  simp only [Functor.map_map]
def advance : Nat→State→State
  | 0=>id
  | count+1=>fun before=>charge (advance count before)
private theorem vector (count : Nat) (before : State) :
    (simulateQ physical (simulateQ coinLift (SampleableType.vector UInt8 count))).run before=
      (fun reply=>(reply,advance count before)) <$> SampleableType.vector UInt8 count := by
  induction count generalizing before with
  | zero=>simp only [SampleableType.vector,simulateQ_pure,StateT.run_pure,map_pure,advance,id_eq]
  | succ count ih=>
    simp only [SampleableType.vector,seq_eq_bind_map,bind_map_left,simulateQ_bind,simulateQ_map,StateT.run_bind,
      StateT.run_map,ih,byte setup codec route,Functor.map_map,map_bind,advance]
private theorem candidate_repr (count : Nat) : ($ᵗ (List.Vector UInt8 count))=
    (fun value:Vector UInt8 count=>(Equiv.vectorEquivFin UInt8 count).symm (arrayVectorEquivFin UInt8 count value)) <$>
      SampleableType.vector UInt8 count := by
  change (Equiv.vectorEquivFin UInt8 count).symm <$> ((arrayVectorEquivFin UInt8 count) <$> SampleableType.vector UInt8 count)=_
  rw [Functor.map_map]
/-- The actual 32-byte candidate draw is independent of its exact deterministic reached physical poststate. The full warm cache and local key table remain literal. -/
theorem draw (before : State) :
    (simulateQ physical (simulateQ coinLift ($ᵗ PqxdhKemIndCca.MlKemSharedSecret))).run before=
      (fun candidate=>(candidate,advance 32 before)) <$> ($ᵗ PqxdhKemIndCca.MlKemSharedSecret) := by
  rw [candidate_repr,simulateQ_map,simulateQ_map,StateT.run_map,vector setup codec route]
  simp only [Functor.map_map]
/-- All actual warm physical caches, local seal dictionaries, installed controls and shell fields are retained by the candidate's deterministic coin charge. -/
theorem frame (count : Nat) (before : State) :
    (advance count before).1=before.1 ∧(advance count before).2.1=before.2.1 ∧
    (advance count before).2.2.keys=before.2.2.keys ∧
    (advance count before).2.2.base.chain=before.2.2.base.chain ∧
    (advance count before).2.2.base.pending=before.2.2.base.pending ∧
    (advance count before).2.2.base.produced=before.2.2.base.produced ∧
    (advance count before).2.2.base.seeds=before.2.2.base.seeds ∧
    (advance count before).2.2.base.primitive.2=before.2.2.base.primitive.2 ∧
    (advance count before).2.2.base.primitive.1.native=before.2.2.base.primitive.1.native := by
  induction count with
  | zero=>simp only [advance,id_eq,and_self]
  | succ count ih=>simpa only [advance,charge] using ih
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureCandidateDraw
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureCandidateDraw.coin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureCandidateDraw.coin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureCandidateDraw.draw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureCandidateDraw.draw

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureCandidateDraw.frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureCandidateDraw.frame
