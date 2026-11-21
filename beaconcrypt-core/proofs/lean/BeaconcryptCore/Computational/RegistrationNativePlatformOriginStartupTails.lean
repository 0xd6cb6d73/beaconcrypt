-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeTails
import BeaconcryptCore.Computational.RegistrationNativeRecordOriginStartup
/-! The literal constructor and shared-pin hash form a zero-sealing prefix of the same source tree. Composition retains the reached CBOR cursor and record control; no warmed cache is reset. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginStartupTails
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (WorldSpec)
open RegistrationNativePlatformOriginSourceTails (HasTails)
open PqxdhRecordLiftCtxProgramBounds (Weighted)
variable {n : Nat} {Platform Failure Reader Response A B : Type}
noncomputable def compile (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp (WorldSpec n) A) (shell : CborRecordWorldClient.Shell)
    (control : PqxdhRecordLiftProtocol.Control n) :=
  (simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
    ((simulateQ CborRecordWorldClient.handler work).run shell)).run control
private theorem weighted_zero {I : Type} {spec : OracleSpec I} (cost : I → Nat)
    (work : OracleComp spec A) (bounded : Weighted cost work 0) : work.AllQueriesSatisfy (fun query=>cost query=0) := by
  induction work using OracleComp.inductionOn with
  | pure value=>trivial
  | query_bind query next ih=>
    rw [Weighted,isQueryBound_query_bind_iff] at bounded
    rw [allQueriesSatisfy_query_bind_iff]
    refine ⟨by omega,?_⟩
    intro reply
    apply ih reply
    change (next reply).IsQueryBound 0 (fun query available=>cost query≤available) (fun query available=>available-cost query)
    simpa only [Nat.zero_sub] using bounded.2 reply
private theorem seal_bill : (PqxdhRecordLiftCtxBills.worldBill .seal : (WorldSpec n).Domain → Nat)=
    fun query=>if PqxdhRecordLiftBudget.WorldRecord .send query then 1 else 0 := by
  funext query
  rcases query with created|(effect|record)
  · rfl
  · cases effect <;> rfl
  · rcases record with (send|raw)|⟨owner,plaintext|raw⟩ <;> rfl

/-- Only the actual startup request kinds are admitted, so the literal source prefix contains no hidden seal. -/
theorem quiet (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp (WorldSpec n) A) (safe : work.AllQueriesSatisfy RegistrationNativeRecordOriginStartup.Allowed)
    (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n) :
    HasTails Platform Failure (compile codec route work shell control) := by
  classical
  have absent : work.AllQueriesSatisfy (fun query=>¬PqxdhRecordLiftBudget.WorldRecord .send query) := by
    apply safe.mono
    intro query allowed
    rcases query with created|(effect|record)
    · simp [PqxdhRecordLiftBudget.WorldRecord]
    · cases effect <;> simp [PqxdhRecordLiftBudget.WorldRecord]
    · exact allowed.elim
  have cap : work.IsQueryBoundP (PqxdhRecordLiftBudget.WorldRecord .send) 0 := by
    simpa only [not_not] using (isQueryBoundP_zero_iff work (fun query=>¬PqxdhRecordLiftBudget.WorldRecord .send query)).mpr absent
  have cursor := CborRecordWorldClient.client_bound work (PqxdhRecordLiftBudget.WorldRecord .send) 0 cap shell
  simp only [CborRecordWorldClient.client,isQueryBoundP_map_iff] at cursor
  have weight := PqxdhRecordLiftCtxProgramBounds.weighted_indicator (PqxdhRecordLiftBudget.WorldRecord .send) 1 _ 0 cursor
  simp only [Nat.one_mul] at weight
  rw [←seal_bill] at weight
  have compiled := PqxdhRecordLiftCtxProgramBounds.weighted_run (PqxdhRecordLiftCtxBills.worldBill .seal)
    (PqxdhRecordLiftCtxProtocolBounds.categoryCost .seal) (PqxdhRecordLiftProtocol.handler codec.frameRead route) _ 0 control weight
      (fun query current=>PqxdhRecordLiftCtxBills.handler_categories .seal codec.frameRead route query current)
  apply RegistrationNativePlatformOriginSourceTails.zero
  apply (weighted_zero (PqxdhRecordLiftCtxProtocolBounds.categoryCost .seal) _ compiled).mono
  rintro query zero ⟨pending,equal⟩
  subst query
  change (1 : Nat)=0 at zero
  omega

/-- The genuine constructor, credential generation, Server import and actual pin hash retain the original zero-sealing syntax on every failure and success branch. -/
theorem start {I KemSK : Type} {base : OracleSpec I} (setup : Setup base KemSK)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (identity : PqxdhJointIdentity.PublicIdentity)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n) :
    HasTails Platform Failure (compile codec route
      (RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId identity) shell control) :=
  quiet codec route _ (RegistrationNativeRecordOriginStartup.allowed setup source ensureInit identityIndex serverKeyId identity) shell control

/-- The same actual World prefix composes with its own returned cursor and control, retaining every reached public startup and private service effect. -/
theorem bind (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp (WorldSpec n) A) (next : A → OracleComp (WorldSpec n) B)
    (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n)
    (first : HasTails Platform Failure (compile codec route work shell control))
    (later : ∀value reachedShell reachedControl,HasTails Platform Failure (compile codec route (next value) reachedShell reachedControl)) :
    HasTails Platform Failure (compile codec route (work >>= next) shell control) := by
  simp only [compile,simulateQ_bind,StateT.run_bind]
  exact RegistrationNativePlatformOriginSourceTails.bind _ _ first (fun result=>later result.1.1 result.1.2 result.2)
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginStartupTails

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginStartupTails.quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginStartupTails.quiet

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginStartupTails.start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginStartupTails.start

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginStartupTails.bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginStartupTails.bind
