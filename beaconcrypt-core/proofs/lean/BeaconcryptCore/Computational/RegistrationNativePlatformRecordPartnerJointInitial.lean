-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointPhysical
import BeaconcryptCore.Computational.RegistrationNativeHiddenStartup
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointInitial
open PqxdhRecordLiftInterface (WorldSpec coinLift)
open RegistrationNativePlatformRecordSlotNeutral (Quiet)
variable {n : Nat} {I KemSK Reader Response Secret A : Type} {base : OracleSpec I}
variable (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
local notation "State" => RegistrationNativePlatformLorIdealPhysical.State n Secret
local notation "physical" => RegistrationNativePlatformLorIdealPhysical.implementation service codec route

private theorem cursor_quiet (work : OracleComp (WorldSpec n) A) (quiet : work.AllQueriesSatisfy Quiet)
    (ghost : RegistrationNativePlatformRecordSlotGhost.State n)
    (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n) (secret : Secret) :
    RegistrationNativePlatformRecordSlotCursor.interpret service codec route work ghost shell control secret =
      (fun result => (((result.1.1,ghost),result.1.2),result.2)) <$>
        CborRawRecordOriginFlatten.interpret service codec route work shell control secret := by
  unfold RegistrationNativePlatformRecordSlotCursor.interpret
  rw [RegistrationNativePlatformRecordSlotCursorSource.program]
  have same := RegistrationNativePlatformRecordSlotNeutral.program_quiet work quiet ghost
  change (simulateQ RegistrationNativePlatformRecordSlotGhost.handler work).run ghost=(fun value=>(value,ghost)) <$>work at same
  rw [same]
  simp only [simulateQ_map,StateT.run_map,Functor.map_map,CborRawRecordOriginFlatten.interpret]

/-- Genuine startup/coin/hash-only prefixes preserve the initial origins relation while retaining arbitrary private service and physical cache outcomes. -/
theorem quiet (work : OracleComp (WorldSpec n) A) (allowed : work.AllQueriesSatisfy Quiet)
    (before : State) (result : A × State)
    (supported : result∈support ((simulateQ physical work).run before)) :
    RegistrationNativePlatformRecordSlotControl.origins result.2.2.1=RegistrationNativePlatformRecordSlotControl.origins before.2.1 := by
  rw [RegistrationNativePlatformLorIdealPhysical.program_source,support_map] at supported
  obtain ⟨current,called,rfl⟩ := supported
  let ghost : RegistrationNativePlatformRecordSlotGhost.State n := ⟨RegistrationNativePlatformRecordSlotControl.origins before.2.1,[]⟩
  have lifted : (((current.1.1,ghost),current.1.2),current.2) ∈ support
      (RegistrationNativePlatformRecordSlotCursor.interpret service codec route work ghost before.1 before.2.1 before.2.2) := by
    rw [cursor_quiet service codec route work allowed ghost before.1 before.2.1 before.2.2,support_map]
    exact ⟨current,called,rfl⟩
  have projected := RegistrationNativePlatformRecordSlotCursor.projection service codec route work ghost before.1 before.2.1 rfl before.2.2 _ lifted
  change RegistrationNativePlatformRecordSlotGhost.slots ghost=PqxdhRecordLiftIdeal.handleSlot current.1.2 at projected
  have originsEq : ghost.origins=RegistrationNativePlatformRecordSlotControl.origins current.1.2 := by
    apply congrArg₂ PqxdhRecordLiftOrigins.Origins.mk
    · funext keyId
      exact congrFun projected (.peer keyId)
    · funext owner
      exact congrFun projected (.owner owner)
  exact originsEq.symm

private theorem coins {B : Type} (work : ProbComp B) :
    (simulateQ (coinLift (n := n)) work).AllQueriesSatisfy Quiet := by
  induction work using OracleComp.inductionOn with
  | pure value=>trivial
  | query_bind query next ih=>
    simp only [simulateQ_bind,simulateQ_spec_query,coinLift,allQueriesSatisfy_query_bind_iff]
    exact ⟨trivial,ih⟩

/-- The literal effectful source startup makes no hidden installation or owner append, including all constructor/generation failures. -/
theorem startup_quiet (setup : PqxdhServerAuthExperiment.Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64) (identity : PqxdhJointIdentity.PublicIdentity) :
    (RegistrationNativeHiddenStartup.start (n := n) setup source ensureInit identityIndex serverKeyId identity).AllQueriesSatisfy Quiet := by
  unfold RegistrationNativeHiddenStartup.start
  apply allQueriesSatisfy_bind (coins _)
  intro constructed
  cases built : constructed.1 with
  | none=>trivial
  | some created=>
    apply allQueriesSatisfy_bind (coins _)
    intro credential
    cases credential with
    | none=>trivial
    | some credential=>
      simp only [allQueriesSatisfy_query_bind_iff]
      exact ⟨trivial,fun _=>trivial⟩

/-- The actual source startup derives unchanged physical opaque origins; no initial/final slot equality is assumed. -/
theorem startup (setup : PqxdhServerAuthExperiment.Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64) (identity : PqxdhJointIdentity.PublicIdentity)
    (before : State) (result : Option (RegistrationNativeHiddenStartup.Started source) × State)
    (supported : result∈support ((simulateQ physical
      (RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId identity)).run before)) :
    RegistrationNativePlatformRecordSlotControl.origins result.2.2.1=RegistrationNativePlatformRecordSlotControl.origins before.2.1 :=
  quiet service codec route _ (startup_quiet setup source ensureInit identityIndex serverKeyId identity) before result supported
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointInitial
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointInitial.quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointInitial.quiet
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointInitial.startup_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointInitial.startup_quiet
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointInitial.startup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointInitial.startup
