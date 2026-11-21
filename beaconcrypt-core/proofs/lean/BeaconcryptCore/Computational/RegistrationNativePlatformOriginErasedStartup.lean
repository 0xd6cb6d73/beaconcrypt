-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointUniform
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginStartupTails
import BeaconcryptCore.Computational.RegistrationNativeRecordHandleSlots
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedFields
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedStartup
open PqxdhRecordLiftInterface (WorldSpec coinLift effectLift)
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode ctxInterpreter)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {I KemSK Reader Response A : Type} {base : OracleSpec I}
variable (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
local notation "service" => PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec
local notation "State" => RegistrationNativePlatformLorIdealPhysical.State n (CtxPrivate n)
local notation "physical" => RegistrationNativePlatformLorIdealPhysical.implementation service codec route

inductive Allowed : (WorldSpec n).Domain → Prop where
  | coin (coin : unifSpec.Domain) : Allowed (.inr (.inl (.inl coin)))
  | init (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) : Allowed (.inl created)
  | hash (bytes : Pqxdh.Bytes) : Allowed (.inr (.inl (.inr (.hash bytes))))

private theorem map_apply {S X Y : Type} (f : X →Y) (work : StateT S (OracleComp (ServiceSpec n)) X) (before : S) :
    (f <$>work) before=Prod.map f id <$>work before := StateT.run_map f work before
private theorem bind_apply {S X Y : Type} (work : StateT S (OracleComp (ServiceSpec n)) X)
    (next : X →StateT S (OracleComp (ServiceSpec n)) Y) (before : S) :
    (work >>=next) before=(do let result←work before;next result.1 result.2) := rfl
private theorem lift_apply {S X : Type} (work : OracleComp (ServiceSpec n) X) (before : S) :
    (StateT.lift work : StateT S (OracleComp (ServiceSpec n)) X) before=(fun value=>(value,before)) <$>work := by
  exact bind_pure_comp _ _

private theorem query_source (query : (WorldSpec n).Domain) (allowed : Allowed query)
    (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n) :
    ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
      ((simulateQ CborRecordWorldClient.handler ((WorldSpec n).query query : OracleComp (WorldSpec n) _)).run shell)).run control).AllQueriesSatisfy
      RegistrationNativePlatformOriginErasedFields.BaseOnly := by
  cases allowed
  all_goals
    simp only [simulateQ_spec_query,CborRecordWorldClient.handler,CborRecordWorldClient.refusal,
      CborRecordWorldClient.forward,CborRecordWorldClient.next,simulateQ_map,simulateQ_spec_query,
      PqxdhRecordLiftProtocol.handler,PqxdhRecordLiftProtocol.effects,StateT.run]
  case coin coin =>
    simp only [map_apply,bind_apply,lift_apply,map_eq_bind_pure_comp,bind_assoc,
      allQueriesSatisfy_query_bind_iff]
    exact ⟨by trivial,fun _ => ⟨by trivial,fun _ => by trivial⟩⟩
  case hash bytes =>
    simp only [PqxdhRecordLiftProtocol.capability,map_apply,bind_apply,lift_apply,
      map_eq_bind_pure_comp,bind_assoc,allQueriesSatisfy_query_bind_iff]
    exact ⟨by trivial,fun _ => ⟨by trivial,fun _ => by trivial⟩⟩
  case init created =>
    cases existing : control.server <;> simp [map_apply,PqxdhRecordLiftProtocol.initializeServer,existing]

private theorem source_program (work : OracleComp (WorldSpec n) A) (allowed : work.AllQueriesSatisfy Allowed)
    (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n) :
    ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
      ((simulateQ CborRecordWorldClient.handler work).run shell)).run control).AllQueriesSatisfy
      RegistrationNativePlatformOriginErasedFields.BaseOnly := by
  induction work using OracleComp.inductionOn generalizing shell control with
  | pure value => simp only [simulateQ_pure,StateT.run_pure,allQueriesSatisfy_pure]
  | query_bind query next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at allowed
    simp only [simulateQ_bind,StateT.run_bind]
    apply allQueriesSatisfy_bind (query_source codec route query allowed.1 shell control)
    rintro ⟨⟨value,nextShell⟩,nextControl⟩
    exact ih value (allowed.2 value) nextShell nextControl

private theorem coins_allowed {B : Type} (sample : ProbComp B) :
    (simulateQ (coinLift (n:=n)) sample).AllQueriesSatisfy Allowed := by
  induction sample using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,coinLift,allQueriesSatisfy_query_bind_iff]
    exact ⟨.coin query,ih⟩

private theorem startup_allowed (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64) (identity : PqxdhJointIdentity.PublicIdentity) :
    (RegistrationNativeHiddenStartup.start (n:=n) setup source ensureInit identityIndex serverKeyId identity).AllQueriesSatisfy Allowed := by
  unfold RegistrationNativeHiddenStartup.start
  apply allQueriesSatisfy_bind (coins_allowed _)
  intro constructed
  cases built : constructed.1 with
  | none => trivial
  | some created =>
    apply allQueriesSatisfy_bind (coins_allowed _)
    intro credential
    cases credential with
    | none => trivial
    | some credential =>
      simp only [allQueriesSatisfy_query_bind_iff]
      exact ⟨.init _,fun _ => by trivial⟩


/-- The literal startup contains only base services, before either success or refusal and through the pure full pin selection. -/
theorem compiled (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (identity : PqxdhJointIdentity.PublicIdentity)
    (shell : CborRecordWorldClient.Shell) (control : PqxdhRecordLiftProtocol.Control n) :
    (RegistrationNativePlatformOriginStartupTails.compile codec route
      (RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId identity) shell control).AllQueriesSatisfy
        RegistrationNativePlatformOriginErasedFields.BaseOnly :=
  source_program codec route _ (startup_allowed setup source ensureInit identityIndex serverKeyId identity) shell control

/-- The actual erased startup retains every warm local record entry and derives source Protocol safety internally. -/
theorem facts (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (identity : PqxdhJointIdentity.PublicIdentity)
    (start : CtxPrivate n)
    (result : ((Option (RegistrationNativeHiddenStartup.Started source)×CborRecordWorldClient.Shell)×PqxdhRecordLiftProtocol.Control n)×CtxPrivate n)
    (supported : result∈support ((simulateQ service (RegistrationNativePlatformOriginStartupTails.compile codec route
      (RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId identity)
      CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl)).run start)) :
    PqxdhRecordLiftProtocolHistory.Safe result.1.2 ∧result.2.keys=start.keys := by
  constructor
  · exact (RegistrationNativeRecordHandleSlots.interpreted service codec route _ CborRecordWorldClient.initial
      PqxdhRecordLiftProtocol.initialControl PqxdhRecordLiftProtocolHistory.initial_safe start result supported).1
  · exact RegistrationNativePlatformOriginErasedFields.program modes replace setup codec _
      (compiled setup codec route source ensureInit identityIndex serverKeyId identity CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl)
      start result supported
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedStartup
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedStartup.compiled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedStartup.compiled
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedStartup.facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedStartup.facts
