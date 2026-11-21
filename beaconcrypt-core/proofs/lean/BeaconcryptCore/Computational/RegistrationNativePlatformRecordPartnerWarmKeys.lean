-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointUniform
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginErasedFields
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerWarmKeys
open PqxdhRecordLiftInterface (WorldSpec coinLift effectLift)
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode ctxInterpreter)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {I KemSK Reader Response A : Type} {base : OracleSpec I}
variable (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
local notation "service" => ctxInterpreter modes replace setup codec
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

private theorem base_call (query : PqxdhRecordLiftProtocol.Service n)
    (quiet : RegistrationNativePlatformOriginErasedFields.BaseOnly query) (before : CtxPrivate n)
    (result : (ServiceSpec n).Range query × CtxPrivate n)
    (supported : result∈support ((service query).run before)) : result.2.keys=before.keys := by
  cases query
  all_goals first
    | exact False.elim quiet
    | (simp only [ctxInterpreter,PqxdhRecordLiftIdeal.onBase,PqxdhRecordLiftProtocol.interpreter,PqxdhRecordLiftProtocol.withRecord,
        StateT.run,bind_pure_comp,Functor.map_map,support_map] at supported
       obtain ⟨inner,_called,rfl⟩ := supported
       rfl)

private theorem base_program (work : OracleComp (ServiceSpec n) A)
    (quiet : work.AllQueriesSatisfy RegistrationNativePlatformOriginErasedFields.BaseOnly)
    (before : CtxPrivate n) (result : A × CtxPrivate n)
    (supported : result∈support ((simulateQ service work).run before)) : result.2.keys=before.keys := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
    simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
    cases supported
    rfl
  | query_bind query next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at quiet
    rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨middle,called,continued⟩ := supported
    exact (ih middle.1 (quiet.2 middle.1) middle.2 result continued).trans
      (base_call modes replace setup codec query quiet.1 before middle called)

/-- The actual World constructor/coin/hash prefix leaves every local record-key entry exact, while retaining its complete physical base work. -/
theorem keys (work : OracleComp (WorldSpec n) A) (allowed : work.AllQueriesSatisfy Allowed)
    (before : State) (result : A × State)
    (supported : result∈support ((simulateQ physical work).run before)) : result.2.2.2.keys=before.2.2.keys := by
  rw [RegistrationNativePlatformLorIdealPhysical.program_source,support_map] at supported
  obtain ⟨inner,called,rfl⟩ := supported
  exact base_program modes replace setup codec _ (source_program codec route work allowed before.1 before.2.1)
    before.2.2 inner called

private theorem coins_allowed {B : Type} (sample : ProbComp B) :
    (simulateQ (coinLift (n:=n)) sample).AllQueriesSatisfy Allowed := by
  induction sample using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,coinLift,allQueriesSatisfy_query_bind_iff]
    exact ⟨.coin query,ih⟩

/-- Reduction-owned sampling keeps the original local key dictionary, including private suffix caches, nonces and seal histories. -/
theorem sampler (sample : ProbComp A) (before : State) (result : A × State)
    (supported : result∈support ((simulateQ physical (simulateQ coinLift sample)).run before)) :
    result.2.2.2.keys=before.2.2.keys :=
  keys modes replace setup codec route _ (coins_allowed _) before result supported

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

/-- Genuine startup preserves the warm local key dictionary through constructor refusals, credential generation and the actual pure full pin selection. -/
theorem startup (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (identity : PqxdhJointIdentity.PublicIdentity)
    (before : State) (result : Option (RegistrationNativeHiddenStartup.Started source) × State)
    (supported : result∈support ((simulateQ physical
      (RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId identity)).run before)) :
    result.2.2.2.keys=before.2.2.keys :=
  keys modes replace setup codec route _ (startup_allowed setup source ensureInit identityIndex serverKeyId identity) before result supported

/-- The actual sampler-reached private state is locally virgin with empty seal histories, while every genuine warm base effect is retained. -/
theorem sampler_initial (sample : ProbComp A) (sampled : A × State)
    (sampleCalled : sampled∈support ((simulateQ physical (simulateQ coinLift sample)).run
      (CborRecordWorldClient.initial,PqxdhRecordLiftProtocol.initialControl,CtxPrivate.initial))) :
    PqxdhRecordFactsPrivateCacheSource.Virgin sampled.2.2.2 [] ∧
      ∀label,(sampled.2.2.2.keys label).1.successfulSeals=[] := by
  have initialKeys := sampler modes replace setup codec route sample _ sampled sampleCalled
  constructor
  · intro label _absent
    rw [initialKeys]
    exact ⟨rfl,rfl⟩
  · intro label
    rw [initialKeys]
    rfl

/-- The same sampled-and-initialized physical run has virgin local entries and empty successful-seal histories, without resetting any warm base field. -/
theorem initialized (sample : ProbComp A) (sampled : A × State)
    (sampleCalled : sampled∈support ((simulateQ physical (simulateQ coinLift sample)).run
      (CborRecordWorldClient.initial,PqxdhRecordLiftProtocol.initialControl,CtxPrivate.initial)))
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (identity : PqxdhJointIdentity.PublicIdentity)
    (result : Option (RegistrationNativeHiddenStartup.Started source) × State)
    (startupCalled : result∈support ((simulateQ physical
      (RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId identity)).run sampled.2)) :
    PqxdhRecordFactsPrivateCacheSource.Virgin result.2.2.2 [] ∧
      ∀label,(result.2.2.2.keys label).1.successfulSeals=[] := by
  have sampledKeys := sampler modes replace setup codec route sample _ sampled sampleCalled
  have startupKeys := startup modes replace setup codec route source ensureInit identityIndex serverKeyId identity sampled.2 result startupCalled
  have initialKeys := startupKeys.trans sampledKeys
  constructor
  · intro label _absent
    rw [initialKeys]
    exact ⟨rfl,rfl⟩
  · intro label
    rw [initialKeys]
    rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerWarmKeys

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerWarmKeys.keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerWarmKeys.keys

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerWarmKeys.sampler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerWarmKeys.sampler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerWarmKeys.startup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerWarmKeys.startup

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerWarmKeys.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerWarmKeys.initialized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerWarmKeys.sampler_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerWarmKeys.sampler_initial
