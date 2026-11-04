-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxFree
import BeaconcryptCore.Computational.RegistrationAuthenticationHashBounds
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
/-! Explicit request-class bills for the literal corrected OPEN accept syntax. Counts cover every optional/failure branch and the real public reservation. No admission, successful allocation, old-controller equality or whole-frame allowance is assumed. -/
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxBounds
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (EffectKind effectKind)
open RegistrationNativePlatformServerOpenSyntax (Spec protocol reserve)
open RegistrationNativePlatformServerReferenceAccept (PublicM)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

inductive Kind where
  | prepare | coin | hash | admin | encapsulation | reserve | other
  deriving DecidableEq

def protocolKind : (RegistrationNativeKemReferenceCompiler.Spec n KemSK).Domain → Kind
  | .inl _ => .prepare
  | .inr (.inl (.inl _)) | .inr (.inl (.inr (.inl _))) => .other
  | .inr (.inl (.inr (.inr query))) => match effectKind query with
      | .coin => .coin
      | .hash => .hash
      | .administrative => .admin
  | .inr (.inr (.inr (.inr _))) => .encapsulation
  | .inr (.inr _) => .other

def queryKind : (Spec n KemSK).Domain → Kind
  | .inl query => protocolKind (n := n) (KemSK := KemSK) query
  | .inr _ => .reserve

def cap : Kind → Nat
  | .prepare | .encapsulation | .reserve => 1
  | .coin => 32
  | .hash => 4
  | .admin | .other => 0

def prefixCap : Kind → Nat
  | .coin => 32
  | .encapsulation => 1
  | _ => 0

def sourceCost {Reader E : Type} (kind : Kind) : PqxdhServerRootPreparation.Query Reader E → Nat
  | .generate => if kind = .coin then 32 else 0
  | .encapsulate _ => if kind = .encapsulation then 1 else 0
  | _ => 0

private theorem lower_weighted {I J State A : Type} {queries : OracleSpec I} {target : OracleSpec J}
    (selected : J → Prop) [DecidablePred selected] (cost : I → Nat)
    (implementation : QueryImpl queries (StateT State (OracleComp target)))
    (step : ∀ query state, ((implementation query).run state).IsQueryBoundP selected (cost query))
    (work : OracleComp queries A) (budget : Nat)
    (bounded : work.IsQueryBound budget (fun query remaining => cost query ≤ remaining) (fun query remaining => remaining - cost query))
    (before : State) : ((simulateQ implementation work).run before).IsQueryBoundP selected budget := by
  induction work using OracleComp.inductionOn generalizing budget before with
  | pure value => trivial
  | query_bind query next ih =>
    rw [isQueryBound_query_bind_iff] at bounded
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    have tail : ∀ reply ∈ support ((implementation query).run before),
        ((simulateQ implementation (next reply.1)).run reply.2).IsQueryBoundP selected (budget - cost query) := by
      intro reply _
      exact ih reply.1 _ (bounded.2 reply.1) reply.2
    exact (isQueryBoundP_bind (step query before) tail).mono (by have := bounded.1; omega)

theorem source_prefix_bound {Reader E Shared : Type} (kind : Kind) (verified : PqxdhServerRootPreparation.Verified Reader) :
    (PqxdhServerRootPreparation.collectVerified (E := E) (Shared := Shared) verified).IsQueryBound (prefixCap kind)
      (fun query remaining => sourceCost kind query ≤ remaining)
      (fun query remaining => remaining - sourceCost kind query) := by
  cases kind <;> unfold PqxdhServerRootPreparation.collectVerified
  all_goals simp only [OptionT.run_bind, OptionT.run_monadLift, Option.elimM, bind_map_left]
  all_goals repeat' first
    | trivial
    | rw [isQueryBound_query_bind_iff]
    | constructor
    | intro answer; cases answer

attribute [local irreducible] PqxdhJointGapDh.sampleScalar

private theorem generated_bound (setup : Setup base KemSK) :
    (PqxdhServerAuthExperiment.generateEphemeral setup).IsTotalQueryBound 32 := by
  unfold PqxdhServerAuthExperiment.generateEphemeral
  apply isTotalQueryBound_bind (n₁ := 32) (n₂ := 0) PqxdhJointGapDh.sampleScalar_uniform
  intro secret
  trivial

attribute [local irreducible] PqxdhServerAuthExperiment.generateEphemeral RegistrationAgreementShared.rootResponse

private theorem ordinary_primitive_bound (setup : Setup base KemSK) (checks : Checks)
    (request : RegistrationAgreementExecutor.Request) (state : RegistrationServerRoleBackend.State)
    (notEncap : RegistrationNativeKemReferenceCompiler.NonEncapsulation request) :
    ((RegistrationAgreementShared.auxiliary setup.source (RegistrationServerRoleBackend.localBackend setup checks) request).run state).IsTotalQueryBound
      (match request with | .generate _ => 32 | _ => 0) := by
  cases request with
  | encapsulate key => exact False.elim notEncap
  | generate role =>
    cases role
    simpa only [RegistrationAgreementShared.auxiliary, RegistrationServerRoleBackend.localBackend,
      StateT.run, IsTotalQueryBound, isQueryBound_map_iff] using generated_bound setup
  | convertPublic key =>
    simp only [RegistrationAgreementShared.auxiliary, RegistrationServerRoleBackend.localBackend, StateT.run_pure]
    trivial
  | convertSecret role =>
    cases role <;> simp only [RegistrationAgreementShared.auxiliary, RegistrationServerRoleBackend.localBackend, StateT.run_pure] <;> trivial
  | decapsulate ciphertext =>
    simp only [RegistrationAgreementShared.auxiliary, RegistrationServerRoleBackend.localBackend, StateT.run_pure]
    trivial
  | dh request => cases role : request.secret_role <;> simp only [RegistrationAgreementShared.auxiliary,
      RegistrationServerRoleBackend.localBackend, role, StateT.run] <;> trivial
  | root request =>
    simp only [RegistrationAgreementShared.auxiliary, StateT.run_pure]
    trivial

def effectMatches (kind : Kind) (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) : Prop :=
  match kind with
  | .coin => effectKind query = .coin
  | .hash => effectKind query = .hash
  | .admin => effectKind query = .administrative
  | _ => False
instance (kind : Kind) : DecidablePred (effectMatches (n := n) kind) := fun query => by
  cases kind <;> dsimp [effectMatches] <;> infer_instance

private theorem env_forward (kind : Kind) (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value)
    (budget : Nat) (bounded : work.IsQueryBoundP (effectMatches kind) budget) :
    (simulateQ (RegistrationNativeKemReferenceCompiler.lift (KemSK := KemSK))
      (simulateQ RegistrationServerReferenceCompiler.effect work)).IsQueryBoundP
        (fun query => protocolKind (n := n) (KemSK := KemSK) query = kind) budget := by
  rw [← QueryImpl.simulateQ_compose]
  apply RawCtxSourceOpen.simulate_bound _ (effectMatches kind) _ work budget bounded
  intro query
  cases kind <;> cases actual : effectKind query <;>
    simp [QueryImpl.apply_compose, RegistrationServerReferenceCompiler.effect, RegistrationNativeKemReferenceCompiler.lift,
      protocolKind, effectMatches, actual, isQueryBoundP_query_iff]

private theorem ordinary_backend_bound (setup : Setup base KemSK) (checks : Checks)
    (request : RegistrationAgreementExecutor.Request) (before : RegistrationServerReferenceCompiler.Environment)
    (notEncap : RegistrationNativeKemReferenceCompiler.NonEncapsulation request) (kind : Kind) :
    ((RegistrationNativeKemReferenceCompiler.backend (n := n) setup checks request).run before).IsQueryBoundP
      (fun query => protocolKind (n := n) (KemSK := KemSK) query = kind)
      (if kind = .coin then (match request with | .generate _ => 32 | _ => 0) else 0) := by
  rw [RegistrationNativeKemReferenceCompiler.backend_ordinary setup checks request notEncap]
  change (simulateQ RegistrationNativeKemReferenceCompiler.lift (simulateQ RegistrationServerReferenceCompiler.effect
    ((RegistrationWorldAgreementCompiler.compiler setup.source (RegistrationServerRoleBackend.localBackend setup checks) request).run before))).IsQueryBoundP _ _
  apply env_forward
  have draws := ordinary_primitive_bound setup checks request before.auxiliary notEncap
  cases kind with
  | coin =>
    apply OracleComp.IsQueryBoundP.of_imp (p' := fun effect => effectKind effect = .coin) (fun _ present => present)
    exact RegistrationWorldAgreementCompiler.query_bound setup.source (RegistrationServerRoleBackend.localBackend setup checks) request before _ draws .coin
  | hash =>
    apply OracleComp.IsQueryBoundP.of_imp (p' := fun effect => effectKind effect = .hash) (fun _ present => present)
    exact RegistrationWorldAgreementCompiler.query_bound setup.source (RegistrationServerRoleBackend.localBackend setup checks) request before _ draws .hash
  | admin =>
    apply OracleComp.IsQueryBoundP.of_imp (p' := fun effect => effectKind effect = .administrative) (fun _ present => present)
    exact RegistrationWorldAgreementCompiler.query_bound setup.source (RegistrationServerRoleBackend.localBackend setup checks) request before _ draws .administrative
  | prepare | encapsulation | reserve | other => exact isQueryBoundP_false _ 0

def backendCost (kind : Kind) : RegistrationAgreementExecutor.Request → Nat
  | .generate _ => if kind = .coin then 32 else 0
  | .encapsulate _ => if kind = .encapsulation then 1 else 0
  | _ => 0

private theorem backend_bound (setup : Setup base KemSK) (checks : Checks)
    (request : RegistrationAgreementExecutor.Request) (before : RegistrationServerReferenceCompiler.Environment) (kind : Kind) :
    ((RegistrationNativeKemReferenceCompiler.backend (n := n) setup checks request).run before).IsQueryBoundP
      (fun query => protocolKind (n := n) (KemSK := KemSK) query = kind) (backendCost kind request) := by
  cases request with
  | encapsulate key =>
    simp only [RegistrationNativeKemReferenceCompiler.backend, StateT.run, isQueryBoundP_map_iff]
    cases key with
    | none => trivial
    | some key =>
      simp only [RegistrationNativeKemInterface.server]
      split
      · cases kind <;> simp [RegistrationNativeKemInterface.encapsulate, RegistrationBeaconReferenceCompiler.indexed,
          simulateQ_map, isQueryBoundP_query_iff, protocolKind, backendCost]
      · trivial
  | generate role => exact ordinary_backend_bound (n := n) setup checks (.generate role) before (by trivial) kind
  | convertPublic key => simpa only [backendCost, ite_self] using ordinary_backend_bound (n := n) setup checks (.convertPublic key) before (by trivial) kind
  | convertSecret role => simpa only [backendCost, ite_self] using ordinary_backend_bound (n := n) setup checks (.convertSecret role) before (by trivial) kind
  | decapsulate ciphertext => simpa only [backendCost, ite_self] using ordinary_backend_bound (n := n) setup checks (.decapsulate ciphertext) before (by trivial) kind
  | dh request => simpa only [backendCost, ite_self] using ordinary_backend_bound (n := n) setup checks (.dh request) before (by trivial) kind
  | root request => simpa only [backendCost, ite_self] using ordinary_backend_bound (n := n) setup checks (.root request) before (by trivial) kind

attribute [local irreducible] RegistrationNativeKemReferenceCompiler.backend

private theorem prefix_step_bound (setup : Setup base KemSK) (checks : Checks) (kind : Kind)
    (request : PqxdhServerRootPreparation.Query registration.InitPacket Unit)
    (before : RegistrationServerReferenceCompiler.Environment) :
    ((PqxdhServerStaticDhSource.prefixImpl setup.serverDomain
      (RegistrationAgreementInterpreter.prepImpl (RegistrationNativeKemReferenceCompiler.backend (n := n) setup checks))
      RegistrationNativeKemReferenceCompiler.visit request).run before).IsQueryBoundP
        (fun query => protocolKind (n := n) (KemSK := KemSK) query = kind) (sourceCost kind request) := by
  cases request <;> simp only [PqxdhServerStaticDhSource.prefixImpl, RegistrationAgreementInterpreter.prepImpl,
    RegistrationAgreementRoot.callbacks, simulateQ_pure, simulateQ_map, simulateQ_spec_query,
    StateT.run_pure, StateT.run_map, isQueryBoundP_map_iff]
  all_goals first
    | trivial
    | exact backend_bound setup checks _ before kind

theorem collect_bound (setup : Setup base KemSK) (checks : Checks) (kind : Kind)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationServerReferenceCompiler.Environment) :
    ((RegistrationNativeKemReferenceCompiler.collect (n := n) setup checks packet authenticated).run before).IsQueryBoundP
      (fun query => protocolKind (n := n) (KemSK := KemSK) query = kind) (prefixCap kind) :=
  lower_weighted _ (sourceCost kind) _ (prefix_step_bound setup checks kind) _ _
    (source_prefix_bound kind (RegistrationRootInput.verified packet authenticated)) before

private theorem protocol_forward (kind : Kind) (work : OracleComp (RegistrationNativeKemReferenceCompiler.Spec n KemSK) Value)
    (budget : Nat) (bounded : work.IsQueryBoundP (fun query => protocolKind (n := n) (KemSK := KemSK) query = kind) budget) :
    (simulateQ protocol work).IsQueryBoundP (fun query => queryKind (n := n) (KemSK := KemSK) query = kind) budget := by
  apply RawCtxSourceOpen.simulate_bound _ (fun query => protocolKind (n := n) (KemSK := KemSK) query = kind) _ work budget bounded
  intro query
  simp only [protocol, isQueryBoundP_query_iff, queryKind]
  intro present
  simp only [present, ite_true]
  omega

private theorem effects_forward (kind : Kind) (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value)
    (budget : Nat) (bounded : work.IsQueryBoundP (effectMatches kind) budget) :
    (simulateQ (RegistrationNativePlatformServerOpenControl.effects (protocol (n := n) (KemSK := KemSK))) work).IsQueryBoundP
      (fun query => queryKind (n := n) (KemSK := KemSK) query = kind) budget := by
  apply RawCtxSourceOpen.simulate_bound _ (effectMatches kind) _ work budget bounded
  intro query
  cases kind <;> cases actual : effectKind query <;>
    simp [RegistrationNativePlatformServerOpenControl.effects, QueryImpl.compose, protocol,
      RegistrationBeaconReferenceCompiler.effect, queryKind, protocolKind, effectMatches, actual, isQueryBoundP_query_iff]

private theorem hash_callback_bound (kind : Kind) (request : registration.HashRequest) :
    (RegistrationNativePlatformServerReferenceAccept.hash
      (RegistrationNativePlatformServerOpenControl.effects (protocol (n := n) (KemSK := KemSK))) request).IsQueryBoundP
      (fun query => queryKind (n := n) (KemSK := KemSK) query = kind) (if kind = .hash then 1 else 0) := by
  simp only [RegistrationNativePlatformServerReferenceAccept.hash, bind_pure_comp, isQueryBoundP_map_iff]
  cases kind <;> simp [RegistrationNativePlatformServerOpenControl.effects, QueryImpl.apply_compose,
    RegistrationBeaconReferenceCompiler.effect, protocol, queryKind, protocolKind, effectKind, isQueryBoundP_query_iff]

theorem pin_bound (kind : Kind) (current : session.ServerAuthenticationPin) :
    (RegistrationNativePlatformServerReferenceAccept.pin
      (RegistrationNativePlatformServerOpenControl.effects (protocol (n := n) (KemSK := KemSK))) current).IsQueryBoundP
      (fun query => queryKind (n := n) (KemSK := KemSK) query = kind) (if kind = .hash then 1 else 0) := by
  unfold RegistrationNativePlatformServerReferenceAccept.pin RegistrationNativeServerPinRecompute.program
  simp only [bind_pure_comp]
  exact hash_callback_bound (n := n) (KemSK := KemSK) kind _

attribute [local irreducible] RegistrationAuthenticationCompiler.program

theorem authentication_bound (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) (kind : Kind) :
    (simulateQ (RegistrationNativePlatformServerOpenControl.effects (protocol (n := n) (KemSK := KemSK)))
      (RegistrationAuthenticationCompiler.program crypto verify pin packet)).IsQueryBoundP
        (fun query => queryKind (n := n) (KemSK := KemSK) query = kind) (if kind = .hash then 3 else 0) := by
  refine effects_forward (n := n) (KemSK := KemSK) kind
    (RegistrationAuthenticationCompiler.program crypto verify pin packet)
    (if kind = .hash then 3 else 0) ?_
  cases kind with
  | coin =>
    apply OracleComp.IsQueryBoundP.of_imp (p' := fun effect => effectKind effect = .coin) (fun _ present => present)
    exact RegistrationAuthenticationHashBounds.program_bound crypto verify pin packet .coin
  | hash =>
    apply OracleComp.IsQueryBoundP.of_imp (p' := fun effect => effectKind effect = .hash) (fun _ present => present)
    exact RegistrationAuthenticationHashBounds.program_bound crypto verify pin packet .hash
  | admin =>
    apply OracleComp.IsQueryBoundP.of_imp (p' := fun effect => effectKind effect = .administrative) (fun _ present => present)
    exact RegistrationAuthenticationHashBounds.program_bound crypto verify pin packet .administrative
  | prepare | encapsulation | reserve | other => exact isQueryBoundP_false _ 0

private theorem prepare_bound (kind : Kind) (binding : session.RegistrationBinding)
    (input : PqxdhServerRootPreparation.Inputs registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding) :
    (simulateQ (RegistrationBeaconReferenceCompiler.prepare (n := n) (KemSK := KemSK))
      (RegistrationServerReferenceRoot.client binding input)).IsQueryBoundP
      (fun query => protocolKind (n := n) (KemSK := KemSK) query = kind) (if kind = .prepare then 1 else 0) := by
  classical
  unfold RegistrationServerReferenceRoot.client
  split
  · trivial
  · cases kind <;> simp [RegistrationBeaconReferenceCompiler.prepare, protocolKind]

private theorem lift_bound (kind : Kind) (work : OracleComp (Spec n KemSK) Value) (budget : Nat)
    (bounded : work.IsQueryBoundP (fun query => queryKind (n := n) (KemSK := KemSK) query = kind) budget)
    (before : RegistrationServerMaterialFrontend.State) (env : RegistrationServerReferenceCompiler.Environment) :
    (((StateT.lift (StateT.lift work) : PublicM (OracleComp (Spec n KemSK)) Value).run before).run env).IsQueryBoundP
      (fun query => queryKind (n := n) (KemSK := KemSK) query = kind) budget := by
  simpa only [StateT.run_lift, bind_pure_comp, StateT.run_map, isQueryBoundP_map_iff] using bounded

private theorem retain_bound (kind : Kind) (ready : RegistrationServerReferenceRoot.Ready)
    (before : RegistrationServerMaterialFrontend.State) (env : RegistrationServerReferenceCompiler.Environment) (budget : Nat) :
    (((RegistrationNativePlatformServerReferenceAccept.retain ready : PublicM (OracleComp (Spec n KemSK)) _).run before).run env).IsQueryBoundP
      (fun query => queryKind (n := n) (KemSK := KemSK) query = kind) budget := by
  dsimp only [RegistrationNativePlatformServerReferenceAccept.retain, StateT.run]
  cases current : RegistrationServerMaterialFrontend.retain ready before <;> trivial

def agreementCap (kind : Kind) : Nat := prefixCap kind + if kind = .prepare then 1 else 0

attribute [local irreducible] RegistrationNativeKemReferenceCompiler.collect RegistrationServerReferenceRoot.client

theorem agreement_bound (setup : Setup base KemSK) (checks : Checks) (kind : Kind)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationServerMaterialFrontend.State) (env : RegistrationServerReferenceCompiler.Environment) :
    (((RegistrationNativePlatformServerOpenKernel.agreement (protocol (n := n)) setup checks packet authenticated).run before).run env).IsQueryBoundP
      (fun query => queryKind (n := n) (KemSK := KemSK) query = kind) (agreementCap kind) := by
  change (simulateQ protocol (((RegistrationServerOpenReferenceCompiler.agreement setup checks packet authenticated).run before).run env)).IsQueryBoundP _ _
  apply protocol_forward
  simp only [RegistrationServerOpenReferenceCompiler.agreement, StateT.run_bind, StateT.run_lift,
    bind_pure_comp, bind_map_left]
  apply isQueryBoundP_bind (collect_bound setup checks kind packet authenticated env)
  rintro ⟨input, currentEnv⟩ _
  cases input with
  | none => trivial
  | some input =>
    simpa only [StateT.run_lift, bind_pure_comp, StateT.run_map, isQueryBoundP_map_iff] using prepare_bound (n := n) (KemSK := KemSK) kind authenticated.binding input

private theorem public_bind_bound {Next : Type} (kind : Kind)
    (work : PublicM (OracleComp (Spec n KemSK)) Value)
    (next : Value → PublicM (OracleComp (Spec n KemSK)) Next)
    (before : RegistrationServerMaterialFrontend.State) (env : RegistrationServerReferenceCompiler.Environment)
    (first rest : Nat)
    (bounded : ((work.run before).run env).IsQueryBoundP (fun query => queryKind (n := n) (KemSK := KemSK) query = kind) first)
    (tailBound : ∀ value current currentEnv, (((next value).run current).run currentEnv).IsQueryBoundP
      (fun query => queryKind (n := n) (KemSK := KemSK) query = kind) rest) :
    (((work >>= next).run before).run env).IsQueryBoundP
      (fun query => queryKind (n := n) (KemSK := KemSK) query = kind) (first + rest) := by
  simp only [StateT.run_bind]
  apply isQueryBoundP_bind bounded
  rintro ⟨⟨value, current⟩, currentEnv⟩ _
  exact tailBound value current currentEnv

private theorem reserve_bound (kind : Kind) :
    (reserve (n := n) (KemSK := KemSK)).IsQueryBoundP
      (fun query => queryKind (n := n) (KemSK := KemSK) query = kind) (if kind = .reserve then 1 else 0) := by
  cases kind <;> simp [reserve, queryKind, isQueryBoundP_query_iff]

def afterAuthenticationCap (kind : Kind) : Nat := (if kind = .reserve then 1 else 0) + agreementCap kind

attribute [local irreducible] RegistrationNativePlatformServerOpenKernel.agreement

theorem afterAuthentication_bound (setup : Setup base KemSK) (checks : Checks) (kind : Kind)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationServerMaterialFrontend.State) (env : RegistrationServerReferenceCompiler.Environment) :
    (((RegistrationNativePlatformServerOpenControl.afterAuthentication protocol reserve setup checks packet authenticated).run before).run env).IsQueryBoundP
      (fun query => queryKind (n := n) (KemSK := KemSK) query = kind) (afterAuthenticationCap kind) := by
  unfold RegistrationNativePlatformServerOpenControl.afterAuthentication
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · trivial
  · apply public_bind_bound kind _ _ before env (if kind = .reserve then 1 else 0) (agreementCap kind)
      (lift_bound kind _ _ (reserve_bound kind) before env)
    intro admitted current currentEnv
    cases admitted with
    | false => trivial
    | true =>
      simp only [ite_true]
      simpa only [Nat.add_zero] using public_bind_bound kind _ _ current currentEnv (agreementCap kind) 0
        (agreement_bound setup checks kind packet authenticated current currentEnv) (by
          intro accepted final finalEnv
          cases accepted with
          | fail error | div => trivial
          | ok selected => cases selected with
            | none => trivial
            | some ready => exact retain_bound kind ready final finalEnv 0)

def afterPinCap (kind : Kind) : Nat := (if kind = .hash then 3 else 0) + afterAuthenticationCap kind

attribute [local irreducible] RegistrationNativePlatformServerOpenControl.afterAuthentication

theorem afterPin_bound (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify) (kind : Kind)
    (packet : registration.InitPacket) (result : RegistrationNativeServerPinRecompute.PinReply)
    (before : RegistrationServerMaterialFrontend.State) (env : RegistrationServerReferenceCompiler.Environment) :
    (((RegistrationNativePlatformServerOpenControl.afterPin protocol reserve setup checks verify packet result).run before).run env).IsQueryBoundP
      (fun query => queryKind (n := n) (KemSK := KemSK) query = kind) (afterPinCap kind) := by
  unfold RegistrationNativePlatformServerOpenControl.afterPin
  cases result with
  | fail error | div => trivial
  | ok selected => cases selected with
    | none => trivial
    | some pin =>
      apply public_bind_bound kind _ _ before env (if kind = .hash then 3 else 0) (afterAuthenticationCap kind)
        (lift_bound kind _ _ (authentication_bound setup.source.crypto verify pin packet kind) before env)
      intro checked current currentEnv
      cases checked with
      | fail error | div => trivial
      | ok pair =>
        rcases pair with ⟨events, authenticated⟩
        cases authenticated
        all_goals first
          | exact afterAuthentication_bound setup checks kind packet _ current currentEnv
          | trivial

attribute [local irreducible] RegistrationNativePlatformServerOpenControl.afterPin

theorem accept_bound (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify) (kind : Kind)
    (packet : registration.InitPacket)
    (before : RegistrationServerMaterialFrontend.State) (env : RegistrationServerReferenceCompiler.Environment) :
    (((RegistrationNativePlatformServerOpenSyntax.accept setup checks verify packet).run before).run env).IsQueryBoundP
      (fun query => queryKind (n := n) (KemSK := KemSK) query = kind) (cap kind) := by
  have total : cap kind = (if kind = .hash then 1 else 0) + afterPinCap kind := by
    cases kind <;> rfl
  rw [total]
  unfold RegistrationNativePlatformServerOpenSyntax.accept RegistrationNativePlatformServerOpenControl.accept
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  apply public_bind_bound kind _ _ before env (if kind = .hash then 1 else 0) (afterPinCap kind)
    (lift_bound kind _ _ (pin_bound kind before.pin) before env)
  intro current materialState currentEnv
  exact afterPin_bound setup checks verify kind packet current materialState currentEnv

end BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxBounds.source_prefix_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxBounds.source_prefix_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxBounds.collect_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxBounds.collect_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxBounds.pin_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxBounds.pin_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxBounds.authentication_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxBounds.authentication_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxBounds.agreement_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxBounds.agreement_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxBounds.afterAuthentication_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxBounds.afterAuthentication_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxBounds.afterPin_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxBounds.afterPin_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxBounds.accept_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxBounds.accept_bound
