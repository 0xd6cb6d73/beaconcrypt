-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformInstallServerControl
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinEmbedding
/-! The actual public Server build preserves its own retained descriptor and exact successful installation bill after the source vector-to-byte representation map. All mutable platform and writer outcomes remain literal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformInstallServerTyped
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeG2Trace (State handler)
open RegistrationNativeInstallOrdinals (messages)
open RegistrationNativeInstallBeaconComplete (present)
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

private theorem embedding (work : OracleComp (RegistrationNativePlatformServerFrontendCompiler.Spec n) A) :
    simulateQ (RegistrationNativePlatformPublicCoinEmbedding.embed (KemSK := KemSK))
      (simulateQ RegistrationNativePlatformPublicFrontend.embedLocal
        (simulateQ RegistrationNativePlatformPublicFrontend.buildEmbedding work)) =
      simulateQ RegistrationNativePlatformInstallServerBranch.embed work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure]
  | query_bind query next ih =>
    have leaf : simulateQ (RegistrationNativePlatformPublicCoinEmbedding.embed (KemSK := KemSK))
        (simulateQ RegistrationNativePlatformPublicFrontend.embedLocal
          (RegistrationNativePlatformPublicFrontend.buildEmbedding query)) =
        RegistrationNativePlatformInstallServerBranch.embed query := by
      cases query with
      | inl message =>
        simp only [RegistrationNativePlatformPublicFrontend.buildEmbedding,RegistrationNativePlatformPublicFrontend.localQuery,
          RegistrationNativePlatformPublicFrontend.embedLocal,RegistrationNativePlatformPublicCoinEmbedding.embed,
          RegistrationNativePlatformInstallServerBranch.embed,RegistrationNativePlatformInstallEffects.embed,simulateQ_spec_query]
      | inr query => cases query <;>
        simp only [RegistrationNativePlatformPublicFrontend.buildEmbedding,RegistrationNativePlatformPublicFrontend.localQuery,
          RegistrationNativePlatformPublicFrontend.effect,RegistrationNativePlatformPublicFrontend.embedLocal,
          RegistrationNativePlatformPublicFrontend.localCoin,RegistrationNativePlatformPublicFrontend.publicCoin,
          RegistrationNativePlatformPublicCoinEmbedding.embed,RegistrationNativePublicFrontend.effect,RegistrationNativePublicFrontend.liftLocal,
          RegistrationNativePlatformInstallServerBranch.embed,RegistrationNativePlatformInstallEffects.embed,
          RegistrationNativePlatformInstallEffects.effects,RegistrationNativePlatformInstallEffects.env,simulateQ_spec_query]
    simp only [simulateQ_bind,simulateQ_spec_query,leaf]
    congr 1
    funext reply
    exact ih reply

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before

variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool)

/-- The literal source callback is its exact native controller under the same public/platform embedding. -/
theorem build_source (handle : Nat) (application : Option (Slice U8))
    (before : RegistrationNativePlatformPublicFrontend.State source Platform) :
    simulateQ (RegistrationNativePlatformPublicCoinEmbedding.embed (n := n) (KemSK := KemSK))
      ((RegistrationNativePlatformPublicFrontend.executeLocal
        (RegistrationNativePlatformPublicFrontend.build setup sign view failure allocation erased helper writer reserve handle application source)).run before) =
      (fun result => (RegistrationNativePlatformPublicFrontend.responseBytes result.1.1,
        ({before.1 with server := result.1.2,environment := {before.1.environment with receipts := result.2.1,recordRequests := []}},result.2.2))) <$>
      simulateQ RegistrationNativePlatformInstallServerBranch.embed
        (((RegistrationNativePlatformInstallServerControl.body setup.source view failure allocation erased helper sign writer reserve handle application).run before.1.server).run
          (before.1.environment.receipts,before.2)) := by
  unfold RegistrationNativePlatformPublicFrontend.executeLocal RegistrationNativePlatformPublicFrontend.build
  simp only [StateT.run,simulateQ_map]
  rw [embedding]
  have sourceEq := congrArg (fun work => work.run (before.1.environment.receipts,before.2))
    (RegistrationNativePlatformInstallServerControl.program_source (n := n) setup.source view failure allocation erased helper sign writer reserve handle application before.1.server)
  simp only [StateT.run] at sourceEq
  rw [sourceEq]

omit primitive in
private theorem same_presence (reply : RustM (Option (U64 × alloc.vec.Vec U8))) :
    present (RegistrationNativePlatformPublicFrontend.responseBytes reply) = present reply := by
  cases reply with
  | fail error | div => rfl
  | ok value => cases value <;> rfl

/-- A stored actual Ready supplies the exact concrete G2 descriptor on successful returned peer creation. -/
theorem build_live (role : PqxdhRecordLiftInterface.Role) (handle : Nat) (application : Option (Slice U8))
    (ready : RegistrationServerReferenceRoot.Ready) (before : RegistrationNativePlatformPublicFrontend.State source Platform)
    (stored : before.1.server.sessions[handle]? = some (some ready)) (trace : State)
    (result : (RustM (Option (U64 × Pqxdh.Bytes)) × RegistrationNativePlatformPublicFrontend.State source Platform) × State)
    (supported : result ∈ support ((simulateQ handler (simulateQ (RegistrationNativePlatformPublicCoinEmbedding.embed (n := n) (KemSK := KemSK))
      ((RegistrationNativePlatformPublicFrontend.executeLocal
        (RegistrationNativePlatformPublicFrontend.build setup sign view failure allocation erased helper writer reserve handle application source)).run before))).run trace)) :
    messages role result.2.events = messages role trace.events ++
      if role = .server ∧ present result.1.1 = true then [ready.reference] else [] := by
  rw [build_source] at supported
  simp only [simulateQ_map,StateT.run_map,support_map] at supported
  obtain ⟨reached,called,equal⟩ := supported
  cases equal
  have counted := RegistrationNativePlatformInstallServerControl.body_live setup.source view failure allocation erased helper sign writer reserve
    role handle application before.1.server ready stored (before.1.environment.receipts,before.2) trace reached called
  simpa only [Prod.map_def,id_eq,same_presence] using counted

/-- Every actual returned build result retains the exact successful peer-install count. -/
theorem build_count (role : PqxdhRecordLiftInterface.Role) (handle : Nat) (application : Option (Slice U8))
    (before : RegistrationNativePlatformPublicFrontend.State source Platform) (trace : State)
    (result : (RustM (Option (U64 × Pqxdh.Bytes)) × RegistrationNativePlatformPublicFrontend.State source Platform) × State)
    (supported : result ∈ support ((simulateQ handler (simulateQ (RegistrationNativePlatformPublicCoinEmbedding.embed (n := n) (KemSK := KemSK))
      ((RegistrationNativePlatformPublicFrontend.executeLocal
        (RegistrationNativePlatformPublicFrontend.build setup sign view failure allocation erased helper writer reserve handle application source)).run before))).run trace)) :
    ∃ added, messages role result.2.events = messages role trace.events ++ added ∧
      added.length = if role = .server ∧ present result.1.1 = true then 1 else 0 := by
  rw [build_source] at supported
  simp only [simulateQ_map,StateT.run_map,support_map] at supported
  obtain ⟨reached,called,equal⟩ := supported
  cases equal
  have counted := RegistrationNativePlatformInstallServerControl.body_count setup.source view failure allocation erased helper sign writer reserve
    role handle application before.1.server (before.1.environment.receipts,before.2) trace reached called
  simpa only [Prod.map_def,id_eq,same_presence] using counted

end BeaconcryptCore.Computational.RegistrationNativePlatformInstallServerTyped
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInstallServerTyped.build_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInstallServerTyped.build_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInstallServerTyped.build_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInstallServerTyped.build_live

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInstallServerTyped.build_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInstallServerTyped.build_count
