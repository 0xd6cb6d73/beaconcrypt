-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeAcceptCosts

/-! Literal source bills for Server material completion, including every publication failure and the one-use handle taken before admission. The bound distinguishes material demand, signing coins, shared hashes and ownership requests. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeBuildCosts
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (EnvEffects EffectKind effectKind)
open PqxdhRecordLiftCtxProgramBounds (Weighted weighted_indicator weighted_bind weighted_simulate weighted_run weighted_mono)
open RegistrationNativePrimitiveCosts (coinCost)
open RegistrationNativePublicationCosts (hashCost)
variable {n : Nat} {ι KemSK Encoded Value : Type} {base : OracleSpec ι}

private theorem record_continue {Input : Type} (action : RustM Input)
    (next : Input → OracleComp RegistrationRecordPrimitives.Spec (RustM RegistrationServerRecordExecutor.Result))
    (count : Nat) (bounded : ∀ value, (next value).IsTotalQueryBound count) :
    (RegistrationServerRecordExecutor.continueWith action next).IsTotalQueryBound count := by
  cases action with
  | ok value => exact bounded value
  | fail error => trivial
  | div => trivial

private theorem record_result {Input : Type} (action : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → OracleComp RegistrationRecordPrimitives.Spec (RustM RegistrationServerRecordExecutor.Result))
    (count : Nat) (bounded : ∀ value, (next value).IsTotalQueryBound count) :
    (RegistrationServerRecordExecutor.continueResult action next).IsTotalQueryBound count := by
  cases action with
  | ok value => cases value with
    | Ok value => exact bounded value
    | Err previous => trivial
  | fail error => trivial
  | div => trivial

theorem write_bound (pending : registration.ServerRecordWrite) :
    (RegistrationServerRecordExecutor.fromWrite pending).IsTotalQueryBound 1 := by
  apply record_continue
  intro request
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨by decide, fun _ => by trivial⟩

theorem commitment_bound (pending : registration.ServerRecordCommitment) :
    (RegistrationServerRecordExecutor.fromCommitment pending).IsTotalQueryBound 2 := by
  apply record_continue
  intro transcript
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨by decide, fun reply => record_result _ _ 1 write_bound⟩

theorem aead_bound (pending : registration.ServerRecordAead) :
    (RegistrationServerRecordExecutor.fromAead pending).IsTotalQueryBound 3 := by
  apply record_continue
  intro request
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨by decide, fun reply => record_result _ _ 2 commitment_bound⟩

theorem factored_bound (initial : RegistrationBoundKeySchedule.PublicInitial)
    (output : PqxdhServerAuthKeySchedule.Output) :
    (RegistrationBoundKeySchedule.factored initial output).IsTotalQueryBound 3 :=
  record_result _ _ 3 aead_bound

private theorem signing_continue {Input : Type} (action : RustM Input)
    (next : Input → OracleComp RegistrationSigningShared.Spec (RustM (RegistrationWorldServerPublication.Result Encoded)))
    (qSign : Nat) (kind : EffectKind) (count : Nat)
    (bounded : ∀ value, Weighted (fun query => RegistrationNativePublicationCosts.bill qSign (.inr query) kind) (next value) count) :
    Weighted (fun query => RegistrationNativePublicationCosts.bill qSign (.inr query) kind)
      (RegistrationWorldServerPublication.continueWith action next) count := by
  cases action with
  | ok value => exact bounded value
  | fail error => trivial
  | div => trivial

private theorem signing_result {Input : Type} (action : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → OracleComp RegistrationSigningShared.Spec (RustM (RegistrationWorldServerPublication.Result Encoded)))
    (qSign : Nat) (kind : EffectKind) (count : Nat)
    (bounded : ∀ value, Weighted (fun query => RegistrationNativePublicationCosts.bill qSign (.inr query) kind) (next value) count) :
    Weighted (fun query => RegistrationNativePublicationCosts.bill qSign (.inr query) kind)
      (RegistrationWorldServerPublication.continueResult action next) count := by
  cases action with
  | ok value => cases value with
    | Ok value => exact bounded value
    | Err previous => trivial
  | fail error => trivial
  | div => trivial

theorem ready_bound (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseReady) (qSign : Nat) (kind : EffectKind) :
    Weighted (fun query => RegistrationNativePublicationCosts.bill qSign (.inr query) kind)
      (RegistrationWorldServerPublication.ready encode pending) 0 := by
  rw [RegistrationWorldServerPublication.ready_pure]
  trivial

theorem signing_bound (encode : registration.SignedResponseView → core.option.Option Encoded)
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.ServerResponseSigning) (qSign : Nat) (kind : EffectKind) :
    Weighted (fun query => RegistrationNativePublicationCosts.bill qSign (.inr query) kind)
      (RegistrationWorldServerPublication.signing encode payload digest pending) (coinCost qSign kind) := by
  apply signing_continue
  intro request
  apply weighted_bind _ _ _ (coinCost qSign kind) 0
  · exact RegistrationNativeWeightedContext.query_bound _ _
  · intro reply
    exact signing_result _ _ qSign kind 0 (fun completed => ready_bound encode completed qSign kind)

attribute [local irreducible] RegistrationWorldServerPublication.signing

set_option maxRecDepth 4096 in
theorem response_bound (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseHash) (qSign : Nat) (kind : EffectKind) :
    Weighted (fun query => RegistrationNativePublicationCosts.bill qSign (.inr query) kind)
      (RegistrationWorldServerPublication.program encode pending) (hashCost kind + coinCost qSign kind) := by
  apply signing_continue
  intro request
  apply weighted_bind _ _ _ (hashCost kind) (coinCost qSign kind)
  · exact RegistrationNativeWeightedContext.query_bound _ _
  · intro digest
    exact signing_result _ _ qSign kind (coinCost qSign kind)
      (fun next => signing_bound encode _ _ next qSign kind)

set_option backward.isDefEq.respectTransparency false in
theorem raw_bound (initial : RegistrationBoundKeySchedule.PublicInitial)
    (output : PqxdhServerAuthKeySchedule.Output) (qSign : Nat) (kind : EffectKind) :
    Weighted (fun query => RegistrationNativePublicationCosts.bill qSign query kind)
      (simulateQ RegistrationBoundPublication.rawLift (simulateQ RegistrationRawSealBridge.nativeAdapter
        (RegistrationBoundKeySchedule.factored initial output))) (3 * hashCost kind) := by
  apply weighted_simulate (fun _ => hashCost kind)
  · apply weighted_simulate (fun _ => hashCost kind)
    · simpa only [ite_true, Nat.mul_comm] using weighted_indicator (fun _ => True) (hashCost kind)
        (RegistrationBoundKeySchedule.factored initial output) 3
        ((isQueryBoundP_true_iff _ _).mpr (factored_bound initial output))
    · intro query
      cases query with
      | write request => cases request <;> simp [Weighted, RegistrationRawSealBridge.nativeAdapter, isQueryBound_query_iff]
      | rootKdf request | initialKdf request | ratchetKdf request | hash request | «seal» request | openAead request =>
          simp [Weighted, RegistrationRawSealBridge.nativeAdapter, isQueryBound_query_iff]
  · intro query
    exact RegistrationNativeWeightedContext.query_bound _ _

theorem after_bound (encode : registration.SignedResponseView → core.option.Option Encoded)
    (record : RustM RegistrationServerRecordExecutor.Result) (qSign : Nat) (kind : EffectKind) :
    Weighted (fun query => RegistrationNativePublicationCosts.bill qSign query kind)
      (RegistrationBoundPublication.after encode record) (hashCost kind + coinCost qSign kind) := by
  cases record with
  | fail error => trivial
  | div => trivial
  | ok result => cases result with
    | Err previous => trivial
    | Ok pending =>
        apply weighted_simulate (fun query => RegistrationNativePublicationCosts.bill qSign (.inr query) kind)
        · exact response_bound encode pending qSign kind
        · intro query
          exact RegistrationNativeWeightedContext.query_bound _ _

theorem publication_bound (encode : registration.SignedResponseView → core.option.Option Encoded)
    (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output)
    (qSign : Nat) (kind : EffectKind) :
    Weighted (fun query => RegistrationNativePublicationCosts.bill qSign query kind)
      (RegistrationBoundPublication.program encode initial output) (4 * hashCost kind + coinCost qSign kind) := by
  have combined := weighted_bind (fun query => RegistrationNativePublicationCosts.bill qSign query kind)
    _ _ (3 * hashCost kind) (hashCost kind + coinCost qSign kind)
    (raw_bound initial output qSign kind) (fun record => after_bound encode record qSign kind)
  convert combined using 1
  · rfl
  · omega

def adminCost : EffectKind → Nat
  | .administrative => 1
  | .coin | .hash => 0

def envCost (kind : EffectKind) (query : (EnvEffects n).Domain) : Nat :=
  if effectKind query = kind then 1 else 0

theorem installation_query (keyId : U64) (binding : PqxdhRecordLiftInterface.PeerBinding)
    (kernel : PqxdhRecordLiftInterface.KernelRef n) (kind : EffectKind) :
    Weighted (envCost (n := n) kind) (((EnvEffects n).query (.inr (.installServer keyId binding kernel))) : OracleComp (EnvEffects n) _) (adminCost kind) := by
  have query := RegistrationNativeWeightedContext.query_bound (envCost kind) (.inr (.installServer keyId binding kernel))
  cases kind <;> simpa [envCost, effectKind, adminCost] using query

set_option maxRecDepth 4096 in
theorem known_install_bound (control : pqxdh.ServerState)
    (published : registration.PublishedServerResponse Encoded) (kind : EffectKind) :
    Weighted (envCost kind) (RegistrationNativePairedServerService.knownInstall (n := n) control published) (adminCost kind) := by
  cases prepared : peer.begin_peer_insert control published with
  | fail error =>
      unfold RegistrationNativePairedServerService.knownInstall
      rw [prepared]
      trivial
  | div =>
      unfold RegistrationNativePairedServerService.knownInstall
      rw [prepared]
      trivial
  | ok result => cases result with
    | Err previous =>
        unfold RegistrationNativePairedServerService.knownInstall
        rw [prepared]
        trivial
    | Ok pending =>
        rw [RegistrationNativePairedServerService.knownInstall_native control published pending prepared]
        apply weighted_bind _ _ _ (adminCost kind) 0
        · exact installation_query _ _ _ kind
        · intro inserted
          trivial

set_option maxRecDepth 4096 in
theorem hidden_install_bound (control : pqxdh.ServerState) (slot : PqxdhRecordLiftInterface.Slot n)
    (published : registration.PublishedServerResponse Encoded) (kind : EffectKind) :
    Weighted (envCost kind) (RegistrationHiddenInstall.install control slot published) (adminCost kind) := by
  cases prepared : peer.begin_peer_insert control published with
  | fail error =>
      unfold RegistrationHiddenInstall.install
      rw [prepared]
      trivial
  | div =>
      unfold RegistrationHiddenInstall.install
      rw [prepared]
      trivial
  | ok result => cases result with
    | Err previous =>
        unfold RegistrationHiddenInstall.install
        rw [prepared]
        trivial
    | Ok pending =>
        rw [RegistrationHiddenInstall.install_native control slot published pending prepared]
        apply weighted_bind _ _ _ (adminCost kind) 0
        · exact installation_query _ _ _ kind
        · intro inserted
          trivial

def commonCost (qSign : Nat) : (RegistrationNativePairedServerService.Common n).Domain → EffectKind → Nat
  | .inl query, kind => RegistrationNativePublicationCosts.bill qSign query kind
  | .inr query, kind => envCost kind query

def serviceCost (qSign : Nat) : (RegistrationNativePairedServerService.PublicSpec n).Domain → EffectKind → Nat
  | .inl _, kind => coinCost 108 kind
  | .inr query, kind => commonCost qSign query kind

theorem known_after_bound (control : pqxdh.ServerState)
    (published : RustM (RegistrationWorldServerPublication.Result Encoded)) (kind : EffectKind) :
    Weighted (envCost (n := n) kind) (RegistrationNativePairedServerService.knownAfter control published) (adminCost kind) := by
  cases published with
  | fail error => trivial
  | div => trivial
  | ok result => cases result with
    | Err previous => trivial
    | Ok completed => exact known_install_bound control completed kind

theorem hidden_after_bound (control : pqxdh.ServerState) (slot : PqxdhRecordLiftInterface.Slot n)
    (published : RustM (RegistrationWorldServerPublication.Result Encoded)) (kind : EffectKind) :
    Weighted (envCost kind) (RegistrationHiddenInstall.after control slot published) (adminCost kind) := by
  cases published with
  | fail error => trivial
  | div => trivial
  | ok result => cases result with
    | Err previous => trivial
    | Ok completed => exact hidden_install_bound control slot completed kind

theorem known_stage_bound (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (output : PqxdhServerAuthKeySchedule.Output) (qSign : Nat) (kind : EffectKind) :
    Weighted (fun query => commonCost (n := n) qSign query kind)
      (RegistrationNativePairedServerService.knownStage encode control initial output)
      ((4 * hashCost kind + coinCost qSign kind) + adminCost kind) := by
  apply weighted_bind _ _ _ (4 * hashCost kind + coinCost qSign kind) (adminCost kind)
  · apply weighted_simulate (fun query => RegistrationNativePublicationCosts.bill qSign query kind)
    · exact publication_bound encode initial output qSign kind
    · intro query
      exact RegistrationNativeWeightedContext.query_bound _ _
  · intro published
    apply weighted_simulate (envCost kind)
    · exact known_after_bound control published kind
    · intro query
      exact RegistrationNativeWeightedContext.query_bound _ _

theorem hidden_stage_bound (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (reference : RegistrationNativePairedDemand.Reference n) (qSign : Nat) (kind : EffectKind) :
    Weighted (fun query => commonCost qSign query kind)
      (RegistrationNativePairedServerService.hiddenStage encode control initial reference)
      ((4 * hashCost kind + coinCost qSign kind) + adminCost kind) := by
  apply weighted_bind _ _ _ (4 * hashCost kind + coinCost qSign kind) (adminCost kind)
  · apply weighted_simulate (fun query => RegistrationNativePublicationCosts.bill qSign query kind)
    · exact publication_bound encode initial _ qSign kind
    · intro query
      exact RegistrationNativeWeightedContext.query_bound _ _
  · intro published
    apply weighted_simulate (envCost kind)
    · exact hidden_after_bound control reference.slot published kind
    · intro query
      exact RegistrationNativeWeightedContext.query_bound _ _

theorem branch_bound (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (choice : RegistrationNativePairedChoice.Choice n) (qSign : Nat) (kind : EffectKind) :
    Weighted (fun query => commonCost qSign query kind)
      (RegistrationNativePairedServerService.publicBranch encode control initial choice)
      ((4 * hashCost kind + coinCost qSign kind) + adminCost kind) := by
  cases choice with
  | known output => exact known_stage_bound encode control initial output qSign kind
  | hidden reference => exact hidden_stage_bound encode control initial reference qSign kind

theorem admitted_bound (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (message : RegistrationNativeRelatedFamily.Message) (qSign : Nat) (kind : EffectKind) :
    Weighted (fun query => serviceCost (n := n) qSign query kind)
      (RegistrationNativePairedServerService.publicAdmitted encode control initial message)
      (coinCost 108 kind + ((4 * hashCost kind + coinCost qSign kind) + adminCost kind)) := by
  apply weighted_bind _ _ _ (coinCost 108 kind) ((4 * hashCost kind + coinCost qSign kind) + adminCost kind)
  · exact RegistrationNativeWeightedContext.query_bound _ _
  · intro selected
    cases selected with
    | none => trivial
    | some choice =>
        apply weighted_simulate (fun query => commonCost qSign query kind)
        · exact branch_bound encode control initial choice qSign kind
        · intro query
          exact RegistrationNativeWeightedContext.query_bound _ _

set_option backward.isDefEq.respectTransparency false in
theorem service_compiler_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (qSign qKem : Nat) (signing : ∀ request, (sign request).IsTotalQueryBound qSign)
    (query : (RegistrationNativePairedServerService.PublicSpec n).Domain)
    (before : RegistrationServerReferenceCompiler.Environment) (kind : EffectKind) :
    Weighted (fun query => RegistrationNativeReferenceCosts.bill (n := n) (KemSK := KemSK) qSign qKem query kind)
      ((RegistrationNativeCommonCompiler.service RegistrationBeaconReferenceCompiler.effect RegistrationServerOpenReferenceCompiler.demand
        source wire.frameWrite sign query).run before) (serviceCost qSign query kind) := by
  rcases query with message | (publication | effect)
  · simp only [RegistrationNativeCommonCompiler.service, StateT.run_lift, bind_pure_comp]
    apply RegistrationNativeWeightedContext.map_bound
    exact RegistrationNativeWeightedContext.query_bound _ _
  · simp only [RegistrationNativeCommonCompiler.service, RegistrationNativeCommonCompiler.common,
      RegistrationNativeCommonCompiler.publication, StateT.run]
    apply RegistrationNativeWeightedContext.map_bound
    exact RegistrationNativeAcceptCosts.effects_bound qSign qKem kind _ _
      (RegistrationNativePublicationCosts.compiler_bound source wire.frameWrite sign qSign signing publication before.receipts kind)
  · simp only [RegistrationNativeCommonCompiler.service, RegistrationNativeCommonCompiler.common,
      StateT.run_lift, bind_pure_comp]
    apply RegistrationNativeWeightedContext.map_bound
    exact RegistrationNativeWeightedContext.query_bound _ _

theorem service_program_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (qSign qKem : Nat) (signing : ∀ request, (sign request).IsTotalQueryBound qSign)
    (work : OracleComp (RegistrationNativePairedServerService.PublicSpec n) Value)
    (before : RegistrationServerReferenceCompiler.Environment) (kind : EffectKind) (count : Nat)
    (bounded : Weighted (fun query => serviceCost qSign query kind) work count) :
    Weighted (fun query => RegistrationNativeReferenceCosts.bill (n := n) (KemSK := KemSK) qSign qKem query kind)
      ((simulateQ (RegistrationNativeCommonCompiler.service RegistrationBeaconReferenceCompiler.effect RegistrationServerOpenReferenceCompiler.demand
        source wire.frameWrite sign) work).run before) count :=
  weighted_run _ _ _ _ _ _ bounded
    (fun query state => service_compiler_bound source wire sign qSign qKem signing query state kind)

def postCost (qSign : Nat) (kind : EffectKind) : Nat :=
  coinCost 108 kind + ((4 * hashCost kind + coinCost qSign kind) + adminCost kind)

theorem occupancy_bound (keyId : U64) (qSign : Nat) (kind : EffectKind) :
    Weighted (fun query => serviceCost (n := n) qSign query kind)
      (RegistrationServerMaterialFrontend.effect (.inr (.peerPresent keyId))) (adminCost kind) := by
  have query := RegistrationNativeWeightedContext.query_bound
    (fun query => serviceCost (n := n) qSign query kind) (.inr (.inr (.inr (.peerPresent keyId))))
  cases kind <;> simpa [RegistrationServerMaterialFrontend.effect, serviceCost, commonCost, envCost, effectKind, adminCost] using query

theorem finish_bound (result : RustM (RegistrationNativePairedServerService.Result Pqxdh.Bytes))
    (before : RegistrationServerMaterialFrontend.State) (qSign : Nat) (kind : EffectKind) :
    Weighted (fun query => serviceCost (n := n) qSign query kind)
      ((RegistrationServerMaterialFrontend.finish result).run before) 0 := by
  cases result with
  | fail error => trivial
  | div => trivial
  | ok result => cases result <;> trivial

set_option maxRecDepth 4096 in
set_option backward.isDefEq.respectTransparency false in
theorem complete_bound (wire : RegistrationNativeWire.Wire) (reservePeer : Bool)
    (ready : RegistrationServerReferenceRoot.Ready) (application : Slice U8)
    (before : RegistrationServerMaterialFrontend.State) (qSign : Nat) (kind : EffectKind) :
    Weighted (fun query => serviceCost (n := n) qSign query kind)
      ((RegistrationServerMaterialFrontend.complete wire reservePeer ready application).run before)
      (adminCost kind + postCost qSign kind) := by
  simp only [RegistrationServerMaterialFrontend.complete, StateT.run]
  cases lookupEq : peer.begin_completion_lookup before.control before.pin (RegistrationServerMaterialFrontend.token ready) application with
  | fail error => trivial
  | div => trivial
  | ok result => cases result with
    | Err previous => trivial
    | Ok lookup =>
        dsimp only
        cases requested : lookup.request with
        | fail error => trivial
        | div => trivial
        | ok keyId =>
            dsimp only
            split
            · apply weighted_bind _ _ _ (adminCost kind) (postCost qSign kind) (occupancy_bound keyId qSign kind)
              intro occupied
              cases resumed : lookup.resume occupied with
              | fail error => trivial
              | div => trivial
              | ok result => cases result with
                | Err previous => trivial
                | Ok selected =>
                    dsimp only
                    split
                    · apply weighted_bind _ _ _ (postCost qSign kind) 0
                      · exact admitted_bound _ _ _ _ qSign kind
                      · intro published
                        exact finish_bound published before qSign kind
                    · trivial
            · trivial

theorem build_source_bound (wire : RegistrationNativeWire.Wire) (reservePeer : Bool)
    (handle : Nat) (application : Option (Slice U8)) (before : RegistrationServerMaterialFrontend.State)
    (qSign : Nat) (kind : EffectKind) :
    Weighted (fun query => serviceCost (n := n) qSign query kind)
      ((RegistrationServerMaterialFrontend.build wire reservePeer handle application).run before)
      (adminCost kind + postCost qSign kind) := by
  simp only [RegistrationServerMaterialFrontend.build, StateT.run]
  cases taken : RegistrationServerMaterialFrontend.take handle before with
  | mk selected current =>
      cases selected with
      | none => trivial
      | some ready =>
          cases application with
          | none => trivial
          | some application => exact complete_bound wire reservePeer ready application current qSign kind

def bill (qSign : Nat) : EffectKind → Nat
  | .coin => 108 + qSign
  | .hash => 4
  | .administrative => 2

theorem server_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (wire : RegistrationNativeWire.Wire) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (qSign qKem : Nat) (signing : ∀ request, (sign request).IsTotalQueryBound qSign)
    (handle : Nat) (application : Option (Slice U8)) (before : RegistrationServerMaterialFrontend.State)
    (env : RegistrationServerReferenceCompiler.Environment) (kind : EffectKind) :
    Weighted (fun query => RegistrationNativeReferenceCosts.bill (n := n) (KemSK := KemSK) qSign qKem query kind)
      (((RegistrationServerOpenReferenceCompiler.build source wire checks sign handle application).run before).run env)
      (bill qSign kind) := by
  have bounded := service_program_bound (n := n) (KemSK := KemSK) source wire sign qSign qKem signing
    ((RegistrationServerMaterialFrontend.build wire checks.reservePeer handle application).run before) env kind
    (adminCost kind + postCost qSign kind) (build_source_bound wire checks.reservePeer handle application before qSign kind)
  exact weighted_mono _ _ _ _ bounded (by cases kind <;> simp [bill, postCost, coinCost, hashCost, adminCost])

set_option maxRecDepth 4096 in
set_option backward.isDefEq.respectTransparency false in
theorem frontend_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept qSign qKem : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (signing : ∀ request, (sign request).IsTotalQueryBound qSign)
    (handle : Nat) (application : Option (Slice U8))
    (before : RegistrationNativePublicFrontend.State source) (kind : EffectKind) :
    Weighted (fun query => RegistrationNativeRestrictedCosts.bill (n := n) (KemSK := KemSK) qSign qKem query kind)
      ((RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey
        (.inr (.build handle application))).run before) (bill qSign kind) := by
  simp only [RegistrationNativePublicFrontend.handler, StateT.run]
  apply RegistrationNativeWeightedContext.map_bound
  apply RegistrationNativeReferenceCosts.lifted_program
  exact server_bound setup.source wire checks sign qSign qKem signing handle application before.server before.environment kind

end BeaconcryptCore.Computational.RegistrationNativeBuildCosts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBuildCosts.write_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBuildCosts.write_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBuildCosts.commitment_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBuildCosts.commitment_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBuildCosts.aead_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBuildCosts.aead_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBuildCosts.factored_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBuildCosts.factored_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBuildCosts.ready_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBuildCosts.ready_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBuildCosts.signing_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBuildCosts.signing_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBuildCosts.response_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBuildCosts.response_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBuildCosts.raw_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBuildCosts.raw_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBuildCosts.after_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBuildCosts.after_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBuildCosts.publication_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBuildCosts.publication_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBuildCosts.installation_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBuildCosts.installation_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBuildCosts.known_install_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBuildCosts.known_install_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBuildCosts.hidden_install_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBuildCosts.hidden_install_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBuildCosts.known_after_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBuildCosts.known_after_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBuildCosts.hidden_after_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBuildCosts.hidden_after_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBuildCosts.known_stage_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBuildCosts.known_stage_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBuildCosts.hidden_stage_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBuildCosts.hidden_stage_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBuildCosts.branch_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBuildCosts.branch_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBuildCosts.admitted_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBuildCosts.admitted_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBuildCosts.service_compiler_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBuildCosts.service_compiler_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBuildCosts.service_program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBuildCosts.service_program_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBuildCosts.occupancy_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBuildCosts.occupancy_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBuildCosts.finish_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBuildCosts.finish_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBuildCosts.complete_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBuildCosts.complete_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBuildCosts.build_source_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBuildCosts.build_source_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBuildCosts.server_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBuildCosts.server_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBuildCosts.frontend_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBuildCosts.frontend_bound
