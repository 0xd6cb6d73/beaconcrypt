-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaRoleSyntax
import BeaconcryptCore.Computational.RegistrationNativeMldsaReceiptPreservation

/-! Outgoing Beacon Init never adds a Server-role receipt, including failed signing and encoding. The source-role subsequence therefore frames the actual all-outcome native build issuance provenance. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaRoleFrame
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend
open RegistrationNativeMldsaShared (Local lower project nativeProject)
open RegistrationSigningShared (Receipt)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeMldsaNoSign (Holds)
open RegistrationNativeMldsaRoleSyntax (NoMldsa)
variable {n : Nat} {ι KemSK Value Next Encoded Auxiliary : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

def serverReceipts (receipts : List Receipt) : List Receipt :=
  receipts.filter fun receipt => decide (receipt.observation.payload.role = .server)

private theorem shared_query (setup : Setup base KemSK) (owner : Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) (allowed : NoMldsa query)
    (before : RegistrationSigningShared.State)
    (result : RegistrationBeaconInitExecutor.Spec.Range query × RegistrationSigningShared.State)
    (supported : result ∈ support ((RegistrationNativeMldsaShared.implementation setup owner query).run before)) :
    serverReceipts result.2.1 = serverReceipts before.1 := by
  cases query with
  | inl query => cases query with
    | hash request =>
        simp only [RegistrationNativeMldsaShared.implementation, RegistrationSigningShared.implementation,
          MldsaSharedNative.authentication, StateT.run, support_map] at supported
        obtain ⟨inner, _queried, same⟩ := supported
        cases same
        rfl
    | sign request payload digest => exact False.elim allowed
  | inr request =>
      simp only [RegistrationNativeMldsaShared.implementation, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      rfl

private theorem shared_program (setup : Setup base KemSK) (owner : Owner source)
    (work : OracleComp RegistrationBeaconInitExecutor.Spec Value) (allowed : AllQueriesSatisfy work NoMldsa)
    (before : RegistrationSigningShared.State) (result : Value × RegistrationSigningShared.State)
    (supported : result ∈ support ((simulateQ (RegistrationNativeMldsaShared.implementation setup owner) work).run before)) :
    serverReceipts result.2.1 = serverReceipts before.1 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      rfl
  | query_bind query next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at allowed
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, queried, continued⟩ := supported
      exact (ih middle.1 (allowed.2 middle.1) middle.2 result continued).trans
        (shared_query setup owner query allowed.1 before middle queried)

/-- The actual complete outgoing Beacon Init preserves the exact Server-role receipt subsequence in the reached shared state. -/
theorem begin_local (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (index : Nat) (owner : Owner source)
    (encode : registration.InitView → core.option.Option Encoded)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin)
    (before : Local n KemSK source)
    (result : RustM (RegistrationBeaconInitExecutor.Result Encoded) × Local n KemSK source)
    (supported : result ∈ support ((lower setup checks representation created
      (simulateQ (RegistrationNativeBeaconFrontend.outgoing setup source index owner)
        (RegistrationBeaconInitExecutor.begin encode control inputs coins pin))).run before)) :
    serverReceipts (project result.2).1 = serverReceipts (project before).1 := by
  apply shared_program setup owner _ (RegistrationNativeMldsaRoleSyntax.begin_all encode control inputs coins pin)
    (project before) (result.1, project result.2)
  rw [← RegistrationNativeMldsaShared.program, support_map]
  exact ⟨result, supported, rfl⟩

private theorem pure_holds (value : Value) : Holds (pure value : M n KemSK source Auxiliary Value) := by
  intro owners env result supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl

private theorem bind_holds (work : M n KemSK source Auxiliary Value) (next : Value → M n KemSK source Auxiliary Next)
    (first : Holds work) (rest : ∀ value, Holds (next value)) : Holds (work >>= next) := by
  intro owners env result supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  exact (rest middle.1.1 middle.1.2 middle.2 result continued).trans (first owners env middle reached)

private theorem get_holds : Holds (get : M n KemSK source Auxiliary (State source)) := by
  intro owners env result supported
  simp only [StateT.run_get, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl

private theorem modify_holds (change : State source → State source) :
    Holds (modify change : M n KemSK source Auxiliary Unit) := by
  intro owners env result supported
  simp only [StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl

private theorem update_holds (change : EnvState Auxiliary → EnvState Auxiliary)
    (same : ∀ env, (change env).receipts = env.receipts) :
    Holds (updateEnv (n := n) (KemSK := KemSK) (mldsaSource := source) change) := by
  intro owners env result supported
  simp only [updateEnv, StateT.run_lift, StateT.run_modify, bind_pure_comp, StateT.run_map,
    map_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact same env

private theorem trusted_holds (query : (Trusted n KemSK).Domain) :
    Holds (StateT.lift (StateT.lift ((Trusted n KemSK).query query)) : M n KemSK source Auxiliary _) := by
  intro owners env result supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, Functor.map_map, support_map] at supported
  obtain ⟨inner, _possible, same⟩ := supported
  cases same
  rfl

private theorem simulate_holds {Query : Type} {spec : OracleSpec Query}
    (implementation : QueryImpl spec (M n KemSK source Auxiliary))
    (law : ∀ query, Holds (implementation query)) (work : OracleComp spec Value) : Holds (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_holds value
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact bind_holds _ _ (law query) ih

private theorem effect_holds (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    Holds (effect (KemSK := KemSK) (mldsaSource := source) (Auxiliary := Auxiliary) query) := trusted_holds _
private theorem kem_holds (query : (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Domain) :
    Holds (kem (n := n) (mldsaSource := source) (Auxiliary := Auxiliary) query) := trusted_holds _
private theorem sample_holds (draw : ProbComp Value) :
    Holds (sample (n := n) (KemSK := KemSK) (mldsaSource := source) (Auxiliary := Auxiliary) draw) :=
  simulate_holds (fun (query : unifSpec.Domain) => effect (.inl query))
    (fun _ => effect_holds _) draw
private theorem phase_holds (index : Nat) (phase : Phase) :
    Holds (updatePhase (n := n) (KemSK := KemSK) (mldsaSource := source) (Auxiliary := Auxiliary) index phase) := modify_holds _

private theorem local_noSign (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : M n KemSK source RegistrationServerRoleBackend.State Value) (noSign : Holds work)
    (before : Local n KemSK source) (result : Value × Local n KemSK source)
    (supported : result ∈ support ((lower setup checks representation created work).run before)) :
    serverReceipts (project result.2).1 = serverReceipts (project before).1 := by
  simp only [lower, StateT.run, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  have original : inner.1 ∈ support ((work.run before.1).run before.2.1) := by
    apply OracleComp.support_simulateQ_run'_subset
      (RegistrationNativeExperiment.trusted setup checks representation created source) _ before.2.2
    rw [StateT.run'_eq, support_map]
    exact ⟨inner, possible, rfl⟩
  have receipts := noSign before.1 before.2.1 inner.1 original
  change serverReceipts inner.1.2.receipts = serverReceipts before.2.1.receipts
  rw [receipts]

private def Keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : M n KemSK source RegistrationServerRoleBackend.State Value) : Prop :=
  ∀ (before : Local n KemSK source) result,
    result ∈ support ((lower setup checks representation created work).run before) →
      serverReceipts (project result.2).1 = serverReceipts (project before).1

private theorem noSign_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : M n KemSK source RegistrationServerRoleBackend.State Value) (noSign : Holds work) :
    Keeps setup checks representation created work := local_noSign setup checks representation created work noSign

private theorem state_bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (state : S) :
    (work >>= next) state = (do let result ← work state; next result.1 result.2) := rfl

private theorem lower_bind (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : M n KemSK source RegistrationServerRoleBackend.State Value)
    (next : Value → M n KemSK source RegistrationServerRoleBackend.State Next) :
    RegistrationNativeMldsaShared.lower setup checks representation created (work >>= next) =
      (RegistrationNativeMldsaShared.lower setup checks representation created work >>= fun value =>
        RegistrationNativeMldsaShared.lower setup checks representation created (next value)) := by
  funext before
  simp only [RegistrationNativeMldsaShared.lower, StateT.run, state_bind_apply,
    simulateQ_bind, map_bind, bind_map_left]

private theorem bind_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : M n KemSK source RegistrationServerRoleBackend.State Value)
    (next : Value → M n KemSK source RegistrationServerRoleBackend.State Next)
    (first : Keeps setup checks representation created work)
    (rest : ∀ value, Keeps setup checks representation created (next value)) :
    Keeps setup checks representation created (work >>= next) := by
  intro before result supported
  rw [lower_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  exact (rest middle.1 middle.2 result continued).trans (first before middle reached)

private theorem begin_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (index : Nat) (owner : Owner source)
    (encode : registration.InitView → core.option.Option Value)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) :
    Keeps (n := n) setup checks representation created
      (simulateQ (outgoing setup source index owner)
        (RegistrationBeaconInitExecutor.begin encode control inputs coins pin)) :=
  begin_local setup checks representation created index owner encode control inputs coins pin

private theorem bundle_keeps (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (index : Nat) :
    Keeps (n := n) setup checks representation created (bundle setup source wire index) := by
  unfold bundle
  apply bind_keeps _ _ _ _ _ _ (noSign_keeps _ _ _ _ _ get_holds)
  intro owners
  cases owners[index]? with
  | none => exact noSign_keeps _ _ _ _ _ (pure_holds _)
  | some owner =>
      dsimp only
      cases owner.phase <;> dsimp only <;> first
        | exact noSign_keeps _ _ _ _ _ (pure_holds _)
        | apply bind_keeps _ _ _ _ _ _
          · first
              | exact noSign_keeps _ _ _ _ _ (sample_holds _)
              | exact noSign_keeps _ _ _ _ _ (pure_holds _)
          · intro oneTime
            apply bind_keeps _ _ _ _ _ _ (begin_keeps setup checks representation created index owner _ _ _ _ _)
            intro published
            cases published with
            | fail error | div => exact noSign_keeps _ _ _ _ _ (pure_holds _)
            | ok outcome => cases outcome with
              | Err previous => exact noSign_keeps _ _ _ _ _ (pure_holds _)
              | Ok finished =>
                  apply bind_keeps _ _ _ _ _ _ (noSign_keeps _ _ _ _ _ (phase_holds index _))
                  intro ignored
                  apply bind_keeps _ _ _ _ _ _ (noSign_keeps _ _ _ _ _ (effect_holds _))
                  intro ignored
                  exact noSign_keeps _ _ _ _ _ (pure_holds _)

private theorem source_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : M n KemSK source RegistrationServerRoleBackend.State Value)
    (keeps : Keeps setup checks representation created work)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : Value × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created work).run before)) :
    serverReceipts (nativeProject result.2).1 = serverReceipts (nativeProject before).1 := by
  have law : (RegistrationNativeExperiment.beacon setup checks representation created work).run before =
      Prod.map id RegistrationNativeMldsaShared.close <$>
        (RegistrationNativeMldsaShared.lower setup checks representation created work).run
          (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before)) := by
    simp only [RegistrationNativeExperiment.beacon, RegistrationNativeMldsaShared.lower,
      StateT.run, bind_pure_comp, Functor.map_map, Prod.map, id_eq, RegistrationNativeMldsaShared.close]
  rw [law, support_map] at supported
  obtain ⟨observed, possible, same⟩ := supported
  have valid := keeps (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before)) observed possible
  rw [← same]
  exact valid


/-- Actual outgoing bundles preserve all earlier Server-role receipts and add only Beacon-role attempts. -/
theorem bundle (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (index : Nat)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : RustM (Option Pqxdh.Bytes) × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativeBeaconFrontend.bundle setup source wire index)).run before)) :
    serverReceipts (nativeProject result.2).1 = serverReceipts (nativeProject before).1 :=
  source_keeps setup checks representation created _ (bundle_keeps setup checks wire representation created index) before result supported

/-- Actual construction and every failed generation path add no Server-role signing receipt. -/
theorem create (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : RustM (Option Nat) × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId)).run before)) :
    serverReceipts (nativeProject result.2).1 = serverReceipts (nativeProject before).1 :=
  source_keeps setup checks representation created _
    (noSign_keeps setup checks representation created _ (RegistrationNativeMldsaNoSign.create setup edPin mlPin keyId)) before result supported

def NonBuild : RegistrationNativeRawAdapter.TypedSpec.Domain → Prop
  | .inr (.build _ _) => False
  | _ => True

attribute [local irreducible] RegistrationNativeExperiment.handler

/-- Every complete original typed callback except response build preserves the exact Server-role receipt subsequence, including all source failures. -/
theorem handler (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (allowed : NonBuild query)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.handler setup checks wire route representation created source credential query).run before)) :
    serverReceipts (nativeProject result.2).1 = serverReceipts (nativeProject before).1 := by
  cases query with
  | inl coin => exact congrArg serverReceipts (RegistrationNativeMldsaReceiptPreservation.handler setup checks wire route representation created credential
      (.inl coin) trivial before result supported)
  | inr query => cases query with
    | create edPin mlPin keyId =>
        simp only [RegistrationNativeExperiment.handler] at supported
        exact create setup checks representation created edPin mlPin keyId before result supported
    | bundle index =>
        simp only [RegistrationNativeExperiment.handler] at supported
        exact bundle setup checks wire representation created index before result supported
    | build index application => exact False.elim allowed
    | accept packet => exact congrArg serverReceipts (RegistrationNativeMldsaReceiptPreservation.handler setup checks wire route representation created credential
        (.inr (.accept packet)) trivial before result supported)
    | finish index packet => exact congrArg serverReceipts (RegistrationNativeMldsaReceiptPreservation.handler setup checks wire route representation created credential
        (.inr (.finish index packet)) trivial before result supported)
    | hmac key message => exact congrArg serverReceipts (RegistrationNativeMldsaReceiptPreservation.handler setup checks wire route representation created credential
        (.inr (.hmac key message)) trivial before result supported)
    | hash bytes => exact congrArg serverReceipts (RegistrationNativeMldsaReceiptPreservation.handler setup checks wire route representation created credential
        (.inr (.hash bytes)) trivial before result supported)
    | serverSend keyId plaintext => exact congrArg serverReceipts (RegistrationNativeMldsaReceiptPreservation.handler setup checks wire route representation created credential
        (.inr (.serverSend keyId plaintext)) trivial before result supported)
    | serverRaw raw => exact congrArg serverReceipts (RegistrationNativeMldsaReceiptPreservation.handler setup checks wire route representation created credential
        (.inr (.serverRaw raw)) trivial before result supported)
    | beaconSend index plaintext => exact congrArg serverReceipts (RegistrationNativeMldsaReceiptPreservation.handler setup checks wire route representation created credential
        (.inr (.beaconSend index plaintext)) trivial before result supported)
    | beaconRaw index raw => exact congrArg serverReceipts (RegistrationNativeMldsaReceiptPreservation.handler setup checks wire route representation created credential
        (.inr (.beaconRaw index raw)) trivial before result supported)

end BeaconcryptCore.Computational.RegistrationNativeMldsaRoleFrame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaRoleFrame.begin_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaRoleFrame.begin_local

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaRoleFrame.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaRoleFrame.bundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaRoleFrame.create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaRoleFrame.create

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaRoleFrame.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaRoleFrame.handler
