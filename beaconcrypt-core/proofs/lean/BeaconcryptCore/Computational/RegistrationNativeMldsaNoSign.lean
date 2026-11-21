-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeWorldCache

/-! Native construction and incoming finish make no ML signing attempt. Their actual local controllers preserve the complete global chronological ML receipt list, including every optional primitive and terminal failure; the shared cache itself may grow. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaNoSign
open RegistrationNativeBeaconFrontend
open RegistrationWorldAgreementCompiler (EnvState)
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK Auxiliary Value Next : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

def Holds (work : M n KemSK source Auxiliary Value) : Prop :=
  ∀ owners env result, result ∈ support ((work.run owners).run env) → result.2.receipts = env.receipts

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

private theorem authentication_holds (setup : Setup base KemSK) (query : RegistrationAuthenticationExecutor.Spec.Domain) :
    Holds (authentication (n := n) (Auxiliary := Auxiliary) setup source query) := by
  cases query with
  | hash request => exact bind_holds _ _ (effect_holds _) (fun _ => pure_holds _)
  | mldsa request | ed25519 request => exact pure_holds _

private theorem primitive_holds (setup : Setup base KemSK) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (query : RegistrationAgreementShared.PrimitiveSpec.Domain) :
    Holds (primitive (n := n) (Auxiliary := Auxiliary) setup owner oneTime query) :=
  simulate_holds _ (fun lower => match lower with
    | .inl _ => sample_holds _
    | .inr _ => kem_holds _) _

private theorem agreement_holds (setup : Setup base KemSK) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (query : RegistrationAgreementExecutor.Spec.Domain) :
    Holds (agreement (n := n) (Auxiliary := Auxiliary) setup owner oneTime query) := by
  unfold agreement
  apply bind_holds _ _ (update_holds
    (fun env => { env with requests := env.requests ++ RegistrationWorldAgreement.recorded query }) (fun _ => rfl))
  intro ignored
  cases query with
  | root request => exact pure_holds _
  | _ => exact primitive_holds setup owner oneTime _

private theorem record_holds (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (query : RegistrationRecordPrimitives.Spec.Domain) : Holds (record (n := n) (mldsaSource := source) (Auxiliary := Auxiliary) setup wire query) := by
  unfold record
  apply bind_holds _ _ (update_holds
    (fun env => { env with recordRequests := env.recordRequests ++ [RegistrationWorldAgreement.recordCall query] }) (fun _ => rfl))
  intro ignored
  cases query with
  | hash request | adHash request => exact bind_holds _ _ (effect_holds _) (fun _ => pure_holds _)
  | _ => exact sample_holds _

private theorem abort_holds (owner : Owner source) :
    Holds (abort (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) owner) :=
  bind_holds _ _ (effect_holds _) (fun _ => pure_holds _)

/-- Pure full-pin selection, actual Ed/prekey draws and all constructor failures leave earlier Server signing attempts unchanged. -/
theorem create (setup : Setup base KemSK) (edPin : Std.Array Std.U8 32#usize)
    (mlPin : Std.Array Std.U8 1952#usize) (keyId : Std.U64) :
    Holds (RegistrationNativeBeaconFrontend.create (n := n) (Auxiliary := Auxiliary) setup source edPin mlPin keyId) := by
  have prepareLaw : Holds (prepare (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) source edPin mlPin keyId) := by
    unfold prepare
    cases registration.begin_server_pin ⟨edPin, keyId⟩ mlPin with
    | fail error | div => exact pure_holds _
    | ok pin =>
        exact bind_holds _ _ (sample_holds _) (fun _ =>
          bind_holds _ _ (sample_holds _) (fun _ => pure_holds _))
  unfold RegistrationNativeBeaconFrontend.create
  apply bind_holds _ _ prepareLaw
  intro prepared
  cases prepared with
  | fail error | div => exact pure_holds _
  | ok option => cases option with
    | none => exact pure_holds _
    | some prepared =>
        unfold appendBorn
        apply bind_holds _ _ (kem_holds _)
        intro born
        apply bind_holds _ _ (effect_holds _)
        intro worldOwner
        apply bind_holds _ _ get_holds
        intro owners
        apply bind_holds _ _ (modify_holds _)
        intro ignored
        exact pure_holds _

/-- The entire actual incoming Beacon controller retains every prior ML attempt, including malformed packets and terminal failures. -/
theorem finish (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (packet : Option registration.ResponsePacket) :
    Holds (RegistrationNativeBeaconFrontend.finish (n := n) (Auxiliary := Auxiliary) setup source wire index packet) := by
  unfold RegistrationNativeBeaconFrontend.finish
  apply bind_holds _ _ get_holds
  intro owners
  cases owners[index]? with
  | none => exact pure_holds _
  | some owner =>
      dsimp only
      cases owner.phase with
      | initSent pending oneTime =>
          dsimp only
          cases pending.aborted_state with
          | fail error | div => exact pure_holds _
          | ok aborted =>
              apply bind_holds _ _ (phase_holds index _)
              intro ignored
              apply bind_holds _ _ (simulate_holds _ (authentication_holds setup) _)
              intro authenticated
              cases authenticated with
              | fail error | div => exact bind_holds _ _ (abort_holds _) (fun _ => pure_holds _)
              | ok outcome => cases outcome with
                | Err previous => exact bind_holds _ _ (abort_holds _) (fun _ => pure_holds _)
                | Ok accepted =>
                    apply bind_holds _ _ (simulate_holds _ (agreement_holds setup owner oneTime) _)
                    intro agreed
                    cases agreed with
                    | fail error | div => exact bind_holds _ _ (abort_holds _) (fun _ => pure_holds _)
                    | ok effect => cases effect with
                      | BeaconComplete completed =>
                          apply bind_holds _ _ (simulate_holds _ (record_holds setup wire) _)
                          intro opened
                          cases opened with
                          | fail error | div => exact bind_holds _ _ (abort_holds _) (fun _ => pure_holds _)
                          | ok result => cases result with
                            | Err previous => exact bind_holds _ _ (abort_holds _) (fun _ => pure_holds _)
                            | Ok established =>
                                apply bind_holds _ _ (effect_holds _)
                                intro installed
                                cases installed <;> first
                                  | exact bind_holds _ _ (abort_holds _) (fun _ => pure_holds _)
                                  | exact bind_holds _ _ (phase_holds index _) (fun _ => pure_holds _)
                      | _ => exact bind_holds _ _ (abort_holds _) (fun _ => pure_holds _)
      | _ => exact pure_holds _

/-- The actual local interpretation of a non-signing controller retains valid chronological ML receipts. -/
theorem local_cached (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : M n KemSK source RegistrationServerRoleBackend.State Value) (noSign : Holds work)
    (before : RegistrationNativeMldsaShared.Local n KemSK source)
    (cached : RegistrationSigningShared.Cached (RegistrationNativeMldsaShared.project before))
    (result : Value × RegistrationNativeMldsaShared.Local n KemSK source)
    (supported : result ∈ support ((RegistrationNativeMldsaShared.lower setup checks representation created work).run before)) :
    RegistrationSigningShared.Cached (RegistrationNativeMldsaShared.project result.2) := by
  have extended := RegistrationNativeWorldCache.localProgram setup checks representation created work before result supported
  simp only [RegistrationNativeMldsaShared.lower, StateT.run, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  have original : inner.1 ∈ support ((work.run before.1).run before.2.1) := by
    apply OracleComp.support_simulateQ_run'_subset
      (RegistrationNativeExperiment.trusted setup checks representation created source) _ before.2.2
    rw [StateT.run'_eq, support_map]
    exact ⟨inner, possible, rfl⟩
  have receipts := noSign before.1 before.2.1 inner.1 original
  change RegistrationSigningShared.Cached (inner.1.2.receipts, RegistrationNativeWorldCache.cache inner.2)
  rw [receipts]
  exact RegistrationSigningShared.cached_extend before.2.1.receipts
    (RegistrationNativeWorldCache.cache before.2.2) (RegistrationNativeWorldCache.cache inner.2) extended cached

private def Keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : M n KemSK source RegistrationServerRoleBackend.State Value) : Prop :=
  ∀ (before : RegistrationNativeMldsaShared.Local n KemSK source),
    RegistrationSigningShared.Cached (RegistrationNativeMldsaShared.project before) →
    ∀ result, result ∈ support ((RegistrationNativeMldsaShared.lower setup checks representation created work).run before) →
      RegistrationSigningShared.Cached (RegistrationNativeMldsaShared.project result.2)

private theorem noSign_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : M n KemSK source RegistrationServerRoleBackend.State Value) (noSign : Holds work) :
    Keeps setup checks representation created work :=
  local_cached setup checks representation created work noSign

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
  intro before cached result supported
  rw [lower_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  exact rest middle.1 middle.2 (first before cached middle reached) result continued

private theorem begin_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (index : Nat) (owner : Owner source)
    (encode : registration.InitView → core.option.Option Value)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) :
    Keeps (n := n) setup checks representation created
      (simulateQ (outgoing setup source index owner)
        (RegistrationBeaconInitExecutor.begin encode control inputs coins pin)) :=
  RegistrationNativeMldsaShared.begin_cached setup checks representation created index owner encode control inputs coins pin

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
    (cached : RegistrationSigningShared.Cached (RegistrationNativeMldsaShared.nativeProject before))
    (result : Value × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created work).run before)) :
    RegistrationSigningShared.Cached (RegistrationNativeMldsaShared.nativeProject result.2) := by
  have law : (RegistrationNativeExperiment.beacon setup checks representation created work).run before =
      Prod.map id RegistrationNativeMldsaShared.close <$>
        (RegistrationNativeMldsaShared.lower setup checks representation created work).run
          (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before)) := by
    simp only [RegistrationNativeExperiment.beacon, RegistrationNativeMldsaShared.lower,
      StateT.run, bind_pure_comp, Functor.map_map, Prod.map, id_eq, RegistrationNativeMldsaShared.close]
  rw [law, support_map] at supported
  obtain ⟨observed, possible, same⟩ := supported
  have valid := keeps (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before)) cached observed possible
  rw [← same]
  exact valid

/-- The actual complete native constructor retains all earlier valid ML signing receipts. -/
theorem source_create_cached (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (edPin : Std.Array Std.U8 32#usize) (mlPin : Std.Array Std.U8 1952#usize) (keyId : Std.U64)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (cached : RegistrationSigningShared.Cached (RegistrationNativeMldsaShared.nativeProject before))
    (result : RustM (Option Nat) × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId)).run before)) :
    RegistrationSigningShared.Cached (RegistrationNativeMldsaShared.nativeProject result.2) :=
  source_keeps setup checks representation created _ (noSign_keeps _ _ _ _ _ (create setup edPin mlPin keyId))
    before cached result supported

/-- Every failed or successful actual outgoing Beacon bundle retains the same valid prior chronological Server ML hash receipts through its actual Ed signing and Init writer branches. -/
theorem source_bundle_cached (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (index : Nat)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (cached : RegistrationSigningShared.Cached (RegistrationNativeMldsaShared.nativeProject before))
    (result : RustM (Option Pqxdh.Bytes) × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativeBeaconFrontend.bundle setup source wire index)).run before)) :
    RegistrationSigningShared.Cached (RegistrationNativeMldsaShared.nativeProject result.2) :=
  source_keeps setup checks representation created _ (bundle_keeps setup checks wire representation created index)
    before cached result supported

/-- Every terminal incoming native finish retains valid prior ML receipts through all response/record gates and installation failures. -/
theorem source_finish_cached (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (index : Nat) (packet : Option registration.ResponsePacket)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (cached : RegistrationSigningShared.Cached (RegistrationNativeMldsaShared.nativeProject before))
    (result : RustM (Option Pqxdh.Bytes) × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativeBeaconFrontend.finish setup source wire index packet)).run before)) :
    RegistrationSigningShared.Cached (RegistrationNativeMldsaShared.nativeProject result.2) :=
  source_keeps setup checks representation created _ (noSign_keeps _ _ _ _ _ (finish setup wire index packet))
    before cached result supported

end BeaconcryptCore.Computational.RegistrationNativeMldsaNoSign

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaNoSign.create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaNoSign.create
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaNoSign.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaNoSign.finish
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaNoSign.local_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaNoSign.local_cached
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaNoSign.source_create_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaNoSign.source_create_cached
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaNoSign.source_bundle_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaNoSign.source_bundle_cached
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaNoSign.source_finish_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaNoSign.source_finish_cached
