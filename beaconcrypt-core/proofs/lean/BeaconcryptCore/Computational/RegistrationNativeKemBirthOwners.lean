-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemBirthInvariant

/-! Local native owner handles and public keys survive lifecycle updates. Successful bundle support also exposes its actual earlier owner lookup and reached outgoing publication callback, rather than assuming correspondence between public bytes and a generated owner. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemBirthOwners
open RegistrationNativeBeaconFrontend
open RegistrationWorldAgreementCompiler (EnvState)
open PqxdhServerAuthExperiment (Setup)
variable {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

private def Unchanged (work : M n KemSK mlSource Auxiliary Value) : Prop :=
  ∀ owners env result, result ∈ support ((work.run owners).run env) → result.1.2 = owners

private theorem pure_unchanged (value : Value) :
    Unchanged (pure value : M n KemSK mlSource Auxiliary Value) := by
  intro owners env result supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl

private theorem bind_unchanged {Next : Type} (work : M n KemSK mlSource Auxiliary Value)
    (next : Value → M n KemSK mlSource Auxiliary Next) (first : Unchanged work)
    (rest : ∀ value, Unchanged (next value)) : Unchanged (work >>= next) := by
  intro owners env result supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  exact (rest middle.1.1 middle.1.2 middle.2 result continued).trans (first owners env middle reached)

private theorem lift_unchanged (work : StateT (EnvState Auxiliary) (OracleComp (Trusted n KemSK)) Value) :
    Unchanged (StateT.lift work : M n KemSK mlSource Auxiliary Value) := by
  intro owners env result supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
  obtain ⟨middle, _, returned⟩ := supported
  cases returned
  rfl

private theorem effect_unchanged (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    Unchanged (effect (mldsaSource := mlSource) (Auxiliary := Auxiliary) (KemSK := KemSK) query) :=
  lift_unchanged _

private theorem simulate_unchanged {Query : Type} {spec : OracleSpec Query}
    (implementation : QueryImpl spec (M n KemSK mlSource Auxiliary))
    (law : ∀ query, Unchanged (implementation query)) (work : OracleComp spec Value) :
    Unchanged (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_unchanged value
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact bind_unchanged _ _ (law query) ih

private theorem sample_unchanged (work : ProbComp Value) :
    Unchanged (sample (n := n) (KemSK := KemSK) (mldsaSource := mlSource) (Auxiliary := Auxiliary) work) :=
  simulate_unchanged (fun (query : unifSpec.Domain) => effect (.inl query))
    (fun _ => effect_unchanged _) work

/-- The actual pre-birth source prefix leaves the entire local owner list unchanged on every primitive result. -/
theorem prepare_owners (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : State mlSource) (env : EnvState Auxiliary)
    (result : (RustM (Option (Prepared mlSource)) × State mlSource) × EnvState Auxiliary)
    (supported : result ∈ support (((prepare (n := n) (KemSK := KemSK) mlSource edPin mlPin keyId).run owners).run env)) :
    result.1.2 = owners := by
  have law : Unchanged (prepare (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) mlSource edPin mlPin keyId) := by
    unfold prepare
    cases registration.begin_server_pin ⟨edPin, keyId⟩ mlPin with
    | fail error => exact pure_unchanged _
    | div => exact pure_unchanged _
    | ok pin =>
        exact bind_unchanged _ _ (sample_unchanged _) (fun _ =>
          bind_unchanged _ _ (sample_unchanged _) (fun _ => pure_unchanged _))
  exact law owners env result supported

/-- Every successful local bundle contains an actual successful outgoing callback for an owner found in the original local list. -/
theorem bundle_receipt (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (wire : RegistrationNativeWire.Wire) (index : Nat)
    (owners : State source) (env : EnvState Auxiliary)
    (bytes : Pqxdh.Bytes) (afterOwners : State source) (afterEnv : EnvState Auxiliary)
    (supported : ((.ok (some bytes), afterOwners), afterEnv) ∈ support
      (((bundle (n := n) setup source wire index).run owners).run env)) :
    ∃ selected oneTime published beforeOwners beforeEnv duringOwners duringEnv,
      owners[index]? = some selected ∧ published.encoded = bytes ∧
      ((.ok (.Ok published), duringOwners), duringEnv) ∈ support
        (((simulateQ (outgoing (n := n) (Auxiliary := Auxiliary) setup source index selected)
          (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨selected.pin.binding⟩ (inputs setup selected)
            ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩
            selected.pin)).run beforeOwners).run beforeEnv) := by
  simp only [bundle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases found : owners[index]? with
  | none => simp [found, StateT.run_pure] at supported
  | some selected =>
      rw [found] at supported
      cases phase : selected.phase <;> simp only [phase] at supported
      all_goals try { simp [StateT.run_pure] at supported }
      case fresh =>
        simp only [StateT.run_bind, mem_support_bind_iff] at supported
        obtain ⟨sampled, _, called⟩ := supported
        obtain ⟨published, outgoingSupport, returned⟩ := called
        cases actual : published.1.1 with
        | fail error => simp [actual, StateT.run_pure] at returned
        | div => simp [actual, StateT.run_pure] at returned
        | ok answer => cases answer with
          | Err previous => simp [actual, StateT.run_pure] at returned
          | Ok finished =>
              simp only [actual, updatePhase, effect, StateT.run_bind, StateT.run_modify, StateT.run_lift,
                pure_bind, bind_pure_comp, StateT.run_map, support_map] at returned
              obtain ⟨effectReply, _, resultEq⟩ := returned
              have encoded : finished.encoded = bytes := Option.some.inj (RustM.ok.inj
                (congrArg (fun value => value.1.1) resultEq))
              refine ⟨selected, sampled.1.1, finished, sampled.1.2, sampled.2,
                published.1.2, published.2, rfl, encoded, ?_⟩
              rw [← actual]
              simpa only [Prod.eta] using outgoingSupport
      case freshWithCoins oneTime =>
        simp only [StateT.run_bind, mem_support_bind_iff] at supported
        obtain ⟨published, outgoingSupport, returned⟩ := supported
        cases actual : published.1.1 with
        | fail error => simp [actual, StateT.run_pure] at returned
        | div => simp [actual, StateT.run_pure] at returned
        | ok answer => cases answer with
          | Err previous => simp [actual, StateT.run_pure] at returned
          | Ok finished =>
              simp only [actual, updatePhase, effect, StateT.run_bind, StateT.run_modify, StateT.run_lift,
                pure_bind, bind_pure_comp, StateT.run_map, support_map] at returned
              obtain ⟨effectReply, _, resultEq⟩ := returned
              have encoded : finished.encoded = bytes := Option.some.inj (RustM.ok.inj
                (congrArg (fun value => value.1.1) resultEq))
              refine ⟨selected, oneTime, finished, owners, env,
                published.1.2, published.2, rfl, encoded, ?_⟩
              rw [← actual]
              simpa only [Prod.eta] using outgoingSupport

end BeaconcryptCore.Computational.RegistrationNativeKemBirthOwners

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemBirthOwners.prepare_owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemBirthOwners.prepare_owners

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemBirthOwners.bundle_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemBirthOwners.bundle_receipt
