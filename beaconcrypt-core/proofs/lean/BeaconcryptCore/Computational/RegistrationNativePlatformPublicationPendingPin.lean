-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformGenericBundle
import BeaconcryptCore.Computational.RegistrationBeaconInitPin

/-! The actual effectful Init publisher retains its original expected Server binding through every reached Core stage. The encoder and primitive replies remain arbitrary; success derives this field from the captured input control rather than from an assumed packet or encoder law. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicationPendingPin
open RegistrationNativePlatformBeaconPublication
open RegistrationBeaconInitPin (StateCoherent Coherent)
variable {expected : pqxdh.ServerBinding}
variable {κ Encoded Auxiliary : Type} {target : OracleSpec κ} {source : RegistrationNativeMldsa.Source}
local notation "M" => RegistrationNativePlatformGenericBundle.M source Auxiliary (OracleComp target)
local notation "Owners" => RegistrationNativeBeaconFrontend.State source
local notation "Env" => RegistrationWorldAgreementCompiler.EnvState Auxiliary

attribute [local irreducible] registration.BeaconInitHash.resume
  registration.BeaconEd25519Signing.resume

private theorem continue_support {Input : Type} (action : RustM Input)
    (next : Input → M (RustM (RegistrationBeaconInitExecutor.Result Encoded)))
    (published : registration.PublishedBeaconInit Encoded) (before after : Owners) (env later : Env)
    (supported : ((.ok (.Ok published), after), later) ∈ support (((continueWith action next).run before).run env)) :
    ∃ value, action = .ok value ∧ ((.ok (.Ok published), after), later) ∈ support (((next value).run before).run env) := by
  cases action <;> simp_all [continueWith]

private theorem ready_coherent (encode : registration.InitView → M (RustM (core.option.Option Encoded)))
    (pending : registration.BeaconInitReady) (published : registration.PublishedBeaconInit Encoded)
    (coherent : Coherent expected (.Ready pending)) (before after : Owners) (env later : Env)
    (supported : ((.ok (.Ok published), after), later) ∈ support (((ready encode pending).run before).run env)) :
    published.pending.control.expected_server_binding = expected := by
  obtain ⟨view, _requested, called⟩ := continue_support pending.message _ published before after env later supported
  simp only [StateT.run_bind, mem_support_bind_iff] at called
  obtain ⟨⟨⟨encoded, current⟩, platform⟩, _encoded, returned⟩ := called
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at returned
  cases encoded with
  | fail error | div => cases returned.1.1
  | ok encoded =>
    exact RegistrationBeaconInitPin.publish_coherent pending encoded published coherent returned.1.1.symm

private theorem hash_coherent (impl : QueryImpl RegistrationBeaconInitExecutor.Spec M)
    (encode : registration.InitView → M (RustM (core.option.Option Encoded)))
    (pending : registration.BeaconInitHash) (published : registration.PublishedBeaconInit Encoded)
    (coherent : StateCoherent expected pending.state) (before after : Owners) (env later : Env)
    (supported : ((.ok (.Ok published), after), later) ∈ support (((fromHash impl encode pending).run before).run env)) :
    published.pending.control.expected_server_binding = expected := by
  obtain ⟨request, _requested, called⟩ := continue_support pending.request _ published before after env later supported
  simp only [StateT.run_bind, mem_support_bind_iff] at called
  obtain ⟨⟨⟨digest, current⟩, platform⟩, _hashed, continued⟩ := called
  obtain ⟨effect, resumed, continued⟩ := continue_support (pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest))) _ published current after platform later continued
  have kept := RegistrationBeaconInitPin.hash_coherent pending _ effect coherent resumed
  cases effect with
  | Ready selected => exact ready_coherent encode selected published kept current after platform later continued
  | _ => simp at continued

private theorem ed_coherent (impl : QueryImpl RegistrationBeaconInitExecutor.Spec M)
    (encode : registration.InitView → M (RustM (core.option.Option Encoded)))
    (pending : registration.BeaconEd25519Signing) (published : registration.PublishedBeaconInit Encoded)
    (coherent : StateCoherent expected pending.state) (before after : Owners) (env later : Env)
    (supported : ((.ok (.Ok published), after), later) ∈ support (((fromEd impl encode pending).run before).run env)) :
    published.pending.control.expected_server_binding = expected := by
  rw [fromEd.eq_def] at supported
  obtain ⟨request, _requested, called⟩ := continue_support pending.request _ published before after env later supported
  simp only [StateT.run_bind, mem_support_bind_iff] at called
  obtain ⟨⟨⟨reply, current⟩, platform⟩, _signed, continued⟩ := called
  cases actual : pending.resume reply with
  | fail error => rw [actual] at continued; simp at continued
  | div => rw [actual] at continued; simp at continued
  | ok effect =>
    have kept := RegistrationBeaconInitPin.ed_coherent pending reply effect coherent actual
    cases effect with
    | Ed25519SigningRequested next =>
      rw [actual] at continued
      exact ed_coherent impl encode next published kept current after platform later continued
    | HashRequested selected =>
      rw [actual] at continued
      exact hash_coherent impl encode selected published kept current after platform later continued
    | _ => rw [actual] at continued; simp at continued
termination_by RegistrationBeaconInitExecutor.edRank pending
decreasing_by exact RegistrationBeaconInitExecutor.ed_rank pending reply next actual

/-- Full actual source publication derives pending coherence even when the encoder has effects and fails on other branches. -/
theorem begin_coherent (impl : QueryImpl RegistrationBeaconInitExecutor.Spec M)
    (encode : registration.InitView → M (RustM (core.option.Option Encoded)))
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin)
    (published : registration.PublishedBeaconInit Encoded) (before after : Owners) (env later : Env)
    (supported : ((.ok (.Ok published), after), later) ∈ support (((begin impl encode control inputs coins pin).run before).run env)) :
    published.pending.control.expected_server_binding = control.expected_server_binding := by
  obtain ⟨effect, actual, continued⟩ := continue_support (registration.begin_beacon_init control inputs coins pin) _ published before after env later supported
  have kept := RegistrationBeaconInitPin.begin_coherent control inputs coins pin effect actual
  cases effect with
  | Ed25519SigningRequested selected => exact ed_coherent impl encode selected published kept before after env later continued
  | _ => simp at continued

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicationPendingPin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicationPendingPin.begin_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicationPendingPin.begin_coherent
