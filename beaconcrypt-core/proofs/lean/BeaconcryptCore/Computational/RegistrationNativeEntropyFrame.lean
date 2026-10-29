-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeEntropyBounds

/-! Actual restricted-environment primitive bounds transfer without a metadata charge. The full-interface syntactic HMAC bill accounts for transport, but metadata never invokes a cryptographic HMAC, coin, hash or installation capability. The callback frame remains uniform over arbitrary literal ML pin bytes and failed native poststates. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeEntropyFrame
open RegistrationNativeEntropyInterface (Environment)
open PqxdhRecordLiftInterface (EffectKind effectKind)
variable {n : Nat} {E : Type}

def Frame (env : Environment n E) (startupCoins : Nat)
    (allowance : Fin 14 → EffectKind → Nat) : Prop :=
  env.start.IsTotalQueryBound startupCoins ∧
    ∀ query before kind, ((env.step query).run before).IsQueryBoundP
      (fun effect => effectKind effect = kind)
      (allowance (RegistrationNativeInterface.queryClass (.inl (.inr query.val))) kind)

/-- Each transported callback has the original native primitive allowance, including zero-effect metadata and malformed transport branches. -/
theorem step_frame (env : Environment n E) (startupCoins : Nat)
    (allowance : Fin 14 → EffectKind → Nat) (bounded : Frame env startupCoins allowance)
    (query : PqxdhRecordLiftInterface.EnvQuery) (before : RegistrationNativeEntropyPort.State E)
    (kind : EffectKind) :
    ((RegistrationNativeEntropyPort.step env query).run before).IsQueryBoundP
      (fun effect => effectKind effect = kind)
      (allowance (PqxdhDeploymentInterface.queryClass (.inl (.inr query.val))) kind) := by
  rcases query with ⟨command, permitted⟩
  cases command with
  | create edPin keyId =>
      rw [RegistrationNativeEntropyPort.create_run, isQueryBoundP_map_iff]
      exact bounded.2 ⟨.create edPin before.1 keyId, trivial⟩ before.2 kind
  | bundle owner =>
      simp only [RegistrationNativeEntropyPort.step, RegistrationNativeEntropyPort.native,
        StateT.run, isQueryBoundP_map_iff]
      exact bounded.2 ⟨.bundle owner, trivial⟩ before.2 kind
  | accept raw =>
      simp only [RegistrationNativeEntropyPort.step, RegistrationNativeEntropyPort.native,
        StateT.run, isQueryBoundP_map_iff]
      exact bounded.2 ⟨.accept raw, trivial⟩ before.2 kind
  | build session payload =>
      simp only [RegistrationNativeEntropyPort.step, RegistrationNativeEntropyPort.native,
        StateT.run, isQueryBoundP_map_iff]
      exact bounded.2 ⟨.build session payload, trivial⟩ before.2 kind
  | finish owner raw =>
      simp only [RegistrationNativeEntropyPort.step, RegistrationNativeEntropyPort.native,
        StateT.run, isQueryBoundP_map_iff]
      exact bounded.2 ⟨.finish owner raw, trivial⟩ before.2 kind
  | hmac key message =>
      cases decoded : RegistrationNativeEntropyInterface.decode message with
      | none => simp only [RegistrationNativeEntropyPort.step, decoded, StateT.run_pure]; trivial
      | some transport =>
          cases transport with
          | metadata mlPin => simp only [RegistrationNativeEntropyPort.step, decoded, StateT.run]; trivial
          | hmac original =>
              simp only [RegistrationNativeEntropyPort.step, decoded, RegistrationNativeEntropyPort.native,
                StateT.run, isQueryBoundP_map_iff]
              exact bounded.2 ⟨.hmac key original, trivial⟩ before.2 kind
  | hash bytes => exact False.elim permitted
  | serverSend keyId plaintext => exact False.elim permitted
  | serverRaw raw => exact False.elim permitted
  | beaconSend owner plaintext => exact False.elim permitted
  | beaconRaw owner raw => exact False.elim permitted

/-- Optional startup, primitive draws and all restricted effects retain their native allowance in the existing record environment. -/
theorem environment_frame (env : Environment n E) (startupCoins : Nat)
    (allowance : Fin 14 → EffectKind → Nat) (bounded : Frame env startupCoins allowance) :
    PqxdhRecordLiftInterface.Frame (RegistrationNativeEntropyPort.environment env) startupCoins allowance := by
  constructor
  · simpa only [RegistrationNativeEntropyPort.environment, IsTotalQueryBound, isQueryBound_map_iff] using bounded.1
  · exact step_frame env startupCoins allowance bounded

end BeaconcryptCore.Computational.RegistrationNativeEntropyFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyFrame.step_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyFrame.step_frame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyFrame.environment_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyFrame.environment_frame
