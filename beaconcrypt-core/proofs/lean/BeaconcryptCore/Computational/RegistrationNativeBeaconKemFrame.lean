-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconKemCaps
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconFinish
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBeaconKemFrame
open RegistrationNativeBeaconFrontend (M Owner)
open RegistrationAgreementKemBounds (Kind)
open RegistrationNativeBeaconKemCaps (Bounded NativeCounted pure_bound bind_bound)
variable {n : Nat} {I KemSK Auxiliary A : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}

theorem mono (kind : Kind) (work : M n KemSK source Auxiliary A) (before after : Nat)
    (bounded : Bounded (NativeCounted kind) before work) (larger : before ≤ after) :
    Bounded (NativeCounted kind) after work := fun owners env => (bounded owners env).mono larger

theorem env_free (kind : Kind) (change : RegistrationWorldAgreementCompiler.EnvState Auxiliary → RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    Bounded (NativeCounted kind) 0 (RegistrationNativeBeaconFrontend.updateEnv (n := n) (KemSK := KemSK) (mldsaSource := source) change) := by
  intro owners env
  change IsQueryBoundP (pure (((), owners), change env)) (NativeCounted kind) 0
  trivial

theorem phase_free (kind : Kind) (index : Nat) (phase : RegistrationNativeBeaconFrontend.Phase) :
    Bounded (NativeCounted kind) 0 (RegistrationNativeBeaconFrontend.updatePhase (n := n) (KemSK := KemSK) (mldsaSource := source) (Auxiliary := Auxiliary) index phase) := by
  intro owners env
  change IsQueryBoundP (pure (((), _), env)) (NativeCounted kind) 0
  trivial

theorem abort_free (kind : Kind) (owner : Owner source) :
    Bounded (NativeCounted kind) 0 (RegistrationNativeBeaconFrontend.abort (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) owner) := by
  unfold RegistrationNativeBeaconFrontend.abort
  exact bind_bound _ _ _ 0 0 (RegistrationNativeBeaconKemCaps.effect_free kind _) (fun _ => pure_bound _ 0 ())

theorem hash_free (kind : Kind) (request : registration.HashRequest) :
    Bounded (NativeCounted kind) 0 (RegistrationNativeBeaconFrontend.hash (n := n) (KemSK := KemSK) (mldsaSource := source) (Auxiliary := Auxiliary) request) :=
  RegistrationNativeBeaconKemCaps.effect_free kind _

theorem authentication_free (kind : Kind) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (query : RegistrationAuthenticationExecutor.Request) :
    Bounded (NativeCounted kind) 0 (RegistrationNativeBeaconFrontend.authentication (n := n) (Auxiliary := Auxiliary) setup source query) := by
  cases query with
  | hash request =>
      unfold RegistrationNativeBeaconFrontend.authentication
      exact bind_bound _ _ _ 0 0 (hash_free kind request) (fun _ => pure_bound _ 0 _)
  | mldsa request | ed25519 request => exact pure_bound _ 0 _

theorem record_free (kind : Kind) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (wire : RegistrationNativeWire.Wire) (query : RegistrationRecordPrimitives.Request) :
    Bounded (NativeCounted kind) 0 (RegistrationNativeBeaconFrontend.record (n := n) (mldsaSource := source) (Auxiliary := Auxiliary) setup wire query) := by
  unfold RegistrationNativeBeaconFrontend.record
  apply bind_bound _ _ _ 0 0 (env_free kind _)
  intro unused
  cases query with
  | hash transcript =>
      change Bounded (NativeCounted kind) 0 (do
        let digest ← RegistrationNativeBeaconFrontend.hash (.Single (Std.Array.to_slice transcript.bytes))
        pure ((core.option.Option.Some (RegistrationAuthenticationShared.digestArray digest)) : core.option.Option (Std.Array U8 64#usize)))
      exact bind_bound _ _ _ 0 0 (hash_free kind _) (fun _ => pure_bound _ 0 _)
  | rootKdf request | initialKdf request | ratchetKdf request | «seal» request | write request | openAead request =>
      apply RegistrationNativeBeaconKemCaps.sample_free

theorem simulate_free {J : Type} {queries : OracleSpec J} (kind : Kind)
    (handler : QueryImpl queries (M n KemSK source Auxiliary))
    (free : ∀ query, Bounded (NativeCounted kind) 0 (handler query)) (work : OracleComp queries A) :
    Bounded (NativeCounted kind) 0 (simulateQ handler work) := by
  intro owners env
  exact RegistrationNativePlatformQueryBounds.simulate_bound (fun _ => False) (NativeCounted kind) handler
    (fun query current previous => free query current previous) work 0 (isQueryBoundP_false work 0) owners env

theorem record_program (kind : Kind) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (wire : RegistrationNativeWire.Wire) (work : OracleComp RegistrationRecordPrimitives.Spec A) :
    Bounded (NativeCounted kind) 0
      (simulateQ (RegistrationNativeBeaconFrontend.record (n := n) (mldsaSource := source) (Auxiliary := Auxiliary) setup wire) work) :=
  simulate_free kind _ (record_free kind setup wire) work

theorem authentication_program (kind : Kind) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (work : OracleComp RegistrationAuthenticationExecutor.Spec A) :
    Bounded (NativeCounted kind) 0
      (simulateQ (RegistrationNativeBeaconFrontend.authentication (n := n) (Auxiliary := Auxiliary) setup source) work) :=
  simulate_free kind _ (authentication_free kind setup) work

theorem install_free (kind : Kind) (index : Nat) (owner : Owner source) (completed : registration.CompletedBeacon) :
    Bounded (NativeCounted kind) 0
      (RegistrationNativePlatformBeaconFinish.install (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) index owner completed) := by
  rw [RegistrationNativePlatformBeaconFinish.install_exact]
  apply bind_bound _ _ _ 0 0 (RegistrationNativeBeaconKemCaps.effect_free kind _)
  intro installed
  split
  · exact bind_bound _ _ _ 0 0 (phase_free kind _ _) (fun _ => pure_bound _ 0 _)
  · exact bind_bound _ _ _ 0 0 (abort_free kind owner) (fun _ => pure_bound _ 0 _)

private theorem abort_reply (kind : Kind) (owner : Owner source) (reply : A) :
    Bounded (NativeCounted kind) 0
      (RegistrationNativeBeaconFrontend.abort (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) owner *> pure reply) :=
  bind_bound _ _ _ 0 0 (abort_free kind owner) (fun _ => pure_bound _ 0 _)

theorem afterAuthenticationWith (kind : Kind) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (installation : Nat → Owner source → registration.CompletedBeacon → M n KemSK source Auxiliary (RustM (Option Pqxdh.Bytes)))
    (freeInstallation : ∀ index owner completed, Bounded (NativeCounted kind) 0 (installation index owner completed))
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse) :
    Bounded (NativeCounted kind) 1
      (RegistrationNativePlatformBeaconFinish.afterAuthenticationWith setup installation wire index owner oneTime authenticated) := by
  unfold RegistrationNativePlatformBeaconFinish.afterAuthenticationWith
  apply bind_bound _ _ _ 1 0 (RegistrationNativeBeaconKemCaps.beacon_one kind setup owner oneTime authenticated)
  intro agreed
  cases agreed with
  | fail error | div => exact abort_reply kind owner _
  | ok phase => cases phase with
    | BeaconComplete completed =>
        apply bind_bound _ _ _ 0 0 (record_program kind setup wire _)
        intro opened
        cases opened with
        | fail error | div => exact abort_reply kind owner _
        | ok result => cases result with
          | Err control => exact abort_reply kind owner _
          | Ok established => exact freeInstallation index owner established
    | _ => exact abort_reply kind owner _

theorem finishWith (kind : Kind) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (installation : Nat → Owner source → registration.CompletedBeacon → M n KemSK source Auxiliary (RustM (Option Pqxdh.Bytes)))
    (freeInstallation : ∀ index owner completed, Bounded (NativeCounted kind) 0 (installation index owner completed))
    (wire : RegistrationNativeWire.Wire) (index : Nat) (packet : Option registration.ResponsePacket) :
    Bounded (NativeCounted kind) 1
      (RegistrationNativePlatformBeaconFinish.finishWith setup source installation wire index packet) := by
  unfold RegistrationNativePlatformBeaconFinish.finishWith
  apply bind_bound _ _ _ 0 1
  · intro owners env
    change IsQueryBoundP (pure ((owners, owners), env)) (NativeCounted kind) 0
    trivial
  · intro owners
    cases found : owners[index]? with
    | none => exact pure_bound _ 1 _
    | some owner =>
        cases phase : owner.phase with
        | initSent pending oneTime =>
            cases aborted : pending.aborted_state with
            | fail error | div =>
                simp only [phase, aborted]
                exact pure_bound _ 1 _
            | ok control =>
                simp only [phase, aborted]
                apply bind_bound _ _ _ 0 1 (phase_free kind index (.aborted control))
                intro unused
                apply bind_bound _ _ _ 0 1 (authentication_program kind setup _)
                intro authenticated
                cases authenticated with
                | fail error | div => exact mono kind _ 0 1 (abort_reply kind owner _) (by omega)
                | ok result => cases result with
                  | Err control => exact mono kind _ 0 1 (abort_reply kind owner _) (by omega)
                  | Ok authenticated => exact afterAuthenticationWith kind setup installation freeInstallation wire index owner oneTime authenticated
        | _ =>
            simp only [phase]
            exact pure_bound _ 1 _

theorem finish (kind : Kind) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (packet : Option registration.ResponsePacket) :
    Bounded (NativeCounted kind) 1
      (RegistrationNativePlatformBeaconFinish.finish (n := n) (Auxiliary := Auxiliary) setup source wire index packet) :=
  finishWith kind setup RegistrationNativePlatformBeaconFinish.install (install_free kind) wire index packet

end BeaconcryptCore.Computational.RegistrationNativeBeaconKemFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconKemFrame.mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconKemFrame.mono

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconKemFrame.env_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconKemFrame.env_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconKemFrame.phase_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconKemFrame.phase_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconKemFrame.abort_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconKemFrame.abort_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconKemFrame.hash_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconKemFrame.hash_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconKemFrame.authentication_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconKemFrame.authentication_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconKemFrame.record_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconKemFrame.record_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconKemFrame.simulate_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconKemFrame.simulate_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconKemFrame.record_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconKemFrame.record_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconKemFrame.authentication_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconKemFrame.authentication_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconKemFrame.install_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconKemFrame.install_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconKemFrame.afterAuthenticationWith' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconKemFrame.afterAuthenticationWith

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconKemFrame.finishWith' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconKemFrame.finishWith

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconKemFrame.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconKemFrame.finish
