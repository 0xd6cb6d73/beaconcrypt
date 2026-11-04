-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaOrdinaryMap

/-! Controller continuations after ML generation are parametric in the private key representation. The only verifier premise is equality of the original ML verifier; all owned phases, World effects and failed prefixes are retained. These lemmas assume no equality for generation or signing of the opaque handle source. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaControllerMap
open RegistrationNativeMldsa (Source)
open RegistrationNativeMldsaMap (Map owners owner)
open RegistrationNativeMldsaOrdinaryMap
variable {left right : Source} {n : Nat} {KemSK Auxiliary ι : Type} {base : OracleSpec ι}

def preparedResult (mapping : Map left right)
    (action : RustM (Option (RegistrationNativeBeaconFrontend.Prepared left))) :
    RustM (Option (RegistrationNativeBeaconFrontend.Prepared right)) :=
  match action with
  | .ok value => .ok (value.map (RegistrationNativeMldsaMap.prepared mapping))
  | .fail error => .fail error
  | .div => .div

set_option backward.isDefEq.respectTransparency false in
theorem afterGenerated_natural (mapping : Map left right)
    (edPin : Std.Array Std.U8 32#usize) (mlPin : Std.Array Std.U8 1952#usize) (keyId : Std.U64)
    (generated : Option (RegistrationNativeMldsa.Credential left)) :
    Natural (n := n) (KemSK := KemSK) (Auxiliary := RegistrationServerRoleBackend.State) mapping (preparedResult mapping)
      (RegistrationNativeMldsaCreation.afterGenerated edPin mlPin keyId generated)
      (RegistrationNativeMldsaCreation.afterGenerated edPin mlPin keyId (generated.map (RegistrationNativeMldsaMap.credential mapping))) := by
  unfold RegistrationNativeMldsaCreation.afterGenerated
  cases generated with
  | none => exact pure_natural mapping (preparedResult mapping) _
  | some credential =>
      simp only [Option.map_some]
      cases registration.begin_server_pin ⟨edPin, keyId⟩ mlPin with
      | fail error => exact pure_natural mapping (preparedResult mapping) _
      | div => exact pure_natural mapping (preparedResult mapping) _
      | ok pending =>
          simp only
          cases pending.request with
          | fail error => exact pure_natural mapping (preparedResult mapping) _
          | div => exact pure_natural mapping (preparedResult mapping) _
          | ok request =>
              simp only
              apply bind_natural mapping id (preparedResult mapping) _ _ _ _ (hash_natural mapping request)
              intro digest
              simp only [id_eq]
              cases pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest)) with
              | fail error => exact pure_natural mapping (preparedResult mapping) _
              | div => exact pure_natural mapping (preparedResult mapping) _
              | ok result => cases result with
                | none => exact pure_natural mapping (preparedResult mapping) _
                | some pin =>
                    apply bind_natural mapping id (preparedResult mapping) _ _ _ _ (sample_natural mapping PqxdhJointIdentity.sampleSeed)
                    intro identity
                    apply bind_natural mapping id (preparedResult mapping) _ _ _ _ (sample_natural mapping PqxdhJointGapDh.sampleScalar)
                    intro prekey
                    exact pure_natural mapping (preparedResult mapping) _

set_option backward.isDefEq.respectTransparency false in
theorem createSuffix_natural (mapping : Map left right) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (edPin : Std.Array Std.U8 32#usize) (mlPin : Std.Array Std.U8 1952#usize) (keyId : Std.U64)
    (generated : Option (RegistrationNativeMldsa.Credential left)) :
    Natural (n := n) (Auxiliary := RegistrationServerRoleBackend.State) mapping id
      (RegistrationNativeMldsaCreation.createSuffix setup edPin mlPin keyId generated)
      (RegistrationNativeMldsaCreation.createSuffix setup edPin mlPin keyId (generated.map (RegistrationNativeMldsaMap.credential mapping))) := by
  unfold RegistrationNativeMldsaCreation.createSuffix
  apply bind_natural mapping (preparedResult mapping) id _ _ _ _ (afterGenerated_natural mapping edPin mlPin keyId generated)
  intro action
  cases action with
  | fail error => exact pure_natural mapping id _
  | div => exact pure_natural mapping id _
  | ok result => cases result with
    | none => exact pure_natural mapping id _
    | some prepared => exact appendBorn_natural mapping setup edPin keyId prepared.pin prepared.credentials prepared.identity prepared.prekey

set_option backward.isDefEq.respectTransparency false in
theorem record_natural (mapping : Map left right) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (wire : RegistrationNativeWire.Wire) (query : RegistrationRecordPrimitives.Request) :
    Natural (n := n) (Auxiliary := Auxiliary) mapping id
      (RegistrationNativeBeaconFrontend.record setup wire query) (RegistrationNativeBeaconFrontend.record setup wire query) := by
  unfold RegistrationNativeBeaconFrontend.record
  apply bind_natural mapping id id _ _ _ _ (updateEnv_natural mapping _)
  intro _updated
  cases query with
  | hash transcript =>
      apply bind_natural mapping id id _ _ _ _ (hash_natural mapping (.Single (Std.Array.to_slice transcript.bytes)))
      intro digest
      exact pure_natural mapping id _
  | rootKdf request | initialKdf request | ratchetKdf request | «seal» request | write request | openAead request =>
      exact sample_natural mapping _

private theorem abort_pure_natural {Value : Type} (mapping : Map left right)
    (current : RegistrationNativeBeaconFrontend.Owner left) (value : Value) :
    Natural (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) mapping id
      (RegistrationNativeBeaconFrontend.abort current *> pure value)
      (RegistrationNativeBeaconFrontend.abort (owner mapping current) *> pure value) := by
  simp only [seqRight_eq_bind]
  apply bind_natural mapping id id _ _ _ _ (abort_natural mapping current)
  intro _aborted
  exact pure_natural mapping id value

set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency false in
theorem finish_natural (mapping : Map left right) (sameVerify : left.verify = right.verify)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (packet : Option registration.ResponsePacket) :
    Natural (n := n) (Auxiliary := Auxiliary) mapping id
      (RegistrationNativeBeaconFrontend.finish setup left wire index packet)
      (RegistrationNativeBeaconFrontend.finish setup right wire index packet) := by
  unfold RegistrationNativeBeaconFrontend.finish
  apply bind_natural mapping (owners mapping) id _ _ _ _ (get_natural mapping)
  intro before
  simp only [RegistrationNativeMldsaMap.owners_lookup]
  cases before[index]? with
  | none => exact pure_natural mapping id _
  | some current =>
      simp only [Option.map_some]
      dsimp only [RegistrationNativeMldsaMap.owner]
      cases current.phase with
      | fresh | freshWithCoins oneTime | established completed | aborted previous => exact pure_natural mapping id _
      | initSent pending oneTime =>
          simp only
          cases pending.aborted_state with
          | fail error => exact pure_natural mapping id _
          | div => exact pure_natural mapping id _
          | ok aborted =>
              apply bind_natural mapping id id _ _ _ _ (phase_natural mapping index (.aborted aborted))
              intro _changed
              apply bind_natural mapping id id _ _ _ _ (simulate_natural mapping _ _ (authentication_natural mapping sameVerify setup) _)
              intro authenticated
              simp only [id_eq]
              cases authenticated with
              | fail error => exact abort_pure_natural mapping current _
              | div => exact abort_pure_natural mapping current _
              | ok outcome => cases outcome with
                | Err previous => exact abort_pure_natural mapping current _
                | Ok accepted =>
                    apply bind_natural mapping id id _ _ _ _ (simulate_natural mapping _ _ (agreement_natural mapping setup current oneTime) _)
                    intro agreed
                    simp only [id_eq]
                    cases agreed with
                    | fail error => exact abort_pure_natural mapping current _
                    | div => exact abort_pure_natural mapping current _
                    | ok outcome => cases outcome with
                      | Rejected value => exact abort_pure_natural mapping current _
                      | ConvertPublic value => exact abort_pure_natural mapping current _
                      | ConvertSecret value => exact abort_pure_natural mapping current _
                      | GenerateEphemeral value => exact abort_pure_natural mapping current _
                      | Encapsulate value => exact abort_pure_natural mapping current _
                      | Decapsulate value => exact abort_pure_natural mapping current _
                      | Dh value => exact abort_pure_natural mapping current _
                      | RootKdf value => exact abort_pure_natural mapping current _
                      | ServerComplete value => exact abort_pure_natural mapping current _
                      | BeaconComplete completed =>
                          apply bind_natural mapping id id _ _ _ _ (simulate_natural mapping _ _ (record_natural mapping setup wire) _)
                          intro opened
                          simp only [id_eq]
                          cases opened with
                          | fail error => exact abort_pure_natural mapping current _
                          | div => exact abort_pure_natural mapping current _
                          | ok outcome => cases outcome with
                            | Err previous => exact abort_pure_natural mapping current _
                            | Ok established =>
                                apply bind_natural mapping id id _ _ _ _ (effect_natural mapping _)
                                intro installed
                                simp only [id_eq]
                                cases installed with
                                | false => exact abort_pure_natural mapping current _
                                | true =>
                                    apply bind_natural mapping id id _ _ _ _ (phase_natural mapping index (.established _))
                                    intro _changed
                                    exact pure_natural mapping id _

end BeaconcryptCore.Computational.RegistrationNativeMldsaControllerMap

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaControllerMap.afterGenerated_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaControllerMap.afterGenerated_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaControllerMap.createSuffix_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaControllerMap.createSuffix_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaControllerMap.record_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaControllerMap.record_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaControllerMap.finish_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaControllerMap.finish_natural
