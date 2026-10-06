-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemGame

/-! Structural query accounting for the actual source compiler with its encapsulation callback exposed. Bounds quantify over every typed reply, including optional failure, before any real or random challenger is selected. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedCounts
open PqxdhRegistrationJointKemEncapsulation PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhRegistrationJointServiceCosts (Kind poolClass classify)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result Local : Type}

/-- The actual exposed encapsulation request, independent of its raw bytes or public key. -/
def IsEncapsulation : (Spec KemSK).Domain → Prop
  | .inl _ => False
  | .inr _ => True
instance : DecidablePred (IsEncapsulation (KemSK := KemSK)) := fun query => by
  cases query
  · exact inferInstanceAs (Decidable False)
  · exact inferInstanceAs (Decidable True)

/-- Forwarding preserves a bound under the exact predicate pullback, for every complete adaptive private-service program. -/
theorem forward_bound (work : OracleComp (PqxdhLiveKemBirth.Spec KemSK) Result)
    (predicate : (Spec KemSK).Domain → Prop) [DecidablePred predicate] (cap : Nat)
    (bounded : work.IsQueryBoundP (fun query => predicate (.inl query)) cap) :
    (simulateQ forward work).IsQueryBoundP predicate cap := by
  exact bounded.simulateQ_of_step
    (fun query chosen => by simp [forward, isQueryBoundP_query_iff, chosen])
    (fun query excluded => by simp [forward, isQueryBoundP_query_iff, excluded])

/-- A lifted old service program cannot create an exposed encapsulation request. Its native and primitive work still executes. -/
theorem lift_no_encapsulation (work : StateT Local (OracleComp (PqxdhLiveKemBirth.Spec KemSK)) Result)
    (state : Local) : ((PqxdhRegistrationJointKemEncapsulation.lift work).run state).IsQueryBoundP (IsEncapsulation (KemSK := KemSK)) 0 := by
  exact forward_bound _ _ 0 (isQueryBoundP_false _ 0)

/-- The exact collector callback contributes one exposed request precisely in its original encapsulation class. -/
theorem prefix_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (raw : Pqxdh.Bytes)
    (query : (PqxdhRegistrationJointServerPrefix.NativeSpec Reader).Domain) (consumed : List Pqxdh.Bytes) :
    ((simulateQ (prefixImpl setup codec checks raw)
      (PqxdhRegistrationJointServerPrefix.compiler (KemSK := KemSK) identityIndex query)).run consumed).IsQueryBoundP
      (IsEncapsulation (KemSK := KemSK))
      (if PqxdhServerAuthSourceCosts.serverClass query = .encapsulate then 1 else 0) := by
  cases query <;> simp only [PqxdhRegistrationJointServerPrefix.compiler, simulateQ_map,
    simulateQ_spec_query, StateT.run_map, PqxdhServerAuthSourceCosts.serverClass]
  case staticDh point => simp [prefixImpl, StateT.run, forward, isQueryBoundP_map_iff, isQueryBoundP_query_iff, IsEncapsulation]
  case encapsulate key => simp [prefixImpl, StateT.run, isQueryBoundP_map_iff, isQueryBoundP_query_iff, IsEncapsulation]
  all_goals exact forward_bound _ _ 0 (isQueryBoundP_false _ 0)

set_option backward.isDefEq.respectTransparency false in
/-- One actual raw acceptance prefix has at most one exposed encapsulation, including all parser, verification and freshness failures. -/
theorem prefix_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (raw : Pqxdh.Bytes) (consumed : List Pqxdh.Bytes) :
    ((simulateQ (prefixImpl setup codec checks raw)
      (PqxdhRegistrationJointServerPrefix.clientPrefix identityIndex raw)).run consumed).IsQueryBoundP
      (IsEncapsulation (KemSK := KemSK)) 1 := by
  rw [PqxdhRegistrationJointServerPrefix.clientPrefix, ← QueryImpl.simulateQ_compose]
  have bounded := PqxdhServerAuthSourceCosts.server_callbacks
    (Reader := Reader) (E := PqxdhJointGapDh.ScalarBytes) (Shared := PqxdhBeaconPhase2Preparation.Word32) raw .encapsulate
  exact bounded.simulateQ_run_of_step
    (fun query counted state => by simpa only [QueryImpl.apply_compose, ite_eq_left counted] using prefix_step setup codec checks identityIndex raw query state)
    (fun query excluded state => by simpa only [QueryImpl.apply_compose, ite_eq_right excluded] using prefix_step setup codec checks identityIndex raw query state)
    consumed

/-- The full actual acceptance adds no exposed request before or after its original collector. -/
theorem accept_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PqxdhJointIdentity.PublicIdentity) (raw : Pqxdh.Bytes)
    (state : NativeState KemSK) :
    ((accept setup codec checks identityIndex publicIdentity raw).run state).IsQueryBoundP
      (IsEncapsulation (KemSK := KemSK)) 1 := by
  simp only [accept, StateT.run_bind]
  rw [← Nat.zero_add 1]
  apply isQueryBoundP_bind (lift_no_encapsulation _ state)
  intro before _
  exact isQueryBoundP_bind (m := 0)
    (by simpa only [prepare, StateT.run, isQueryBoundP_map_iff] using
      prefix_bound setup codec checks identityIndex raw before.2.2.server.consumed)
    (fun collected _ => lift_no_encapsulation _ collected.2)

set_option backward.isDefEq.respectTransparency false in
/-- An exposed request can arise only from the actual Server-accept backend callback, with cap one for every possible intermediate service reply. -/
theorem backend_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (query : (PqxdhRegistrationJointServiceSchedule.Spec KemSK Response).Domain) (state : NativeState KemSK) :
    ((impl setup codec checks identityIndex publicIdentity query).run state).IsQueryBoundP
      (IsEncapsulation (KemSK := KemSK)) (if classify (KemSK := KemSK) query = .accept then 1 else 0) := by
  rcases query with (service | tail) | shared
  case inl.inl =>
    have excluded : poolClass (KemSK := KemSK) service ≠ .accept := by
      rcases service with (coin | service) | (coin | service)
      all_goals simp [poolClass]
      case inl.inr =>
        cases service <;> first | simp | skip
        case service index call => cases call <;> simp
      case inr.inr => cases service <;> simp
    simpa only [impl, classify, ite_eq_right excluded] using lift_no_encapsulation
      (PqxdhRegistrationJointOpenBackend.impl setup codec checks identityIndex publicIdentity (.inl (.inl service))) state
  case inl.inr => exact lift_no_encapsulation _ state
  case inr => cases shared <;> first | exact accept_bound setup codec checks identityIndex publicIdentity _ state | exact lift_no_encapsulation _ state

set_option backward.isDefEq.respectTransparency false in
/-- The complete adaptive source command interface emits at most qAccept actual encapsulation requests, counting unsuccessful accepted-parser paths and repeated equal public keys. -/
theorem command_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (work : OracleComp (PqxdhRegistrationJointKemCommands.SourceSpec KemSK) Result)
    (budget : PqxdhRegistrationJointKemCommands.Budget)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) (state : NativeState KemSK) :
    (commands setup codec checks identityIndex publicIdentity work owners state).IsQueryBoundP
      (IsEncapsulation (KemSK := KemSK)) (budget (.inl 3)) := by
  have bounded := PqxdhRegistrationJointRevealCosts.program_bound setup codec work budget certified owners .accept
  exact bounded.simulateQ_run_of_step
    (fun query counted before => by simpa only [ite_eq_left counted] using backend_step setup codec checks identityIndex publicIdentity query before)
    (fun query excluded before => by simpa only [ite_eq_right excluded] using backend_step setup codec checks identityIndex publicIdentity query before)
    state

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedCounts

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedCounts.forward_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedCounts.forward_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedCounts.lift_no_encapsulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedCounts.lift_no_encapsulation

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedCounts.prefix_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedCounts.prefix_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedCounts.prefix_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedCounts.prefix_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedCounts.accept_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedCounts.accept_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedCounts.backend_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedCounts.backend_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedCounts.command_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemExposedCounts.command_bound
