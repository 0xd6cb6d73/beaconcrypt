-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityFrontend

/-! Generated identity handles and fixed public prekey/PQ fields are immutable during native signing, authentication, agreement and record operations. The invariant is derived from the actual owner updates for every trusted reply, including failed signatures and failed publication. It keeps generated indices separate when public keys alias. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityMetadata
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeIdentityFrontend
open RegistrationWorldAgreementCompiler (EnvState)
variable {ι KemSK Auxiliary Value Other : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

def key (owner : Owner source) := (owner.identity, owner.prekeyPublic, owner.kemPublic)
def keys (current : State source) := current.map key

def Preserves (work : M n KemSK Auxiliary source Value) : Prop :=
  ∀ current env result, result ∈ support ((work.run current).run env) → keys result.1.2 = keys current

theorem pure_preserves (value : Value) : Preserves (pure value : M n KemSK Auxiliary source Value) := by
  intro current env result supported
  simp only [StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  rfl

theorem get_preserves : Preserves (get : M n KemSK Auxiliary source (State source)) := by
  intro current env result supported
  simp only [StateT.run_get, StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  rfl

theorem bind_preserves (work : M n KemSK Auxiliary source Value) (next : Value → M n KemSK Auxiliary source Other)
    (first : Preserves work) (later : ∀ value, Preserves (next value)) : Preserves (work >>= next) := by
  intro current env result supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  exact (later middle.1.1 middle.1.2 middle.2 result continued).trans (first current env middle reached)

theorem lift_preserves (work : StateT (EnvState Auxiliary) (OracleComp (Trusted n KemSK)) Value) :
    Preserves (StateT.lift work : M n KemSK Auxiliary source Value) := by
  intro current env result supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
  obtain ⟨middle, _reached, returned⟩ := supported
  cases returned
  rfl

theorem simulate_preserves {Index : Type} {spec : OracleSpec Index}
    (implementation : QueryImpl spec (M n KemSK Auxiliary source))
    (step : ∀ query, Preserves (implementation query)) (work : OracleComp spec Value) :
    Preserves (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure] using pure_preserves value
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact bind_preserves _ _ (step query) ih

theorem sample_preserves (work : ProbComp Value) :
    Preserves (sample (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) work) :=
  simulate_preserves (fun (query : unifSpec.Domain) => effect (.inl query)) (fun _ => lift_preserves _) work

private theorem set_found {Element : Type} (items : List Element) (index : Nat) (value : Element)
    (found : items[index]? = some value) : items.set index value = items := by
  induction items generalizing index with
  | nil => simp only [List.getElem?_nil] at found; cases found
  | cons head rest ih =>
      cases index with
      | zero => simp only [List.getElem?_cons_zero] at found; cases found; rfl
      | succ index =>
          simp only [List.getElem?_cons_succ] at found
          change head :: rest.set index value = head :: rest
          rw [ih index found]

private theorem current_preserves (index : Nat) (change : Owner source → Owner source)
    (same : ∀ owner, key (change owner) = key owner) :
    Preserves ((modify fun current => match current[index]? with
      | none => current
      | some selected => current.set index (change selected)) : M n KemSK Auxiliary source Unit) := by
  intro current env result supported
  simp only [StateT.run_modify, StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  cases found : current[index]? with
  | none => simp only []
  | some selected =>
      simp only [keys, List.map_set, same]
      apply set_found
      simp only [List.getElem?_map, found, Option.map_some]

theorem phase_preserves (index : Nat) (phase : RegistrationNativeBeaconFrontend.Phase) :
    Preserves (updatePhase (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) index phase) :=
  current_preserves index (fun owner => { owner with phase }) (fun _ => rfl)

theorem history_preserves (index : Nat) (message : Pqxdh.Bytes) (value : PqxdhEd25519EufCma.Ed25519Signature) :
    Preserves (logEd (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) index message value) :=
  current_preserves index (fun owner => { owner with edHistory := owner.edHistory ++ [.signed message value] }) (fun _ => rfl)

theorem outgoing_preserves (setup : Setup base KemSK) (index : Nat) (owner : Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    Preserves (outgoing (n := n) (Auxiliary := Auxiliary) setup source index owner query) := by
  classical
  cases query with
  | inl query => cases query with
    | hash request => exact lift_preserves _
    | sign request payload digest =>
        exact bind_preserves _ _ (sample_preserves _) (fun _ => bind_preserves _ _ (lift_preserves _) (fun _ => pure_preserves _))
  | inr request =>
      simp only [outgoing]
      split
      · apply bind_preserves _ _ (lift_preserves _)
        intro value
        cases value with
        | none => exact pure_preserves _
        | some value => exact bind_preserves _ _ (history_preserves index _ value) (fun _ => pure_preserves _)
      · exact pure_preserves _

theorem authentication_preserves (setup : Setup base KemSK) (query : RegistrationAuthenticationExecutor.Request) :
    Preserves (authentication (n := n) (Auxiliary := Auxiliary) setup source query) := by
  cases query with
  | hash request => exact bind_preserves _ _ (lift_preserves _) (fun _ => pure_preserves _)
  | mldsa request | ed25519 request => exact pure_preserves _

theorem primitive_preserves (setup : Setup base KemSK) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementShared.PrimitiveSpec.Domain) :
    Preserves (primitive (n := n) (Auxiliary := Auxiliary) setup owner oneTime query) := by
  cases query with
  | convertSecret role => cases role <;> first | exact pure_preserves _ | exact lift_preserves _
  | dh request => cases role : request.secret_role <;>
      simp only [primitive, role] <;> exact lift_preserves _
  | convertPublic key | generate role | encapsulate key | decapsulate ciphertext => exact lift_preserves _

theorem agreement_preserves (setup : Setup base KemSK) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementExecutor.Request) :
    Preserves (agreement (n := n) (Auxiliary := Auxiliary) setup owner oneTime query) := by
  apply bind_preserves _ _ (lift_preserves _)
  intro _
  cases query with
  | convertPublic key | convertSecret role | generate role | encapsulate key | decapsulate ciphertext | dh request =>
      simp only [agreementCore]
      exact primitive_preserves setup owner oneTime _
  | root request => exact pure_preserves _

theorem record_preserves (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (query : RegistrationRecordPrimitives.Spec.Domain) :
    Preserves (record (n := n) (Auxiliary := Auxiliary) (source := source) setup wire query) := lift_preserves _

theorem abort_preserves (owner : Owner source) : Preserves (abort (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) owner) :=
  bind_preserves _ _ (lift_preserves _) (fun _ => pure_preserves _)

end BeaconcryptCore.Computational.RegistrationNativeIdentityMetadata

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMetadata.pure_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMetadata.pure_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMetadata.get_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMetadata.get_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMetadata.bind_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMetadata.bind_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMetadata.lift_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMetadata.lift_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMetadata.simulate_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMetadata.simulate_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMetadata.sample_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMetadata.sample_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMetadata.phase_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMetadata.phase_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMetadata.history_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMetadata.history_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMetadata.outgoing_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMetadata.outgoing_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMetadata.authentication_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMetadata.authentication_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMetadata.primitive_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMetadata.primitive_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMetadata.agreement_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMetadata.agreement_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMetadata.record_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMetadata.record_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMetadata.abort_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMetadata.abort_preserves
