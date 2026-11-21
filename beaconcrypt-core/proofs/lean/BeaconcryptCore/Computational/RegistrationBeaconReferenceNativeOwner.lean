-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeAuthentication
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativePostRoot
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeCallbacks

/-! The actual finishing controller has one mutable owner phase. Its incoming authentication, agreement and first-record callbacks do not read or change the owner roster. This finite source view keeps all real private owner fields inside the interpreter and preserves every reached local environment and World effect. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeOwner
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeBeaconFrontend (Owner Trusted)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceCompiler (eraseOwner)
variable {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

abbrev M (n : Nat) (KemSK Auxiliary : Type) (source : RegistrationNativeMldsa.Source) :=
  StateT (Owner source) (StateT (EnvState Auxiliary) (OracleComp (Trusted n KemSK)))

noncomputable def record (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (query : RegistrationRecordPrimitives.Request) :
    StateT (EnvState Auxiliary) (OracleComp (Trusted n KemSK)) (RegistrationRecordPrimitives.Spec.Range query) :=
  Prod.fst <$> (RegistrationNativeBeaconFrontend.record setup wire query).run ([] : List (Owner mlSource))

/-- Native record callbacks retain the current owner roster before any continuation resumes. -/
theorem record_owned (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (query : RegistrationRecordPrimitives.Request) :
    RegistrationNativeBeaconFrontend.record (n := n) (mldsaSource := mlSource) (Auxiliary := Auxiliary) setup wire query =
      StateT.lift (record (mlSource := mlSource) setup wire query) := by
  apply StateT.ext
  intro owners
  apply StateT.ext
  intro env
  simp only [record, StateT.run_lift, StateT.run_map, bind_pure_comp, Functor.map_map]
  cases query <;> first | rfl | (rename_i writing; cases writing <;> rfl)

theorem record_program (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (work : OracleComp RegistrationRecordPrimitives.Spec Value) :
    simulateQ (RegistrationNativeBeaconFrontend.record (n := n) (mldsaSource := mlSource)
      (Auxiliary := Auxiliary) setup wire) work =
      StateT.lift (simulateQ (record (mlSource := mlSource) setup wire) work) := by
  have same : RegistrationNativeBeaconFrontend.record (n := n) (mldsaSource := mlSource)
      (Auxiliary := Auxiliary) setup wire =
      QueryImpl.liftTarget (RegistrationNativeBeaconFrontend.M n KemSK mlSource Auxiliary)
        (record (n := n) (Auxiliary := Auxiliary) (mlSource := mlSource) setup wire) := by
    funext query
    rw [QueryImpl.liftTarget_apply]
    exact record_owned setup wire query
  rw [same, simulateQ_liftTarget]
  rfl

noncomputable def authentication (setup : Setup base KemSK) (mlSource : RegistrationNativeMldsa.Source)
    (work : OracleComp RegistrationAuthenticationExecutor.Spec Value) :
    StateT (EnvState Auxiliary) (OracleComp (Trusted n KemSK)) Value :=
  StateT.lift (simulateQ RegistrationBeaconReferenceNativeRecord.environment
    (simulateQ (RegistrationAuthenticationCompiler.callbacks setup.source.crypto mlSource.verify) work))

def abort (owner : Owner mlSource) : M n KemSK Auxiliary mlSource Unit := do
  let _ ← StateT.lift (StateT.lift ((Trusted n KemSK).query (.inl (.inr (.advanceOwner owner.worldOwner .aborted)))))
  pure ()

private theorem abort_frame (owner current : Owner mlSource) (owners : RegistrationNativeBeaconFrontend.State mlSource)
    (index : Nat) (answer : Value) (env : EnvState Auxiliary) :
    (((RegistrationNativeBeaconFrontend.abort owner *> pure answer :
      RegistrationNativeBeaconFrontend.M n KemSK mlSource Auxiliary Value).run (owners.set index current)).run env) =
      (fun result => ((result.1.1, owners.set index result.1.2), result.2)) <$>
        (((abort owner *> pure answer : M n KemSK Auxiliary mlSource Value).run current).run env) := by
  simp only [RegistrationNativeBeaconFrontend.abort, abort, RegistrationNativeBeaconFrontend.effect,
    seqRight_eq_bind, StateT.run_lift, bind_pure_comp, StateT.run_map, Functor.map_map]
  rfl

def after (owner : Owner mlSource) :
    RustM RegistrationBeaconRecordExecutor.Result → M n KemSK Auxiliary mlSource (RustM (Option Pqxdh.Bytes))
  | .fail error => abort owner *> pure (.fail error)
  | .div => abort owner *> pure .div
  | .ok (.Err _) => abort owner *> pure (.ok none)
  | .ok (.Ok established) => do
      let installed : Bool ← StateT.lift (StateT.lift ((Trusted n KemSK).query (.inl (.inr (.installBeacon owner.worldOwner
        ⟨owner.pin.binding.identity_key_id, established.control, established.binding.associated_data⟩ (.known established.kernel))))))
      if installed then
        modify fun current => { current with phase := .established ⟨established.control, established.binding, established.application⟩ }
        pure (.ok (some (TranscriptAuthParts.absSlice established.application)))
      else abort owner *> pure (.ok none)

noncomputable def finish (setup : Setup base KemSK) (mlSource : RegistrationNativeMldsa.Source)
    (wire : RegistrationNativeWire.Wire) (packet : Option registration.ResponsePacket) :
    M n KemSK Auxiliary mlSource (RustM (Option Pqxdh.Bytes)) := do
  let owner ← get
  match owner.phase with
  | .initSent pending oneTime =>
      match pending.aborted_state with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok aborted => do
          modify fun current => { current with phase := .aborted aborted }
          let authenticated ← StateT.lift (authentication setup mlSource
            (RegistrationResponseExecutor.begin pending (match packet with | none => .None | some value => .Some value)))
          match authenticated with
          | .fail error => abort owner *> pure (.fail error)
          | .div => abort owner *> pure .div
          | .ok (.Err _) => abort owner *> pure (.ok none)
          | .ok (.Ok accepted) => do
              let agreed ← StateT.lift (simulateQ (RegistrationBeaconReferenceNativeCallbacks.source setup
                owner.prekeyScalar (eraseOwner owner) oneTime) (RegistrationAgreementExecutor.beacon accepted))
              match agreed with
              | .fail error => abort owner *> pure (.fail error)
              | .div => abort owner *> pure .div
              | .ok (.BeaconComplete completed) => do
                  let opened ← StateT.lift (simulateQ (record (mlSource := mlSource) setup wire) (RegistrationBeaconRecordExecutor.begin completed))
                  after owner opened
              | .ok _ => abort owner *> pure (.ok none)
  | _ => pure (.ok none)

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

private theorem set_twice {Element : Type} (items : List Element) (index : Nat) (first second : Element) :
    (items.set index first).set index second = items.set index second := by
  induction items generalizing index with
  | nil => rfl
  | cons head rest ih =>
      cases index with
      | zero => rfl
      | succ index =>
          change head :: (rest.set index first).set index second = head :: rest.set index second
          rw [ih]

private theorem agreement_program (setup : Setup base KemSK) (owner : Owner mlSource)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (work : OracleComp RegistrationAgreementExecutor.Spec Value) :
    simulateQ (RegistrationNativeBeaconFrontend.agreement (n := n) (Auxiliary := Auxiliary) setup owner oneTime) work =
      StateT.lift (simulateQ (RegistrationBeaconReferenceNativeCallbacks.source setup owner.prekeyScalar
        (eraseOwner owner) oneTime) work) := by
  simpa only [RegistrationBeaconReferenceCompiler.restore_erase] using
    RegistrationBeaconReferenceNativeCallbacks.owned_program (n := n) (Auxiliary := Auxiliary) setup owner.prekeyScalar
      (eraseOwner owner) oneTime work

/-- The actual roster controller is exactly the one-owner native source controller, with its complete final owner written back at the same index. -/
theorem finish_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (packet : Option registration.ResponsePacket)
    (owners : RegistrationNativeBeaconFrontend.State mlSource) (owner : Owner mlSource)
    (found : owners[index]? = some owner) (env : EnvState Auxiliary) :
    ((RegistrationNativeBeaconFrontend.finish (n := n) setup mlSource wire index packet).run owners).run env =
      (fun result => ((result.1.1, owners.set index result.1.2), result.2)) <$>
        ((finish setup mlSource wire packet).run owner).run env := by
  obtain ⟨within, _⟩ := List.getElem?_eq_some_iff.mp found
  have same := set_found owners index owner found
  cases phase : owner.phase with
  | fresh | freshWithCoins scalar | established completed | aborted aborted =>
      simp only [RegistrationNativeBeaconFrontend.finish, finish, StateT.run_bind, StateT.run_get,
        pure_bind, found, phase, StateT.run_pure, map_pure, same]
  | initSent pending oneTime =>
      simp only [RegistrationNativeBeaconFrontend.finish, finish, StateT.run_bind, StateT.run_get,
        pure_bind, found, phase]
      cases moved : pending.aborted_state with
      | fail error | div => simp only [StateT.run_pure, map_pure, same]
      | ok aborted =>
          simp only [RegistrationNativeBeaconFrontend.updatePhase, StateT.run_modify, found, pure_bind,
            RegistrationBeaconReferenceNativeAuthentication.program, agreement_program, record_program,
            StateT.run_bind, StateT.run_lift, authentication, bind_pure_comp,
            bind_map_left, map_bind]
          apply bind_congr
          intro authenticated
          cases authenticated with
          | fail error | div => exact abort_frame _ _ _ _ _ _
          | ok response => cases response with
            | Err error => exact abort_frame _ _ _ _ _ _
            | Ok accepted =>
                simp only [StateT.run_bind, StateT.run_lift, bind_pure_comp,
                  bind_map_left, map_bind]
                apply bind_congr
                rintro ⟨agreed, afterEnv⟩
                cases agreed with
                | fail error | div => exact abort_frame _ _ _ _ _ _
                | ok effect =>
                    cases effect <;> try exact abort_frame _ _ _ _ _ _
                    rename_i completed
                    simp only [StateT.run_bind, StateT.run_lift, bind_pure_comp,
                      bind_map_left, map_bind]
                    apply bind_congr
                    rintro ⟨opened, recordEnv⟩
                    cases opened with
                    | fail error | div => exact abort_frame _ _ _ _ _ _
                    | ok result => cases result with
                      | Err error => exact abort_frame _ _ _ _ _ _
                      | Ok established =>
                          simp only [after, RegistrationNativeBeaconFrontend.effect, StateT.run_bind,
                            StateT.run_lift, bind_pure_comp, bind_map_left, map_bind]
                          apply bind_congr
                          intro installed
                          cases installed with
                          | false => exact abort_frame _ _ _ _ _ _
                          | true =>
                              simp only [↓reduceIte, StateT.run_map, StateT.run_modify, StateT.run_pure,
                                List.getElem?_set_self within, map_pure, set_twice]

end BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeOwner

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeOwner.record_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeOwner.record_owned

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeOwner.record_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeOwner.record_program

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeOwner.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeOwner.finish_source
