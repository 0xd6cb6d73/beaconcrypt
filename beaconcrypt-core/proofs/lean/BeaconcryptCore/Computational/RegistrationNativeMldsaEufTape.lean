-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaEager
import BeaconcryptCore.Computational.RegistrationNativeMldsaChosenProgram

/-! An eager ordinary-EUF reduction retains ordinary private keys and one public challenge token. The token has no private key field. Actual restoration is an analysis-only map using the challenger's key; complete adaptive source execution and every failed signing attempt are preserved after erasing the challenger's private query history. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaEufTape
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (handleSource Attempt)
open RegistrationNativeMldsaEuf (PublicKey)
variable {Value : Type} (source : Source)

/-- None is the public challenge token; ordinary rows contain only reduction-owned keys. -/
abbrev Token := Option (Credential source)
structure Pool where
  keys : List (Token source) := []
  bornAt : List Nat := []
  attempts : Nat := 0
  signing : List Attempt := []

def restoreKey (challenge : Credential source) : Token source → Credential source
  | none => challenge
  | some key => key

def restore (challenge : Credential source) (before : Pool source) : RegistrationNativeMldsaOpaque.Pool source :=
  ⟨before.keys.map (restoreKey source challenge), before.bornAt, before.attempts, before.signing⟩

def restoreTape (challenge : Credential source) (tape : List (Option (Token source))) : List (Option (Credential source)) :=
  tape.map (Option.map (restoreKey source challenge))

def birth (publicKey : PublicKey) (before : Pool source) (generated : Option (Token source)) :
    (Option (Credential (handleSource source)) × Nat) × Pool source :=
  match generated with
  | none => ((none, 0), {before with attempts := before.attempts + 1})
  | some key => ((some ⟨key.elim publicKey Credential.publicKey, before.keys.length⟩, 0),
      {before with keys := before.keys ++ [key], bornAt := before.bornAt ++ [before.attempts], attempts := before.attempts + 1})

def record (before : Pool source) (handle : Credential (handleSource source))
    (request : registration.MldsaSigningRequest) (reply : RegistrationSigningShared.SignReply) : Pool source :=
  {before with signing := before.signing ++ [⟨handle.secret, handle.publicKey, request, reply⟩]}

noncomputable def handler (publicKey : PublicKey) (tape : List (Option (Token source))) :
    QueryImpl (RegistrationNativeMldsaProgram.Spec (handleSource source))
      (StateT (Pool source) (OracleComp RegistrationNativeMldsaEuf.Spec)) := by
  classical
  exact fun query => match query with
  | .inl coin => StateT.lift (RegistrationNativeMldsaChosen.coins coin)
  | .inr .generate => fun before => pure (birth source publicKey before ((tape[before.attempts]?).getD none))
  | .inr (.sign handle request) => fun before =>
      match before.keys[handle.secret]? with
      | none => pure ((.None, 0), record source before handle request .None)
      | some key => if handle.publicKey = key.elim publicKey Credential.publicKey then
          match key with
          | some ordinary => (fun reply => ((reply, 0), record source before handle request reply)) <$>
              RegistrationNativeMldsaChosen.lift (RegistrationNativeMldsa.owned source ordinary request)
          | none => (fun reply => ((reply, 0), record source before handle request reply)) <$>
              RegistrationNativeMldsaEuf.Spec.query (.inr request)
        else pure ((.None, 0), record source before handle request .None)

noncomputable def evaluate (publicKey : PublicKey) (tape : List (Option (Token source)))
    (work : OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source)) Value) (before : Pool source) :
    OracleComp RegistrationNativeMldsaEuf.Spec (Value × Pool source) :=
  (simulateQ (handler source publicKey tape) work).run before

private theorem birth_restore (challenge : Credential source) (before : Pool source) (generated : Option (Token source)) :
    Prod.map id (restore source challenge) (birth source challenge.publicKey before generated) =
      RegistrationNativeMldsaOpaque.birth source (restore source challenge before)
        (generated.map (restoreKey source challenge), 0) := by
  cases generated with
  | none => rfl
  | some key =>
      cases key <;> simp only [birth, restore, restoreKey, Option.map_some,
        Prod.map, id_eq, List.map_append, List.map_cons, List.map_nil, List.length_map,
        RegistrationNativeMldsaOpaque.birth, Option.elim_none, Option.elim_some]

private theorem record_restore (challenge : Credential source) (before : Pool source)
    (handle : Credential (handleSource source)) (request : registration.MldsaSigningRequest)
    (reply : RegistrationSigningShared.SignReply) :
    restore source challenge (record source before handle request reply) =
      RegistrationNativeMldsaOpaque.record source (restore source challenge before) handle request reply := rfl

private theorem tape_lookup (challenge : Credential source) (tape : List (Option (Token source))) (attempt : Nat) :
    ((restoreTape source challenge tape)[attempt]?).getD none =
      ((tape[attempt]?).getD none).map (restoreKey source challenge) := by
  simp only [restoreTape, List.getElem?_map]
  cases tape[attempt]? <;> rfl

/-- Each routed call returns the exact source reply and restored private table, independently of the challenger's earlier signing history. -/
theorem query (challenge : Credential source) (tape : List (Option (Token source)))
    (request : (RegistrationNativeMldsaProgram.Spec (handleSource source)).Domain)
    (before : Pool source) (history : List registration.MldsaSigningRequest) :
    (fun result => (result.1.1, restore source challenge result.1.2)) <$>
      RegistrationNativeMldsaChosenProgram.interpreted source challenge
        ((handler source challenge.publicKey tape request).run before) history =
      (RegistrationNativeMldsaEager.handler source (restoreTape source challenge tape) request).run (restore source challenge before) := by
  classical
  cases request with
  | inl coin =>
      simp only [handler, StateT.run_lift, bind_pure_comp,
        RegistrationNativeMldsaChosenProgram.interpreted, RegistrationNativeMldsaChosen.coins,
        simulateQ_map, simulateQ_spec_query, RegistrationNativeMldsaEuf.handler,
        StateT.run_map, StateT.run_lift, bind_pure_comp, Functor.map_map,
        RegistrationNativeMldsaEager.handler, RegistrationNativeMldsaZeroSource.handler]
  | inr request => cases request with
    | generate =>
        change (fun result => (result.1.1, restore source challenge result.1.2)) <$>
          pure (birth source challenge.publicKey before ((tape[before.attempts]?).getD none), history) =
          pure (RegistrationNativeMldsaOpaque.birth source (restore source challenge before)
            (((restoreTape source challenge tape)[before.attempts]?).getD none, 0))
        rw [map_pure, tape_lookup]
        exact congrArg pure (birth_restore source challenge before _)
    | sign handle request =>
        simp only [handler, StateT.run, RegistrationNativeMldsaEager.handler,
          RegistrationNativeMldsaZeroSource.handler, RegistrationNativeMldsaZeroSource.capability,
          restore, List.getElem?_map]
        cases found : before.keys[handle.secret]? with
        | none =>
            simp only [Option.map_none, RegistrationNativeMldsaChosenProgram.interpreted,
              simulateQ_pure, StateT.run_pure, map_pure]
            rfl
        | some key =>
            simp only [Option.map_some]
            cases key with
            | some ordinary =>
                simp only [Option.elim_some, restoreKey]
                by_cases owned : handle.publicKey = ordinary.publicKey
                · simp only [owned, ite_true, RegistrationNativeMldsaChosenProgram.interpreted,
                    simulateQ_map, StateT.run_map, Functor.map_map]
                  change (fun result => ((result.1, (0 : Nat)), restore source challenge (record source before handle request result.1))) <$>
                    RegistrationNativeMldsaChosenProgram.interpreted source challenge
                      (RegistrationNativeMldsaChosen.lift (RegistrationNativeMldsa.owned source ordinary request)) history = _
                  rw [RegistrationNativeMldsaChosenProgram.ordinary]
                  simp only [Functor.map_map, record_restore]
                  rfl
                · simp only [owned, ite_false, RegistrationNativeMldsaChosenProgram.interpreted,
                    simulateQ_pure, StateT.run_pure, map_pure]
                  rfl
            | none =>
                simp only [Option.elim_none, restoreKey]
                by_cases owned : handle.publicKey = challenge.publicKey
                · simp only [owned, ite_true, RegistrationNativeMldsaChosenProgram.interpreted,
                    simulateQ_map, simulateQ_spec_query, StateT.run_map,
                    RegistrationNativeMldsaEuf.handler]
                  have same := congrArg (fun work => (fun reply => ((reply, (0 : Nat)),
                      RegistrationNativeMldsaOpaque.record source (restore source challenge before) handle request reply)) <$> work)
                    (RegistrationNativeMldsaEuf.signing_owned source challenge request history)
                  simp only [Functor.map_map] at same
                  simp only [Functor.map_map]
                  convert same using 1 <;> rfl
                · simp only [owned, ite_false, RegistrationNativeMldsaChosenProgram.interpreted,
                    simulateQ_pure, StateT.run_pure, map_pure]
                  rfl

/-- Restoring the challenge token preserves every complete adaptive execution, including invalid handles, failed replies and all native continuation state. -/
theorem program (challenge : Credential source) (tape : List (Option (Token source)))
    (work : OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source)) Value)
    (before : Pool source) (history : List registration.MldsaSigningRequest) :
    (fun result => (result.1.1, restore source challenge result.1.2)) <$>
      RegistrationNativeMldsaChosenProgram.interpreted source challenge
        (evaluate source challenge.publicKey tape work before) history =
      (simulateQ (RegistrationNativeMldsaEager.handler source (restoreTape source challenge tape)) work).run
        (restore source challenge before) := by
  induction work using OracleComp.inductionOn generalizing before history with
  | pure value =>
      simp only [evaluate, RegistrationNativeMldsaChosenProgram.interpreted,
        simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind request next ih =>
      simp only [evaluate, RegistrationNativeMldsaChosenProgram.interpreted,
        simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      change (RegistrationNativeMldsaChosenProgram.interpreted source challenge
          ((handler source challenge.publicKey tape request).run before) history >>= fun middle =>
          (fun result => (result.1.1, restore source challenge result.1.2)) <$>
            RegistrationNativeMldsaChosenProgram.interpreted source challenge
              (evaluate source challenge.publicKey tape (next middle.1.1) middle.1.2) middle.2) = _
      simp_rw [ih]
      have same := query source challenge tape request before history
      rw [← same, bind_map_left]

/-- The single challenged attempt contains a public token; every other tape entry contains only its independently generated ordinary key. -/
def selectedTape {count : Nat} (target : Fin (count + 1))
    (others : Fin count → Option (Credential source)) : List (Option (Token source)) :=
  List.ofFn (target.insertNth (some none) (fun index => (others index).map some))

/-- Analysis-only restoration of the public token reconstructs the exact selected source-generation family. -/
theorem selected_tape (challenge : Credential source) {count : Nat} (target : Fin (count + 1))
    (others : Fin count → Option (Credential source)) :
    restoreTape source challenge (selectedTape source target others) =
      List.ofFn (target.insertNth (some challenge) others) := by
  simp only [restoreTape, selectedTape, List.map_ofFn]
  congr 1
  funext index
  induction index using Fin.succAboveCases target with
  | x => simp only [Function.comp_apply, Fin.insertNth_apply_same, Option.map_some, restoreKey]
  | p other =>
      simp only [Function.comp_apply, Fin.insertNth_apply_succAbove]
      cases others other <;> rfl

/-- The ordinary challenger and the actual source tape have identical complete replies and restored native continuation states for the chosen successful generation attempt. -/
theorem selected_program (challenge : Credential source) {count : Nat} (target : Fin (count + 1))
    (others : Fin count → Option (Credential source))
    (work : OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source)) Value)
    (history : List registration.MldsaSigningRequest) :
    (fun result => (result.1.1, restore source challenge result.1.2)) <$>
      RegistrationNativeMldsaChosenProgram.interpreted source challenge
        (evaluate source challenge.publicKey (selectedTape source target others) work {}) history =
      (simulateQ (RegistrationNativeMldsaEager.handler source
        (List.ofFn (target.insertNth (some challenge) others))) work).run {} := by
  simpa only [selected_tape, restore, List.map_nil] using
    program source challenge (selectedTape source target others) work {} history
end BeaconcryptCore.Computational.RegistrationNativeMldsaEufTape

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaEufTape.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaEufTape.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaEufTape.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaEufTape.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaEufTape.selected_tape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaEufTape.selected_tape

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaEufTape.selected_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaEufTape.selected_program
