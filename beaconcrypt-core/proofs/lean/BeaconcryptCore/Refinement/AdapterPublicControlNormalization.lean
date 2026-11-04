-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationCodecControlNormalization
import BeaconcryptCore.Extraction.Funs

/-! Algebra for the checked public-wrapper extraction preparation. All leaves retain arbitrary effects, including a shared mutable platform state. Returning, breaking, continuing and unwinding short circuit their enclosing block; moving a continuation into a switch does not execute it after such an exit. The source checker retains every branch selector and operation operand. The DH normalization distributes the original optional borrowed-key view into its consuming scalar multiplication, and the Init normalization only returns the two original loop exits to its caller. -/

set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Refinement.AdapterPublicControlNormalization

universe v
variable {m : Type → Type v} [Monad m] [LawfulMonad m]
variable {S R A B : Type}

inductive Outcome (S R : Type) where
  | next (state : S)
  | returned (result : R)
  | broke (depth : Nat) (state : S)
  | continued (depth : Nat) (state : S)
  | unwound

def onward (next : S → m (Outcome S R)) : Outcome S R → m (Outcome S R)
  | .next state => next state
  | .returned result => pure (.returned result)
  | .broke depth state => pure (.broke depth state)
  | .continued depth state => pure (.continued depth state)
  | .unwound => pure .unwound

theorem branch_tail
    (tree : RegistrationCodecControlNormalization.Tree m (Outcome S R))
    (next : S → m (Outcome S R)) :
    RegistrationCodecControlNormalization.cps (onward next) tree =
      (RegistrationCodecControlNormalization.evaluate tree >>= onward next) :=
  RegistrationCodecControlNormalization.cps_preserves tree (onward next)

theorem terminal_tail (result : Outcome S R) (terminal : ∀ state, result ≠ .next state)
    (next : S → m (Outcome S R)) :
    (pure result >>= onward next) = (pure result : m (Outcome S R)) := by
  rw [pure_bind]
  cases result with
  | next state => exact False.elim (terminal state rfl)
  | returned result => rfl
  | broke depth state => rfl
  | continued depth state => rfl
  | unwound => rfl

omit [Monad m] [LawfulMonad m] in
theorem loop_congr
    (iterate : (S → m (Outcome S R)) → S → m R)
    (left right : S → m (Outcome S R)) (same : ∀ state, left state = right state)
    (initial : S) : iterate left initial = iterate right initial := by
  have equal : left = right := funext same
  rw [equal]

inductive InitExit (A : Type) where
  | rejected
  | ready (value : A)

def initOption : InitExit A → Option A
  | .rejected => none
  | .ready value => some value

theorem init_loop_factor (work : m (InitExit A)) (next : A → m (Option B)) :
    (do
      let ready ← initOption <$> work
      match ready with
      | none => pure none
      | some value => next value) =
    (do
      let exit ← work
      match exit with
      | .rejected => pure none
      | .ready value => next value) := by
  rw [bind_map_left]
  apply bind_congr
  intro exit
  cases exit <;> rfl

omit [Monad m] [LawfulMonad m] in
theorem option_view_bind (input : Option A) (view : A → B) (consume : B → Option R) :
    (input.map view).bind consume = input.bind (fun key => consume (view key)) := by
  cases input <;> rfl

omit [Monad m] [LawfulMonad m] in
theorem dh_selection
    (role : beaconcrypt_core.agreement.DhSecretRole)
    {L E P O : Type}
    (localIdentity : Option L) (serverEphemeral : Option E)
    (beaconPrekey : Option P) (beaconOneTime : Option O)
    (localView : L → B) (serverView : E → B)
    (prekeyView : P → B) (oneTimeView : O → B) (consume : B → Option R) :
    ((match role with
      | .LocalIdentity => localIdentity.map localView
      | .ServerEphemeral => serverEphemeral.map serverView
      | .BeaconPrekey => beaconPrekey.map prekeyView
      | .BeaconOneTime => beaconOneTime.map oneTimeView).bind consume) =
    (match role with
      | .LocalIdentity => localIdentity.bind (fun key => consume (localView key))
      | .ServerEphemeral => serverEphemeral.bind (fun key => consume (serverView key))
      | .BeaconPrekey => beaconPrekey.bind (fun key => consume (prekeyView key))
      | .BeaconOneTime => beaconOneTime.bind (fun key => consume (oneTimeView key))) := by
  cases role <;> exact option_view_bind _ _ consume

def optionalView (view : A → m B) : Option A → m (Option B)
  | none => pure none
  | some key => some <$> view key

def optionalConsume (consume : B → m (Option R)) : Option B → m (Option R)
  | none => pure none
  | some value => consume value

theorem option_view_bindM (input : Option A) (view : A → m B)
    (consume : B → m (Option R)) :
    (optionalView view input >>= optionalConsume consume) =
      (match input with
       | none => pure none
       | some key => view key >>= consume) := by
  cases input with
  | none => simp only [optionalView, pure_bind, optionalConsume]
  | some key => simp only [optionalView, bind_map_left, optionalConsume]

theorem dh_selectionM
    (role : beaconcrypt_core.agreement.DhSecretRole)
    {L E P O : Type}
    (localIdentity : Option L) (serverEphemeral : Option E)
    (beaconPrekey : Option P) (beaconOneTime : Option O)
    (localView : L → m B) (serverView : E → m B)
    (prekeyView : P → m B) (oneTimeView : O → m B)
    (consume : B → m (Option R)) :
    ((match role with
      | .LocalIdentity => optionalView localView localIdentity
      | .ServerEphemeral => optionalView serverView serverEphemeral
      | .BeaconPrekey => optionalView prekeyView beaconPrekey
      | .BeaconOneTime => optionalView oneTimeView beaconOneTime) >>= optionalConsume consume) =
    (match role with
      | .LocalIdentity => match localIdentity with
          | none => pure none
          | some key => localView key >>= consume
      | .ServerEphemeral => match serverEphemeral with
          | none => pure none
          | some key => serverView key >>= consume
      | .BeaconPrekey => match beaconPrekey with
          | none => pure none
          | some key => prekeyView key >>= consume
      | .BeaconOneTime => match beaconOneTime with
          | none => pure none
          | some key => oneTimeView key >>= consume) := by
  cases role <;> exact option_view_bindM _ _ consume

end BeaconcryptCore.Refinement.AdapterPublicControlNormalization

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicControlNormalization.option_view_bindM' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicControlNormalization.option_view_bindM
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicControlNormalization.dh_selectionM' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicControlNormalization.dh_selectionM

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicControlNormalization.branch_tail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicControlNormalization.branch_tail

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicControlNormalization.terminal_tail' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicControlNormalization.terminal_tail

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicControlNormalization.loop_congr' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicControlNormalization.loop_congr

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicControlNormalization.init_loop_factor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicControlNormalization.init_loop_factor

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicControlNormalization.option_view_bind' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicControlNormalization.option_view_bind

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicControlNormalization.dh_selection' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicControlNormalization.dh_selection
