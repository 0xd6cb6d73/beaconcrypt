-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordRecoveryCompiler

/-! Each actual symbolic material demand makes at most one protected key-table request and at most one additional suffix-key request. Preparation makes neither. These structural bills allow the whole frontend's original build-plus-finish demand allowance to supply the concrete recovery adversary's two caps. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordServiceCaps
open RegistrationNativeSecretWordService (Spec Combined Flags handler material)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
variable {n : Nat} {Value : Type}
attribute [local irreducible] RegistrationNativeSuffixKeyPrf.value

inductive Kind where
  | key
  | suffix

def Counted : Kind → Combined.Domain → Prop
  | .key => RegistrationNativeSecretWordRecoveryCompiler.IsKey
  | .suffix => RegistrationNativeSecretWordRecoveryCompiler.IsSuffix

instance (kind : Kind) : DecidablePred (Counted kind) := by
  cases kind <;> dsimp only [Counted] <;> infer_instance

def IsDemand : (Spec n).Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance : DecidablePred (IsDemand (n := n))
  | .inl _ => inferInstanceAs (Decidable False)
  | .inr _ => inferInstanceAs (Decidable True)

/-- The complete real branch computation makes no more than one request of either billed oracle class. -/
theorem material_bound (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (key : Key) (kind : Kind) :
    (material source inside key).IsQueryBoundP (Counted kind) 1 := by
  cases protectedInput : inside key.head with
  | true =>
      cases kind <;> simp [material, protectedInput, Counted,
        RegistrationNativeSecretWordRecoveryCompiler.IsKey, RegistrationNativeSecretWordRecoveryCompiler.IsSuffix,
        RegistrationNativeSecretWord.IsKey, isQueryBoundP_query_iff]
  | false =>
      cases word : key.word <;> cases kind <;>
        simp [material, protectedInput, word, Counted,
          RegistrationNativeSecretWordRecoveryCompiler.IsKey, RegistrationNativeSecretWordRecoveryCompiler.IsSuffix,
          isQueryBoundP_query_iff]

/-- The actual prepare/demand service charges only material demands, including failed and already-refused branches. -/
theorem handler_bound (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Key)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (query : (Spec n).Domain)
    (before : Flags) (kind : Kind) :
    ((handler source input inside query).run before).IsQueryBoundP (Counted kind)
      (if IsDemand (n := n) query then 1 else 0) := by
  cases query with
  | inl message => simp only [handler, StateT.run, IsDemand, ite_false, isQueryBoundP_pure]
  | inr message =>
      simp only [handler, StateT.run, IsDemand, ite_true]
      split
      · cases realized : input message with
        | none => simp only [isQueryBoundP_pure]
        | some key => simpa only [isQueryBoundP_map_iff] using material_bound source inside key kind
      · simp only [isQueryBoundP_pure]

/-- The full actual service compiler derives both ordinary recovery bills from its original syntactic demand cap. -/
theorem program_bound (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Key)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (work : OracleComp (Spec n) Value)
    (cap : Nat) (bounded : work.IsQueryBoundP (IsDemand (n := n)) cap) (before : Flags) (kind : Kind) :
    ((simulateQ (handler source input inside) work).run before).IsQueryBoundP (Counted kind) cap :=
  bounded.simulateQ_run_of_step
    (fun query selected state => by simpa only [ite_eq_left selected] using handler_bound (n := n) source input inside query state kind)
    (fun query unselected state => by simpa only [ite_eq_right unselected] using handler_bound (n := n) source input inside query state kind)
    before

end BeaconcryptCore.Computational.RegistrationNativeSecretWordServiceCaps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordServiceCaps.material_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordServiceCaps.material_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordServiceCaps.handler_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordServiceCaps.handler_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordServiceCaps.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordServiceCaps.program_bound
