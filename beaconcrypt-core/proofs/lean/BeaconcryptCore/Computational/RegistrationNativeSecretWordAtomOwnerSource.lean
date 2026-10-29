-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTracedSource
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerIncoming

/-! Incoming owner callbacks retain their exact current environment, chronological trace and private source state. Erasing only that pure trace gives the same actual selected/ordinary local source used by the atom provenance receipts. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerSource
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationServerReferenceCompiler (Environment)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

abbrev State (n : Nat) (KemSK : Type) := Environment ×
  (RegistrationNativeSecretWordFrontendTrace.State × RegistrationNativeSecretWordInterpreter.State n KemSK)

def drop (before : State n KemSK) : RegistrationNativeSecretWordTargetServerExecution.Auxiliary n KemSK :=
  (before.1, before.2.2)

def routing (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes) :
    QueryImpl (RegistrationNativeSecretWordInterface.LocalSpec n KemSK)
      (OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK)) :=
  match scalar with
  | none => RegistrationNativeSecretWordInterface.liftLocal false
  | some scalar => RegistrationNativeSecretWordInterface.liftLocal false ∘ₛ RegistrationNativeSecretWordOwners.ordinary setup scalar

variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
local notation "wordSource" => RegistrationNativeSecretWordAtomTracedSource.word (n := n) setup wire route sign input inside provider outer
local notation "plainSource" => RegistrationNativeSecretWordTargetSource.implementation (n := n) setup wire route sign input inside provider outer
local notation "plainLocal" => RegistrationNativeSecretWordTargetServerExecution.localImpl (n := n) setup wire route sign input inside provider outer false

noncomputable def lower (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (work : StateT Environment (OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK)) Value) :
    StateT (State n KemSK) ProbComp Value := fun before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ wordSource (simulateQ (routing setup scalar) (work.run before.1))).run before.2

private theorem local_source (scalar : Option PqxdhJointGapDh.ScalarBytes) :
    plainSource ∘ₛ routing setup scalar = RegistrationNativeSecretWordAtomOwnerGetter.withScalar setup plainLocal scalar := by
  cases scalar with
  | none => rfl
  | some scalar =>
      funext query
      simp only [routing, RegistrationNativeSecretWordAtomOwnerGetter.withScalar,
        RegistrationNativeSecretWordTargetServerExecution.localImpl, QueryImpl.compose, QueryImpl.simulateQ_compose]

/-- Only the chronological observer is forgotten; every current environment and private source field stays literal. -/
theorem source (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (work : StateT Environment (OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK)) Value)
    (before : State n KemSK) :
    Prod.map id drop <$> (lower setup wire route sign input inside provider outer scalar work).run before =
      (RegistrationNativeSecretWordTargetServerExecution.lower
        (RegistrationNativeSecretWordAtomOwnerGetter.withScalar setup plainLocal scalar) work).run (drop before) := by
  have actual := RegistrationNativeSecretWordAtomTracedSource.word_source setup wire route sign input inside provider outer
    (simulateQ (routing setup scalar) (work.run before.1)) before.2.1 before.2.2
  have plain : simulateQ plainSource (simulateQ (routing setup scalar) (work.run before.1)) =
      simulateQ (RegistrationNativeSecretWordAtomOwnerGetter.withScalar setup plainLocal scalar) (work.run before.1) := by
    rw [← QueryImpl.simulateQ_compose, local_source setup wire route sign input inside provider outer scalar]
  rw [plain] at actual
  have moved := congrArg (fun program => (fun result => (result.1.1, (result.1.2, result.2))) <$> program) actual
  simpa only [StateT.run, lower, drop, RegistrationNativeSecretWordTargetServerExecution.lower,
    Prod.map_def, id_eq, Functor.map_map] using moved

/-- The same actual supported owner call has its same complete pure chronological trace before private source interpretation. -/
theorem trace_support (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (work : StateT Environment (OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK)) Value)
    (before : State n KemSK) (result : Value × State n KemSK)
    (supported : result ∈ support ((lower setup wire route sign input inside provider outer scalar work).run before)) :
    ((result.1, result.2.1), result.2.2.1) ∈ support
      ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler
        (simulateQ (routing setup scalar) (work.run before.1))).run before.2.1) := by
  simp only [lower, StateT.run, support_map] at supported
  obtain ⟨inner, actual, equal⟩ := supported
  cases equal
  exact RegistrationNativeSecretWordAtomTracedSource.word_support setup wire route sign input inside provider outer _ before.2 inner actual

private theorem state_bind_apply {Private Value Result : Type} {m : Type → Type} [Monad m]
    (work : StateT Private m Value) (next : Value → StateT Private m Result) (before : Private) :
    (work >>= next) before = (do let reached ← work before; next reached.1 reached.2) := rfl

private theorem state_pure_apply {Private Value : Type} {m : Type → Type} [Monad m]
    (value : Value) (before : Private) : (pure value : StateT Private m Value) before = pure (value, before) := rfl

/-- The current environment and complete trace/private state are threaded through each actual owner continuation. -/
theorem lower_bind {Result : Type} (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (work : StateT Environment (OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK)) Value)
    (next : Value → StateT Environment (OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK)) Result) :
    lower setup wire route sign input inside provider outer scalar (work >>= next) =
      (lower setup wire route sign input inside provider outer scalar work >>= fun value =>
        lower setup wire route sign input inside provider outer scalar (next value)) := by
  apply StateT.ext
  intro before
  simp only [StateT.run, lower, state_bind_apply, simulateQ_bind, map_bind, bind_map_left]

/-- Pure owner-local results keep their complete environment, chronological trace and private source state. -/
theorem lower_pure (scalar : Option PqxdhJointGapDh.ScalarBytes) (value : Value) :
    lower (n := n) setup wire route sign input inside provider outer scalar (pure value) = pure value := by
  apply StateT.ext
  intro before
  simp only [StateT.run, lower, state_pure_apply, simulateQ_pure, map_pure]

/-- The ordinary-owner translator changes only optional root descriptors and preserves both actual installation bills. -/
theorem routing_bound (role : PqxdhRecordLiftInterface.Role) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) Value) (cap : Nat)
    (bounded : work.IsQueryBoundP (RegistrationNativeSecretWordAtomInstallPredicate.LocalInstall (KemSK := KemSK) role) cap) :
    (simulateQ (routing setup scalar) work).IsQueryBoundP
      (RegistrationNativeSecretWordAtomInstallPredicate.GlobalInstall (KemSK := KemSK) role) cap := by
  cases scalar with
  | none => exact RegistrationNativeSecretWordAtomInstallPredicate.local_bound role false work cap bounded
  | some scalar =>
      simp only [routing, QueryImpl.simulateQ_compose]
      apply RegistrationNativeSecretWordAtomInstallPredicate.local_bound role false _ cap
      apply RawCtxSourceOpen.simulate_bound _ _ _ work cap bounded
      intro query
      cases query with
      | inl message =>
          simp only [RegistrationNativeSecretWordOwners.ordinary, RegistrationNativeSecretWordAtomInstallPredicate.LocalInstall]
          split <;> simp [RegistrationNativeSecretWordAtomInstallPredicate.LocalInstall, isQueryBoundP_query_iff]
      | inr query =>
          simp only [RegistrationNativeSecretWordOwners.ordinary, isQueryBoundP_query_iff]
          intro counted
          rw [ite_eq_left counted]
          decide

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerSource.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerSource.source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerSource.trace_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerSource.trace_support

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerSource.lower_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerSource.lower_bind
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerSource.lower_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerSource.lower_pure
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerSource.routing_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomOwnerSource.routing_bound
