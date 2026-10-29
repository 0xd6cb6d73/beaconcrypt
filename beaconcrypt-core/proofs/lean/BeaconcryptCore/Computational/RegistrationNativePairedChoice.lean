-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRelatedRoot
import BeaconcryptCore.Computational.RegistrationNativePairedDemand

/-! Root preparation and material demand occur at their actual distinct phases. The private preparation map retains the optional root reply of RootSpec.derive, while the public prepared reference contains only the executable related-root message. At material demand, only the actual protected full inputs use a hidden slot. Other inputs consume the exact earlier root reply through the real source key schedule. Public fixed HMAC evaluation remains outside this private service. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePairedChoice
open PqxdhJointIdentity (Primitives IdentitySeed)
open PqxdhJointGapDh (DhInterface ScalarBytes)
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativeRelatedRoot (RootSpec)
open PqxdhSecretInputKdf (RootOutput)
open PqxdhRecordLiftInterface (Slot)
variable {n : Nat}

/-- Root bytes and family instrumentation are held only by the private interpreter. -/
structure Prepared (n : Nat) where
  roots : Pqxdh.Bytes → Option RootOutput
  family : RegistrationNativeRelatedFamily.State
  table : RegistrationNativePairedServices.State n

def initial (world : PqxdhRecordLiftWorld.State n) : Prepared n :=
  ⟨fun _ => none, RegistrationNativeRelatedFamily.empty, RegistrationNativePairedServices.initial world⟩

noncomputable def prepareWith (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (family : QueryImpl RootSpec (StateT RegistrationNativeRelatedFamily.State ProbComp))
    (message : Message) : StateT (Prepared n) ProbComp (Option Message) := fun before => do
  let actual ← (family (.inr (.derive message))).run before.family
  let roots := match RegistrationNativeRelatedFamily.input joint dh seed scalar message, actual.1 with
    | some bytes, some root => Function.update before.roots bytes (some root)
    | _, _ => before.roots
  pure (actual.1.map (fun _ => message), ⟨roots, actual.2, before.table⟩)

/-- A root callback may update its private family/root history, but cannot allocate or evaluate108 material. -/
theorem prepare_no_material (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (family : QueryImpl RootSpec (StateT RegistrationNativeRelatedFamily.State ProbComp))
    (message : Message) (before : Prepared n) (result : Option Message × Prepared n)
    (supported : result ∈ support ((prepareWith joint dh seed scalar family message).run before)) :
    result.2.table = before.table := by
  simp only [prepareWith, StateT.run, bind_pure_comp, support_map] at supported
  obtain ⟨actual, _reached, rfl⟩ := supported
  rfl

/-- The source specialization makes its actual root call now, retains that precise private root, and returns only the message reference. -/
theorem prepare_source (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (hmac : PqxdhSecretInputKdf.HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (message : Message) (before : Prepared n) :
    (prepareWith joint dh seed scalar
      (RegistrationNativeRelatedRoot.sourceImpl source hmac joint dh seed scalar) message).run before =
      match RegistrationNativeRelatedFamily.input joint dh seed scalar message with
      | none => pure (none, { before with family :=
          { before.family with history := before.family.history ++ [.derive message none] } })
      | some bytes => pure (some message,
          ⟨Function.update before.roots bytes (some (RegistrationNativeRelatedRoot.nativeRoot source bytes)),
            RegistrationNativeRelatedRoot.rootState hmac message bytes before.family, before.table⟩) := by
  cases realized : RegistrationNativeRelatedFamily.input joint dh seed scalar message <;>
    simp only [prepareWith, RegistrationNativeRelatedRoot.sourceImpl, RegistrationNativeRelatedRoot.sourceRoot,
      StateT.run, realized, pure_bind, Option.map_none, Option.map_some]

inductive PrivateChoice (n : Nat) where
  | known : PqxdhServerAuthKeySchedule.Output → PrivateChoice n
  | hidden : Slot n → PqxdhServerAuthKeySchedule.Output → PrivateChoice n

inductive Choice (n : Nat) where
  | known : PqxdhServerAuthKeySchedule.Output → Choice n
  | hidden : RegistrationNativePairedDemand.Reference n → Choice n

def publicChoice : PrivateChoice n → Choice n
  | .known output => .known output
  | .hidden slot output => .hidden ⟨slot, (PqxdhDeploymentHiddenLayout.splitOutput output).1⟩

/-- The protected mask is the existing predicate on actual full input bytes. Known inputs never consult the uniform material/seed tables. Unprepared and exhausted requests return explicitly absent. -/
noncomputable def choosePrivate (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (message : Message) : StateT (Prepared n) ProbComp (Option (PrivateChoice n)) := fun before =>
  let refused := pure (none, { before with table := { before.table with demands := before.table.demands + 1 } })
  match RegistrationNativeRelatedFamily.input joint dh seed scalar message with
  | none => refused
  | some bytes => match before.roots bytes with
    | none => refused
    | some root =>
      if RegistrationNativeRelatedFamily.Protected (joint.staticDh seed (dh.publicKey scalar)) bytes then
        (fun result => (result.1.map (fun value => PrivateChoice.hidden value.1 value.2),
          { before with table := result.2 })) <$>
            (RegistrationNativePairedDemand.privateDemand bytes).run before.table
      else pure (some (.known (PqxdhServerAuthKeySchedule.fromRoot source root)),
        { before with table := { before.table with demands := before.table.demands + 1 } })

noncomputable def choose (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (message : Message) : StateT (Prepared n) ProbComp (Option (Choice n)) :=
  Option.map publicChoice <$> choosePrivate source joint dh seed scalar message

/-- Side inputs keep the real full key schedule of the actual earlier root reply; they neither draw108 uniform bytes nor allocate a hidden reference. -/
theorem choose_known (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (message : Message) (bytes : Pqxdh.Bytes) (root : RootOutput) (before : Prepared n)
    (realized : RegistrationNativeRelatedFamily.input joint dh seed scalar message = some bytes)
    (prepared : before.roots bytes = some root)
    (side : ¬ RegistrationNativeRelatedFamily.Protected (joint.staticDh seed (dh.publicKey scalar)) bytes) :
    (choose source joint dh seed scalar message).run before =
      pure (some (.known (PqxdhServerAuthKeySchedule.fromRoot source root)),
        { before with table := { before.table with demands := before.table.demands + 1 } }) := by
  unfold choose
  rw [StateT.run_map]
  simp only [choosePrivate, StateT.run, realized, prepared, ite_eq_right side, map_pure]
  rfl

/-- Every actual DH/input alias chooses the same known-or-hidden service, rather than relying on public descriptor equality. -/
theorem choose_alias (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (left right : Message) (same : RegistrationNativeRelatedFamily.input joint dh seed scalar left =
      RegistrationNativeRelatedFamily.input joint dh seed scalar right) :
    choose (n := n) source joint dh seed scalar left = choose source joint dh seed scalar right := by
  unfold choose
  apply congrArg (fun work => Option.map publicChoice <$> work)
  funext before
  simp only [choosePrivate, same]

/-- Protected requests use only presence of the earlier root receipt, followed by the canonical paired material demand. -/
theorem choose_hidden (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (message : Message) (bytes : Pqxdh.Bytes) (root : RootOutput) (before : Prepared n)
    (realized : RegistrationNativeRelatedFamily.input joint dh seed scalar message = some bytes)
    (prepared : before.roots bytes = some root)
    (inside : RegistrationNativeRelatedFamily.Protected (joint.staticDh seed (dh.publicKey scalar)) bytes) :
    (choose source joint dh seed scalar message).run before =
      (fun result => (result.1.map Choice.hidden, { before with table := result.2 })) <$>
        (RegistrationNativePairedDemand.demand bytes).run before.table := by
  unfold choose
  rw [StateT.run_map]
  simp only [choosePrivate, StateT.run, realized, prepared, ite_eq_left inside, Functor.map_map]
  change _ = (fun result => (result.1.map Choice.hidden, { before with table := result.2 })) <$>
    (RegistrationNativePairedDemand.publicReply <$> RegistrationNativePairedDemand.privateDemand bytes).run before.table
  rw [StateT.run_map]
  simp only [Functor.map_map, RegistrationNativePairedDemand.publicReply,
    Option.map_map, publicChoice, Function.comp_def]
  rfl

def eraseRoots (target : Option PqxdhJointIdentity.DhOutput) (roots : Pqxdh.Bytes → Option RootOutput) :
    Pqxdh.Bytes → Option RootOutput := fun bytes =>
  if RegistrationNativeRelatedFamily.Protected target bytes then roots bytes |>.map (fun _ => RegistrationBoundKeySchedule.zero)
  else roots bytes

def erasePrepared (target : Option PqxdhJointIdentity.DhOutput) (before : Prepared n) : Prepared n :=
  { before with roots := eraseRoots target before.roots }

/-- In the split service, protected root contents are dead private data. Erasing them preserves every native decision, material/seed draw and full World/family state. This is an erasure inside the split game, not an independence premise for the earlier PRK hop. -/
theorem choose_root_erasure (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (message : Message) (before : Prepared n) :
    Prod.map id (erasePrepared (joint.staticDh seed (dh.publicKey scalar))) <$>
      (choosePrivate source joint dh seed scalar message).run before =
      (choosePrivate source joint dh seed scalar message).run
        (erasePrepared (joint.staticDh seed (dh.publicKey scalar)) before) := by
  cases realized : RegistrationNativeRelatedFamily.input joint dh seed scalar message with
  | none => simp [choosePrivate, StateT.run, realized, erasePrepared]
  | some bytes =>
    by_cases inside : RegistrationNativeRelatedFamily.Protected (joint.staticDh seed (dh.publicKey scalar)) bytes
    all_goals cases cached : before.roots bytes
    all_goals simp [choosePrivate, StateT.run, realized, erasePrepared, eraseRoots,
      inside, cached, Functor.map_map, Prod.map]

end BeaconcryptCore.Computational.RegistrationNativePairedChoice

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedChoice.prepare_no_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedChoice.prepare_no_material
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedChoice.prepare_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedChoice.prepare_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedChoice.choose_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedChoice.choose_known
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedChoice.choose_alias' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedChoice.choose_alias
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedChoice.choose_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedChoice.choose_hidden
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedChoice.choose_root_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedChoice.choose_root_erasure
