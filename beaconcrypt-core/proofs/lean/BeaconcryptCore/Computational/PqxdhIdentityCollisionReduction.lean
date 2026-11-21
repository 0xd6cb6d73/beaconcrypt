-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl
import BeaconcryptCore.Computational.PqxdhDynamicIdentityPool

/-! The original pure zero-query joint-Ed collision reduction and its exact bills, separated from classical owner scheduling. All qualified names, declaration terms and hypotheses are retained. Actual current source uses this bound only after its own generated-owner creation-index transport; equality of public keys is not assumed to identify an owner. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective
open PqxdhServerAuthExperiment PqxdhJointIdentity
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

/-- Two distinct positions of a list of identity seeds carry equal Ed25519 identity keys. -/
def Collision (joint : Primitives) (seeds : List IdentitySeed) : Prop :=
  ∃ first second : Nat, first ≠ second ∧ ∃ left right, seeds[first]? = some left ∧ seeds[second]? = some right ∧
    (joint.publicKeys left).ed25519 = (joint.publicKeys right).ed25519

/-- A collision of a prefix is a collision of the list. -/
theorem collision_take (joint : Primitives) (seeds : List IdentitySeed) (taken : Nat)
    (collision : Collision joint (seeds.take taken)) : Collision joint seeds := by
  obtain ⟨first, second, different, left, right, leftFound, rightFound, same⟩ := collision
  have lift : ∀ (index : Nat) (value : IdentitySeed), (seeds.take taken)[index]? = some value → seeds[index]? = some value := by
    intro index value found
    rw [List.getElem?_take] at found
    split_ifs at found
    exact found
  exact ⟨first, second, different, left, right, lift _ _ leftFound, lift _ _ rightFound, same⟩

/-- Signing correctness of the joint identity primitives, from the source wiring and the attached-signature correctness of the source primitives. -/
theorem joint_correct (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (message : Pqxdh.Bytes) :
    setup.joint.verify (setup.joint.publicKeys seed).ed25519 message (setup.joint.sign seed message) = true := by
  have verified := PqxdhServerAuthNegativeControl.server_verify setup seed message
  rw [setup.wiring.verifyAttached] at verified
  split_ifs at verified with valid
  · exact valid

/-- The identity at index `target` of a family of identity seeds has the Ed25519 key of an identity at a lower index. -/
def LowerCollision (joint : Primitives) {count : Nat} (target : Fin count) (seeds : Fin count → IdentitySeed) : Prop :=
  ∃ lower : Fin count, lower < target ∧
    (joint.publicKeys (seeds lower)).ed25519 = (joint.publicKeys (seeds target)).ed25519

/-- The forgery of `B^coll_t` (`collider`) from the challenge identity and the seeds it drew for the other `count` indices of the family, with the challenge at index `target`: if the challenge's Ed25519 key equals the key of a drawn seed whose family index is below `target`, the signature of the empty message under that seed, computed by the reduction itself; otherwise the all-zero signature of the empty message. -/
noncomputable def colliderForgery (joint : Primitives) {count : Nat} (target : Fin (count + 1))
    (jointPublic : PublicIdentity) (others : Fin count → IdentitySeed) : Forgery := by
  classical
  exact if found : ∃ other : Fin count, other.val < target.val ∧
      (joint.publicKeys (others other)).ed25519 = jointPublic.ed25519 then
    ⟨[], joint.sign (others (Classical.choose found)) []⟩
  else ⟨[], List.Vector.replicate 64 0⟩

/-- `B^coll_t`, the zero-query collision reduction of `ε_inj` at identity index `t = target` (plan section 10, owner input 17): a joint-use weak-EUF adversary that receives the challenge identity, draws the seeds of the other `count` identities of the family itself (the challenge at index `target`, the drawn seeds at the other indices in order) and, if the challenge's Ed25519 key equals the key of a drawn seed at a lower index, signs the empty message with that colliding seed itself and returns the signature as its forgery (`colliderForgery`). It makes no signing and no static-DH query; its only oracle queries are the `32·count` uniform bytes of the seeds it draws (`collider_queries`). -/
noncomputable def collider (joint : Primitives) (count : Nat) (target : Fin (count + 1))
    (jointPublic : PublicIdentity) : OracleComp AdversarySpec Forgery := do
  let others ← OracleComp.liftComp (PqxdhJointIdentityFamily.sampleFamily count) AdversarySpec
  pure (colliderForgery joint target jointPublic others)

/-- The joint-use weak-EUF game of `B^coll_t` draws the challenge seed, then the reduction's own seeds, and tests the forgery against the empty signing history. -/
theorem collider_game (joint : Primitives) (count : Nat) (target : Fin (count + 1)) :
    game joint (collider joint count target) = (do
      let seed ← sampleSeed
      let others ← PqxdhJointIdentityFamily.sampleFamily count
      pure (wins joint (joint.publicKeys seed) (colliderForgery joint target (joint.publicKeys seed) others) [])) := by
  simp only [game, run, collider, simulateQ_bind, StateT.run_bind, PqxdhJointIdentityFamily.simulate_joint_uniform,
    simulateQ_pure, StateT.run_pure, bind_map_left, bind_assoc, pure_bind]

/-- If, in the family with the challenge seed at index `target` and the reduction's seeds at the other indices, the identity at `target` collides with a lower index, then `B^coll_t` wins: its forgery is a valid signature under the challenge key (signing correctness, `joint_correct`) on a message the challenger never signed. -/
theorem lower_wins (setup : Setup baseSpec KemSK) (count : Nat) (target : Fin (count + 1)) (seed : IdentitySeed)
    (others : Fin count → IdentitySeed) (lower : LowerCollision setup.joint target (target.insertNth seed others)) :
    wins setup.joint (setup.joint.publicKeys seed)
      (colliderForgery setup.joint target (setup.joint.publicKeys seed) others) [] = true := by
  classical
  obtain ⟨index, below, same⟩ := lower
  have bound : index.val < count := lt_of_lt_of_le below (Nat.lt_succ_iff.mp target.isLt)
  have position : target.succAbove ⟨index.val, bound⟩ = index := by
    rw [Fin.succAbove_of_castSucc_lt _ _ (Fin.lt_def.mpr (Fin.lt_def.mp below))]
    rfl
  have found : ∃ other : Fin count, other.val < target.val ∧
      (setup.joint.publicKeys (others other)).ed25519 = (setup.joint.publicKeys seed).ed25519 := by
    refine ⟨⟨index.val, bound⟩, below, ?_⟩
    rw [← position, Fin.insertNth_apply_succAbove, Fin.insertNth_apply_same] at same
    exact same
  have chosen := (Classical.choose_spec found).2
  simp only [colliderForgery, dite_eq_left found, wins, signedMessages, List.filterMap_nil,
    List.not_mem_nil, decide_false, Bool.not_false, Bool.and_true]
  have valid := joint_correct setup (others (Classical.choose found)) []
  rwa [chosen] at valid

/-- For every identity index `target`, the probability that, among `count + 1` independently drawn identity seeds, the identity at `target` collides with a lower index is at most the joint-use weak-EUF advantage of `B^coll_t`: drawing the seed at `target` first is a distribution equality (`PqxdhJointIdentityFamily.sampleFamily_target_first`), and then `lower_wins` applies on every draw. -/
theorem lower_le_advantage (setup : Setup baseSpec KemSK) (count : Nat) (target : Fin (count + 1)) :
    Pr{let x ← PqxdhJointIdentityFamily.sampleFamily (count + 1)}[(LowerCollision setup.joint target) x] ≤
      advantage setup.joint (collider setup.joint count target) := by
  classical
  have decided : Pr{let x ← PqxdhJointIdentityFamily.sampleFamily (count + 1)}[(LowerCollision setup.joint target) x] =
      Pr{let x ← (PqxdhJointIdentityFamily.sampleFamily (count + 1) >>= fun seeds =>
        pure (decide (LowerCollision setup.joint target seeds)))}[x = true] := by
    -- Turn the final decision into a map of the computation, so that `prEvent_map` applies whatever term `Pr{…}` elaborates to.
    have computation : (PqxdhJointIdentityFamily.sampleFamily (count + 1) >>= fun seeds =>
        pure (decide (LowerCollision setup.joint target seeds))) =
        (fun seeds => decide (LowerCollision setup.joint target seeds)) <$>
          PqxdhJointIdentityFamily.sampleFamily (count + 1) :=
      bind_pure_comp _ _
    rw [computation, prEvent_map]
    exact prEvent_congr _ _ _ fun _ => decide_eq_true_iff.symm
  have moved := (PqxdhJointIdentityFamily.sampleFamily_target_first count target
    (fun seeds => pure (decide (LowerCollision setup.joint target seeds)))).prEvent_eq (fun value => value = true)
  rw [decided, moved, advantage, collider_game]
  refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun seed _ =>
    prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun others _ => ?_
  by_cases lower : LowerCollision setup.joint target (target.insertNth seed others)
  · rw [lower_wins setup count target seed others lower, prEvent_pure, prEvent_pure]
    simp [lower]
  · rw [prEvent_pure, prEvent_pure]
    simp [lower]

/-- A collision of the list of a family of identity seeds is a collision of some index with a lower index. -/
theorem collision_lower (joint : Primitives) (count : Nat) (seeds : Fin count → IdentitySeed)
    (collision : Collision joint (List.ofFn seeds)) :
    ∃ target ∈ (Finset.univ : Finset (Fin count)), LowerCollision joint target seeds := by
  obtain ⟨first, second, different, left, right, leftFound, rightFound, same⟩ := collision
  simp only [List.getElem?_ofFn] at leftFound rightFound
  obtain ⟨firstBound, leftEq⟩ := Option.dite_none_right_eq_some.mp leftFound
  obtain ⟨secondBound, rightEq⟩ := Option.dite_none_right_eq_some.mp rightFound
  rcases Nat.lt_or_gt_of_ne different with less | greater
  · exact ⟨⟨second, secondBound⟩, Finset.mem_univ _, ⟨first, firstBound⟩, less, by
      rw [Option.some.inj leftEq, Option.some.inj rightEq]; exact same⟩
  · exact ⟨⟨first, firstBound⟩, Finset.mem_univ _, ⟨second, secondBound⟩, greater, by
      rw [Option.some.inj leftEq, Option.some.inj rightEq]; exact same.symm⟩

/-- A collision among `count + 1` independently drawn identity seeds is at most the sum, over the `count + 1` identity indices `t`, of the joint-use weak-EUF advantage of the zero-query reduction `B^coll_t` (`collider`): a collision is a collision of its higher index with a lower one (`collision_lower`), the union bound sums over the higher index, and `lower_le_advantage` bounds each term. No assumption beyond joint-use weak-EUF is used: a collision gives a valid forgery by signing correctness. -/
theorem collision_bound (setup : Setup baseSpec KemSK) (count : Nat) :
    Pr{let pool ← PqxdhDynamicIdentityPool.sampleSeeds (count + 1)}[Collision setup.joint pool] ≤
      ∑ target : Fin (count + 1), advantage setup.joint (collider setup.joint count target) := by
  rw [PqxdhDynamicIdentityPool.sampleSeeds, prEvent_map]
  refine (prEvent_mono_of_support _ _ _ fun seeds _ collision => collision_lower setup.joint (count + 1) seeds collision).trans ?_
  exact (prEvent_exists_finset_le _ _ _).trans
    (Finset.sum_le_sum fun target _ => lower_le_advantage setup count target)

/-- `B^coll_t` makes, on every challenge identity, at most `32·count` uniform queries (the bytes of the seeds it draws) and no signing and no static-DH query. -/
theorem collider_queries (joint : Primitives) (count : Nat) (target : Fin (count + 1))
    (kind : PqxdhJointIdentityFamily.Kind) (jointPublic : PublicIdentity) :
    (collider joint count target jointPublic).IsQueryBoundP (PqxdhJointIdentityFamily.IsClass kind)
      (if kind = .uniform then 32 * count else 0) := by
  unfold collider
  have bound := OracleComp.isQueryBoundP_bind (PqxdhJointIdentityFamily.sampleFamily_lift_bound count kind)
    (fun others _ => isQueryBoundP_pure _ (colliderForgery joint target jointPublic others) 0)
  rwa [Nat.add_zero] at bound

/-- The bills of `B^coll_t`: on every challenge identity at most `32·count` uniform queries, no signing query and no static-DH query; its whole joint-use weak-EUF game, with the challenger's own seed draw, makes at most `32·(count + 1)` uniform queries. -/
theorem collider_bills (joint : Primitives) (count : Nat) (target : Fin (count + 1)) :
    (∀ jointPublic, (collider joint count target jointPublic).IsQueryBoundP
      (PqxdhJointIdentityFamily.IsClass .uniform) (32 * count)) ∧
    (∀ jointPublic, (collider joint count target jointPublic).IsQueryBoundP
      (PqxdhJointIdentityFamily.IsClass .sign) 0) ∧
    (∀ jointPublic, (collider joint count target jointPublic).IsQueryBoundP
      (PqxdhJointIdentityFamily.IsClass .staticDh) 0) ∧
    (game joint (collider joint count target)).IsTotalQueryBound (32 * (count + 1)) := by
  refine ⟨fun jointPublic => by simpa using collider_queries joint count target .uniform jointPublic,
    fun jointPublic => by simpa using collider_queries joint count target .sign jointPublic,
    fun jointPublic => by simpa using collider_queries joint count target .staticDh jointPublic, ?_⟩
  have counted := PqxdhJointIdentityFamily.jointGame_uniform_bound joint (collider joint count target) (32 * count)
    fun jointPublic => by simpa using collider_queries joint count target .uniform jointPublic
  convert counted using 1
  omega

end BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.collision_take' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.collision_take

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.joint_correct' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.joint_correct

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.collider_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.collider_game

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.lower_wins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.lower_wins

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.lower_le_advantage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.lower_le_advantage

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.collision_lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.collision_lower

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.collision_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.collision_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.collider_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.collider_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.collider_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.collider_bills
