-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointServiceCosts
import BeaconcryptCore.Computational.PqxdhRegistrationJointAttemptReports

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppression
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhEd25519EufCma
open PqxdhBeaconPhase1Publication
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result I D K A : Type}

/-- The selected signing capability and canonical one-time public message, never its private signing seed. -/
structure Target where
  identityIndex : Nat
  oneTime : X25519PublicKey
  deriving DecidableEq

def Target.message (target : Target) : Pqxdh.Bytes := oneTimeMessage target.oneTime

/-- A public bundle-call ordinal is consumed even if no owner or prepared tuple exists there. -/
structure Selection where
  pending : Option Nat
  target : Option Target
  deriving DecidableEq

def Selection.initial (ordinal : Nat) : Selection := ⟨some ordinal, none⟩

def Selection.advance (selection : Selection) : Bool × Selection :=
  match selection.pending with
  | none => (false, selection)
  | some 0 => (true, { selection with pending := none })
  | some (remaining + 1) => (false, { selection with pending := some remaining })

/-- Selection inspects only an existing handle and the prepared one-time public key. -/
def current (projection : PqxdhLivePhase1Bundle.Public I D K)
    (owner : PqxdhBeaconPhase1Publication.State (I := I) (D := D) (K := K)) (generated : Option D) : Option Target :=
  (prepare owner generated).map fun prepared =>
    ⟨projection.index owner.beacon.identity, projection.dh prepared.oneTime⟩

def Selection.next (selection : Selection) (prepared : Option Target) : Selection :=
  let (selected, advanced) := selection.advance
  if selected then { advanced with target := prepared } else advanced

def Selection.blocks (selection : Selection) (prepared : Option Target) : Bool :=
  match prepared with
  | none => false
  | some target => selection.target == some target

/-- The whole selected signing/writer block is skipped; no signature is fabricated or privately computed. -/
def afterGenerated (projection : PqxdhLivePhase1Bundle.Public I D K) (generated : Option D)
    (owner : PqxdhBeaconPhase1Publication.State (I := I) (D := D) (K := K)) (selection : Selection) :
    OracleComp (PqxdhLivePhase1Bundle.Spec D)
      ((Option Pqxdh.Bytes × PqxdhBeaconPhase1Publication.State (I := I) (D := D) (K := K)) × Selection) :=
  let prepared := current projection owner generated
  let next := selection.next prepared
  if next.blocks prepared then pure ((none, owner), next)
  else (fun result => (result, next)) <$> PqxdhLivePhase1Bundle.afterGenerated projection generated owner

/-- Fresh generation stays in the same source position; retained coins cause no new draw. -/
def client (projection : PqxdhLivePhase1Bundle.Public I D K)
    (owner : PqxdhBeaconPhase1Publication.State (I := I) (D := D) (K := K)) (selection : Selection) :
    OracleComp (PqxdhLivePhase1Bundle.Spec D)
      ((Option Pqxdh.Bytes × PqxdhBeaconPhase1Publication.State (I := I) (D := D) (K := K)) × Selection) :=
  match owner.beacon.phase with
  | .fresh _ _ _ => do
      let generated ← (PqxdhLivePhase1Bundle.Spec D).query (.inl ())
      afterGenerated projection generated owner selection
  | .freshWithCoins _ _ _ _ => afterGenerated projection none owner selection
  | _ => pure ((none, owner), selection.next none)

/-- Every other owner representation has the same selected public tuple. -/
theorem current_map {I' K' : Type} (identityMap : I → I') (kemMap : K → K')
    (projection : PqxdhLivePhase1Bundle.Public I D K) (mapped : PqxdhLivePhase1Bundle.Public I' D K')
    (indices : ∀ owner, mapped.index (identityMap owner) = projection.index owner)
    (dh : mapped.dh = projection.dh) (generated : Option D)
    (owner : PqxdhBeaconPhase1Publication.State (I := I) (D := D) (K := K)) :
    current mapped (mapState identityMap kemMap owner) generated = current projection owner generated := by
  cases owner with
  | mk beacon attempts =>
    cases beacon with
    | mk identity kid pin phase =>
      cases phase <;> cases generated <;> simp [current, prepare, mapState, mapPhase, indices, dh]

/-- Handle erasure preserves the entire modified signing/publication client and its selection state. -/
theorem afterGenerated_map {I' K' : Type} (identityMap : I → I') (kemMap : K → K')
    (projection : PqxdhLivePhase1Bundle.Public I D K) (mapped : PqxdhLivePhase1Bundle.Public I' D K')
    (indices : ∀ owner, mapped.index (identityMap owner) = projection.index owner)
    (identities : ∀ owner, mapped.identity (identityMap owner) = projection.identity owner)
    (dh : mapped.dh = projection.dh) (keys : ∀ key, mapped.kem (kemMap key) = projection.kem key)
    (generated : Option D) (owner : PqxdhBeaconPhase1Publication.State (I := I) (D := D) (K := K))
    (selection : Selection) :
    (fun result => ((result.1.1, mapState identityMap kemMap result.1.2), result.2)) <$>
      afterGenerated projection generated owner selection =
      afterGenerated mapped generated (mapState identityMap kemMap owner) selection := by
  simp only [afterGenerated, current_map identityMap kemMap projection mapped indices dh]
  split
  · rfl
  · rw [Functor.map_map]
    simpa only [Functor.map_map] using congrArg
      (fun work => (fun result => (result, selection.next (current projection owner generated))) <$> work)
      (PqxdhLivePhase1Bundle.afterGenerated_map identityMap kemMap projection mapped indices identities dh keys generated owner)

/-- Full bundle suppression commutes with the private-owner-to-handle map, including its actual generation query. -/
theorem client_map {I' K' : Type} (identityMap : I → I') (kemMap : K → K')
    (projection : PqxdhLivePhase1Bundle.Public I D K) (mapped : PqxdhLivePhase1Bundle.Public I' D K')
    (indices : ∀ owner, mapped.index (identityMap owner) = projection.index owner)
    (identities : ∀ owner, mapped.identity (identityMap owner) = projection.identity owner)
    (dh : mapped.dh = projection.dh) (keys : ∀ key, mapped.kem (kemMap key) = projection.kem key)
    (owner : PqxdhBeaconPhase1Publication.State (I := I) (D := D) (K := K)) (selection : Selection) :
    (fun result => ((result.1.1, mapState identityMap kemMap result.1.2), result.2)) <$>
      client projection owner selection = client mapped (mapState identityMap kemMap owner) selection := by
  cases owner with
  | mk beacon attempts =>
    cases beacon with
    | mk identity kid pin phase =>
      cases phase <;> simp only [client, mapState, mapPhase, map_bind, map_pure]
      all_goals first
        | exact afterGenerated_map identityMap kemMap projection mapped indices identities dh keys _ _ selection
        | apply bind_congr
      all_goals intro generated
      all_goals exact afterGenerated_map identityMap kemMap projection mapped indices identities dh keys _ _ selection

abbrev NativeResult (KemSK : Type) := PqxdhRegistrationJointAttemptTrace.NativeResult KemSK

def nativeCurrent (setup : Setup baseSpec KemSK) (index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (generated : Option ScalarBytes) : Option Target :=
  current (PqxdhRegistrationSchedule.projection setup index) owner generated

/-- This mathematical source interpreter uses its original deterministic signers only on nonsuppressed blocks. -/
def after (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (generated : Option ScalarBytes)
    (pool : PqxdhDynamicIdentityPool.SourceState) (selection : Selection) : NativeResult KemSK × Selection :=
  let prepared := nativeCurrent setup index owner generated
  let next := selection.next prepared
  if next.blocks prepared then (((none, owner), pool), next)
  else (PqxdhRegistrationJointBundle.after setup codec index owner generated pool, next)

def trace (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (pool : PqxdhDynamicIdentityPool.SourceState)
    (selection : Selection) : ProbComp (NativeResult KemSK × Selection) :=
  match owner.beacon.phase with
  | .fresh _ _ _ => (fun scalar => after setup codec index owner (some scalar) pool selection) <$> sampleScalar
  | _ => pure (after setup codec index owner none pool selection)

/-- Suppressing one complete block retains the exact role state, private seeds and earlier history. -/
theorem after_blocked (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (generated : Option ScalarBytes)
    (pool : PqxdhDynamicIdentityPool.SourceState) (selection : Selection)
    (blocked : (selection.next (nativeCurrent setup index owner generated)).blocks
      (nativeCurrent setup index owner generated) = true) :
    after setup codec index owner generated pool selection =
      (((none, owner), pool), selection.next (nativeCurrent setup index owner generated)) := by
  simp only [after, blocked, ite_true]

/-- On an original failed matching attempt, suppression preserves the complete public return and native owner. -/
theorem after_public (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (generated : Option ScalarBytes)
    (pool : PqxdhDynamicIdentityPool.SourceState) (selection : Selection)
    (failure : (selection.next (nativeCurrent setup index owner generated)).blocks
      (nativeCurrent setup index owner generated) = true →
      (PqxdhRegistrationJointBundle.after setup codec index owner generated pool).1.1 = none) :
    (after setup codec index owner generated pool selection).1.1 =
      (PqxdhRegistrationJointBundle.after setup codec index owner generated pool).1 := by
  by_cases blocked : (selection.next (nativeCurrent setup index owner generated)).blocks
      (nativeCurrent setup index owner generated) = true
  · rw [after_blocked setup codec index owner generated pool selection blocked]
    have failed := failure blocked
    cases prepared : prepare owner generated with
    | none => simp [PqxdhRegistrationJointBundle.after, prepared]
    | some prepared =>
      simp only [PqxdhRegistrationJointBundle.after, prepared] at failed ⊢
      split at failed <;> simp_all
  · simp only [after, blocked, Bool.false_eq_true, ite_false]

/-- The source-level client uses exactly the original indexed signing interpreter outside suppressed blocks. -/
theorem afterGenerated_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (generated : Option ScalarBytes)
    (pool : PqxdhDynamicIdentityPool.SourceState) (auxiliary : A) (selection : Selection)
    (created : pool.seeds[index]? = some owner.beacon.identity) :
    (simulateQ (PqxdhLiveJointSigning.impl setup.joint
      (PqxdhRegistrationJointBundle.generate (A := A)) (PqxdhRegistrationJointBundle.writer codec))
      (afterGenerated (PqxdhRegistrationSchedule.projection setup index) generated owner selection)).run
        (pool, auxiliary) =
      pure (((after setup codec index owner generated pool selection).1.1,
        (after setup codec index owner generated pool selection).2),
        ((after setup codec index owner generated pool selection).1.2, auxiliary)) := by
  simp only [afterGenerated]
  by_cases blocked : (selection.next (current (PqxdhRegistrationSchedule.projection setup index) owner generated)).blocks
      (current (PqxdhRegistrationSchedule.projection setup index) owner generated) = true
  · simp only [blocked, ite_true, simulateQ_pure, StateT.run_pure, after, nativeCurrent]
  · simp only [blocked, Bool.false_eq_true, ite_false]
    rw [simulateQ_map, StateT.run_map, PqxdhLiveJointSigning.afterGenerated_source setup.joint
      (PqxdhRegistrationJointBundle.generate (A := A)) (PqxdhRegistrationJointBundle.writer codec)
      (PqxdhRegistrationSchedule.projection setup index) generated owner (pool, auxiliary)
      owner.beacon.identity created]
    unfold PqxdhLiveJointSigning.sourceAfter
    cases prepared : prepare owner generated with
    | none => simp [prepared, after, nativeCurrent, blocked, PqxdhRegistrationJointBundle.after]
    | some prepared =>
      simp only [prepared, PqxdhRegistrationSchedule.projection,
        afterSigning, simulateQ_bind, simulateQ_spec_query, PqxdhRegistrationJointBundle.writer,
        pure_bind]
      split <;> simp_all [after, nativeCurrent, PqxdhRegistrationJointBundle.after,
        simulateQ_pure, StateT.run_pure]
      all_goals rfl

/-- Source bundle execution retains the original draw and every nonsuppressed primitive reply, with the complete owner returned. -/
theorem source_client (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (pool : PqxdhDynamicIdentityPool.SourceState)
    (auxiliary : A) (selection : Selection) (created : pool.seeds[index]? = some owner.beacon.identity) :
    (simulateQ (PqxdhLiveJointSigning.impl setup.joint
      (PqxdhRegistrationJointBundle.generate (A := A)) (PqxdhRegistrationJointBundle.writer codec))
      (client (PqxdhRegistrationSchedule.projection setup index) owner selection)).run (pool, auxiliary) =
      (fun result => ((result.1.1, result.2), (result.1.2, auxiliary))) <$>
        trace setup codec index owner pool selection := by
  cases phase : owner.beacon.phase <;> simp only [client, trace, phase]
  case fresh =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, Functor.map_map]
    have generation : (PqxdhLiveJointSigning.impl setup.joint
        (PqxdhRegistrationJointBundle.generate (A := A)) (PqxdhRegistrationJointBundle.writer codec)
        (.inl ())).run (pool, auxiliary) =
        (fun scalar => (some scalar, (pool, auxiliary))) <$> sampleScalar := by
      rw [PqxdhLiveJointSigning.generation_complete]
      simp only [PqxdhRegistrationJointBundle.generate, StateT.run_lift, bind_pure_comp, Functor.map_map]
    rw [generation, bind_map_left]
    conv_rhs => rw [map_eq_bind_pure_comp]
    apply bind_congr
    intro scalar
    exact afterGenerated_source setup codec index owner (some scalar) pool auxiliary selection created
  case freshWithCoins =>
    exact afterGenerated_source setup codec index owner none pool auxiliary selection created
  all_goals simp [after, nativeCurrent, current, prepare, phase, Selection.blocks, PqxdhRegistrationJointBundle.after]

/-- The executable bundle client receives only identity/KEM handles and uses the indexed external signing service. -/
theorem client_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (index kemIndex : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (pool : PqxdhDynamicIdentityPool.SourceState) (auxiliary : A) (selection : Selection)
    (created : pool.seeds[index]? = some owner.beacon.identity) :
    (simulateQ (PqxdhLiveJointSigning.impl setup.joint
      (PqxdhRegistrationJointBundle.generate (A := A)) (PqxdhRegistrationJointBundle.writer codec))
      (client (PqxdhRegistrationJointBundle.projection setup)
        (PqxdhRegistrationJointBundle.encode setup index kemIndex owner) selection)).run (pool, auxiliary) =
      (fun result => (((result.1.1.1, PqxdhRegistrationJointBundle.encode setup index kemIndex result.1.1.2),
        result.2), (result.1.2, auxiliary))) <$> trace setup codec index owner pool selection := by
  rw [show PqxdhRegistrationJointBundle.encode setup index kemIndex owner =
      mapState (PqxdhRegistrationJointBundle.identityMap setup index)
        (PqxdhRegistrationJointBundle.keyMap kemIndex) owner from rfl,
    ← client_map (PqxdhRegistrationJointBundle.identityMap setup index)
      (PqxdhRegistrationJointBundle.keyMap kemIndex) (PqxdhRegistrationSchedule.projection setup index)
      (PqxdhRegistrationJointBundle.projection setup) (fun _ => rfl) (fun _ => rfl) rfl (fun _ => rfl)]
  rw [simulateQ_map, StateT.run_map, source_client setup codec index owner pool auxiliary selection created,
    Functor.map_map]
  rfl

/-- Compilation leaves genuine indexed identity requests open and preserves the complete KEM pool beside suppression state. -/
theorem compiled_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (index kemIndex : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (pool : PqxdhLiveKemBirth.State KemSK) (selection : Selection)
    (created : pool.1.seeds[index]? = some owner.beacon.identity) :
    (simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem)
      (simulateQ (PqxdhRegistrationJointBundleCompiler.compiler codec)
        (client (PqxdhRegistrationJointBundle.projection setup)
          (PqxdhRegistrationJointBundle.encode setup index kemIndex owner) selection))).run pool =
      (fun result => (((result.1.1.1, PqxdhRegistrationJointBundle.encode setup index kemIndex result.1.1.2),
        result.2), (result.1.2, pool.2))) <$> trace setup codec index owner pool.1 selection := by
  rw [PqxdhRegistrationJointBundleCompiler.program_interpreted,
    client_source setup codec index kemIndex owner pool.1 pool.2 selection created]

/-- Suppression emits no additional signing, KEM, DH or uniform query. -/
theorem after_queries (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (generated : Option ScalarBytes) (owner : PqxdhRegistrationJointBundle.Owner) (selection : Selection)
    (kind : PqxdhRegistrationJointServiceCosts.Kind) :
    (simulateQ (PqxdhRegistrationJointBundleCompiler.compiler (KemSK := KemSK) codec)
      (afterGenerated (PqxdhRegistrationJointBundle.projection setup) generated owner selection)).IsQueryBoundP
        (fun query => PqxdhRegistrationJointServiceCosts.poolClass (KemSK := KemSK) query = kind)
        (if kind = .signing then 3 else 0) := by
  by_cases blocked : (selection.next (current (PqxdhRegistrationJointBundle.projection setup) owner generated)).blocks
      (current (PqxdhRegistrationJointBundle.projection setup) owner generated) = true
  · simp only [afterGenerated, blocked, ite_true, simulateQ_pure, isQueryBoundP_pure]
  · simpa only [afterGenerated, blocked, Bool.false_eq_true, ite_false, simulateQ_map, isQueryBoundP_map_iff] using
      PqxdhRegistrationJointServiceCosts.after_queries setup codec generated owner kind

/-- The modified handle bundle has the unchanged original per-attempt service budget. -/
theorem client_queries (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (owner : PqxdhRegistrationJointBundle.Owner) (selection : Selection)
    (kind : PqxdhRegistrationJointServiceCosts.Kind) :
    (simulateQ (PqxdhRegistrationJointBundleCompiler.compiler (KemSK := KemSK) codec)
      (client (PqxdhRegistrationJointBundle.projection setup) owner selection)).IsQueryBoundP
        (fun query => PqxdhRegistrationJointServiceCosts.poolClass (KemSK := KemSK) query = kind)
        (PqxdhRegistrationJointServiceCosts.bundleCap kind) := by
  cases phase : owner.beacon.phase <;> simp only [client, phase,
    simulateQ_pure, isQueryBoundP_pure, simulateQ_bind, simulateQ_spec_query]
  case fresh =>
    apply isQueryBoundP_bind
    · exact PqxdhRegistrationJointServiceCosts.coins_queries (some <$> sampleScalar) 32
        (by simpa only [IsTotalQueryBound, isQueryBound_map_iff] using sampleScalar_uniform) kind
    · exact fun generated _ => after_queries setup codec generated owner selection kind
  case freshWithCoins =>
    exact (after_queries setup codec none owner selection kind).mono (Nat.le_add_left _ _)

/-- The mathematical source retains all actual generation work and adds no hidden random draw. -/
theorem trace_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (pool : PqxdhDynamicIdentityPool.SourceState)
    (selection : Selection) : (trace setup codec index owner pool selection).IsTotalQueryBound 32 := by
  cases phase : owner.beacon.phase <;> simp only [trace, phase, IsTotalQueryBound,
    isQueryBound_map_iff, isQueryBound_pure]
  exact sampleScalar_uniform

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppression

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppression.current_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppression.current_map

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppression.afterGenerated_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppression.afterGenerated_map

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppression.client_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppression.client_map

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppression.after_blocked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppression.after_blocked

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppression.after_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppression.after_public

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppression.afterGenerated_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppression.afterGenerated_source

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppression.source_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppression.source_client

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppression.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppression.client_source

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppression.compiled_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppression.compiled_source

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppression.after_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppression.after_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppression.client_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppression.client_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppression.trace_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSuppression.trace_uniform
