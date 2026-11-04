-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorOpenDictionary
import BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarly
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenInterpreter
import BeaconcryptCore.Computational.RegistrationNativeSecretWordProtection
/-! Concrete source dictionary closing for the literal selective service. The physical World remains free. The genuine early provider is evaluated query by query, preserving every original sampler and World coin callback. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxLeaves
open PqxdhServerAuthExperiment (Setup)
open PqxdhKemIndCca
open PqxdhRecordLiftInterface (WorldSpec coinLift)
variable {n : Nat} {I KemSK Value : Type} {base : OracleSpec I}
abbrev World (n : Nat) := OracleComp (WorldSpec n)
abbrev Roots (n : Nat) := RegistrationNativeSelectiveHiddenService.State n
abbrev Symbolic (n : Nat) (KemSK : Type) := RegistrationNativeSecretWordInterpreter.State n KemSK × Roots n

variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : MlKemSharedSecret)

def frame (before : Symbolic n KemSK) :
    RegistrationNativeSelectiveHiddenInterpreter.State n KemSK RegistrationNativeKemSwitchSource.Phase :=
  ((⟨before.2.1,(RegistrationNativeSecretWordKemProvider.evalState candidate before.1.kem).1,
    (RegistrationNativeSecretWordKemProvider.evalState candidate before.1.kem).2,before.1.ordinary.receipts⟩),before.2.2)

noncomputable def closing (unused : QueryImpl RegistrationNativeSecretWordService.Combined (World n)) :
    QueryImpl (RegistrationNativePlatformLorOpenDictionary.Spec n) (StateT (Roots n) (World n))
  | .inl (.inl query) => StateT.lift (unused query)
  | .inl (.inr query) => StateT.lift ((WorldSpec n).query query)
  | .inr query => RegistrationNativePlatformLorOpenDictionary.actualRoots setup seed scalar candidate query

noncomputable def lower (unused : QueryImpl RegistrationNativeSecretWordService.Combined (World n))
    (provider : RegistrationNativeSecretWordInterpreter.Provider KemSK) :
    QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT (Symbolic n KemSK) (World n)) :=
  (QueryImpl.mapStateTBase (closing setup seed scalar candidate unused)
    (RegistrationNativePlatformLorOpenDictionary.handler setup wire sign
      (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)
      (RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) provider)).flattenStateT

def nativeQuery (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain) :
    (RegistrationNativePublicFrontend.Spec n KemSK).Domain :=
  match query with
  | .inl (.inl message) => .inl (.inl (RegistrationNativeSecretWordMessage.eval candidate message))
  | .inl (.inr (.inl (.inl message))) => .inl (.inr (.inl (.inl (RegistrationNativeSecretWordMessage.eval candidate message))))
  | .inl (.inr (.inl (.inr query))) => .inl (.inr (.inl (.inr query)))
  | .inl (.inr (.inr query)) => .inl (.inr (.inr query))
  | .inr query => .inr query

def nativeReply : (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain) →
    (RegistrationNativeSecretWordInterface.Spec n KemSK).Range query →
    (RegistrationNativePublicFrontend.Spec n KemSK).Range (nativeQuery candidate query)
  | .inl (.inl _),reply => reply.map (RegistrationNativeSecretWordMessage.eval candidate)
  | .inl (.inr (.inl (.inl _))),reply => reply
  | .inl (.inr (.inl (.inr _))),reply => reply
  | .inl (.inr (.inr query)),reply => RegistrationNativeSecretWordKemProvider.evalReply candidate query reply
  | .inr _,reply => reply

variable (unused : QueryImpl RegistrationNativeSecretWordService.Combined (World n))

theorem world_source (work : World n Value) (before : Roots n) :
    (simulateQ (closing setup seed scalar candidate unused)
      (simulateQ RegistrationNativePlatformLorOpenDictionary.embed
        (simulateQ RegistrationNativePlatformLorWorldDictionary.world work))).run before =
      (fun result => (result,before)) <$> work := by
  rw [← QueryImpl.simulateQ_compose,← QueryImpl.simulateQ_compose]
  have same : (closing setup seed scalar candidate unused ∘ₛ
      RegistrationNativePlatformLorOpenDictionary.embed) ∘ₛ RegistrationNativePlatformLorWorldDictionary.world =
      (QueryImpl.ofLift (WorldSpec n) (World n)).liftTarget (StateT (Roots n) (World n)) := by
    funext query
    simp only [QueryImpl.compose,RegistrationNativePlatformLorWorldDictionary.world,
      RegistrationNativePlatformLorOpenDictionary.embed,simulateQ_spec_query,closing,QueryImpl.liftTarget_apply,QueryImpl.ofLift]
    rfl
  rw [same,simulateQ_liftTarget,simulateQ_ofLift_eq_self]
  change (work >>= fun result => pure (result,before)) = _
  exact bind_pure_comp _ _

theorem effect_source (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value) (before : Roots n) :
    (simulateQ (closing setup seed scalar candidate unused)
      (simulateQ RegistrationNativePlatformLorOpenDictionary.embed
        (simulateQ (fun query => RegistrationNativePlatformLorWorldDictionary.world (.inr (.inl query))) work))).run before =
      (fun result => (result,before)) <$> simulateQ PqxdhRecordLiftInterface.effectLift work := by
  have same : (fun query => RegistrationNativePlatformLorWorldDictionary.world (.inr (.inl query))) =
      RegistrationNativePlatformLorWorldDictionary.world ∘ₛ (PqxdhRecordLiftInterface.effectLift (n := n)) := by
    funext query
    simp only [QueryImpl.compose,PqxdhRecordLiftInterface.effectLift,simulateQ_spec_query]
  rw [same,QueryImpl.simulateQ_compose]
  exact world_source setup seed scalar candidate unused _ before

theorem provider_source (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
    (query : (RegistrationNativeSecretWordKemInterface.Routed KemSK).Domain)
    (before : RegistrationNativeSecretWordKemProvider.State KemSK) :
    simulateQ (coinLift (n := n))
      ((RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected pairs publicKey challenge candidate query).run
        (RegistrationNativeSecretWordKemProvider.evalState candidate before)) =
      (fun result => (RegistrationNativeSecretWordKemProvider.evalReply candidate query result.1,
        RegistrationNativeSecretWordKemProvider.evalState candidate result.2)) <$>
        simulateQ (coinLift (n := n))
          ((RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge query).run before) := by
  rw [←RegistrationNativeSecretWordKemEarly.query_source setup.baseImpl setup.kem selected pairs publicKey challenge candidate query before]
  rw [simulateQ_map]
private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map _ _ _

private theorem lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) :
    (StateT.lift work : StateT S m A) before = (fun result => (result,before)) <$> work := bind_pure_comp _ _

theorem kem_source (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
    (query : (RegistrationNativeSecretWordKemInterface.Routed KemSK).Domain) (before : Symbolic n KemSK) :
    Prod.map (RegistrationNativeSecretWordKemProvider.evalReply candidate query) (frame candidate) <$>
      ((lower setup wire sign seed scalar candidate unused
        (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge))
        (.inl (.inr (.inr query)))).run before =
      ((RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate
        (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected pairs publicKey challenge candidate))
        (.inl (.inr (.inr query)))).run (frame candidate before) := by
  rw [lower,QueryImpl.flattenStateT_mapStateTBase_apply_run]
  simp only [RegistrationNativePlatformLorOpenDictionary.handler,QueryImpl.mapStateTBase,StateT.mk,
    RegistrationNativePlatformLorWorldDictionary.handler,RegistrationNativePlatformLorWorldDictionary.routed,
    StateT.run,simulateQ_map,RegistrationNativePlatformLorWorldDictionary.coins,QueryImpl.simulateQ_compose]
  simp only [map_apply]
  have transported := world_source setup seed scalar candidate unused
    (simulateQ coinLift ((RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge query).run before.1.kem)) before.2
  simp only [StateT.run] at transported
  rw [transported]
  simp only [RegistrationNativeSelectiveHiddenInterpreter.handler,RegistrationNativeSelectiveHiddenInterpreter.onBase,
    RegistrationNativeHiddenInterpreter.handler,RegistrationNativeHiddenInterpreter.routed,StateT.run,frame,Functor.map_map]
  have coupled := provider_source (n := n) setup candidate selected pairs publicKey challenge query before.1.kem
  simp only [StateT.run] at coupled
  rw [coupled]
  simp only [Functor.map_map,Prod.map_apply,id_eq,frame]

theorem prepare_source (provider : RegistrationNativeSecretWordInterpreter.Provider KemSK)
    (nativeProvider : RegistrationNativeHiddenInterpreter.Provider KemSK RegistrationNativeKemSwitchSource.Phase)
    (message : RegistrationNativeSecretWordMessage.Message) (before : Symbolic n KemSK) :
    Prod.map (Option.map (RegistrationNativeSecretWordMessage.eval candidate)) (frame candidate) <$>
      ((lower setup wire sign seed scalar candidate unused provider) (.inl (.inl message))).run before =
      ((RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate nativeProvider)
        (.inl (.inl (RegistrationNativeSecretWordMessage.eval candidate message)))).run (frame candidate before) := by
  rw [lower,QueryImpl.flattenStateT_mapStateTBase_apply_run]
  rw [RegistrationNativePlatformLorOpenDictionary.prepare_run]
  simp only [simulateQ_bind,simulateQ_spec_query,RegistrationNativePlatformLorOpenDictionary.root,closing,
    StateT.run_bind,simulateQ_pure,StateT.run_pure]
  simp only [RegistrationNativePlatformLorOpenDictionary.actualRoots,QueryImpl.mapStateTBase,
    RegistrationNativeSelectiveHiddenService.prepare,RegistrationNativeSelectiveHiddenService.onHidden,
    RegistrationNativeHiddenService.prepare,map_apply,StateT.mk,
    RegistrationNativeSelectiveHiddenInterpreter.handler,RegistrationNativeSelectiveHiddenInterpreter.onBase,
    RegistrationNativeHiddenInterpreter.handler,RegistrationNativeHiddenInterpreter.onKeys,StateT.run,
    simulateQ_pure,map_pure,pure_bind,frame,Prod.map_apply,id_eq]
  rw [←RegistrationNativeSecretWordMessage.input_eval setup.joint setup.dh seed scalar candidate message]
  simp only [Option.map_map]
  rfl

theorem demand_source (provider : RegistrationNativeSecretWordInterpreter.Provider KemSK)
    (nativeProvider : RegistrationNativeHiddenInterpreter.Provider KemSK RegistrationNativeKemSwitchSource.Phase)
    (message : RegistrationNativeSecretWordMessage.Message) (before : Symbolic n KemSK) :
    Prod.map id (frame candidate) <$>
      ((lower setup wire sign seed scalar candidate unused provider) (.inl (.inr (.inl (.inl message))))).run before =
      ((RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate nativeProvider)
        (.inl (.inr (.inl (.inl (RegistrationNativeSecretWordMessage.eval candidate message)))))).run (frame candidate before) := by
  rw [lower,QueryImpl.flattenStateT_mapStateTBase_apply_run,RegistrationNativePlatformLorOpenDictionary.demand_run]
  simp only [simulateQ_map,RegistrationNativePlatformLorOpenDictionary.root,simulateQ_spec_query,closing,
    map_apply,RegistrationNativePlatformLorOpenDictionary.actualRoots,QueryImpl.mapStateTBase,StateT.mk,
    RegistrationNativeSelectiveHiddenInterpreter.handler,RegistrationNativeSelectiveHiddenInterpreter.onKeys,
    StateT.run,frame,Functor.map_map,Prod.map_apply,id_eq]
  rfl

theorem record_source (provider : RegistrationNativeSecretWordInterpreter.Provider KemSK)
    (nativeProvider : RegistrationNativeHiddenInterpreter.Provider KemSK RegistrationNativeKemSwitchSource.Phase)
    (query : PqxdhRecordLiftInterface.RecordQuery) (before : Symbolic n KemSK) :
    Prod.map id (frame candidate) <$>
      ((lower setup wire sign seed scalar candidate unused provider) (.inr query)).run before =
      ((RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate nativeProvider)
        (.inr query)).run (frame candidate before) := by
  rw [lower,QueryImpl.flattenStateT_mapStateTBase_apply_run]
  simp only [RegistrationNativePlatformLorOpenDictionary.handler,QueryImpl.mapStateTBase,StateT.mk,StateT.run]
  have rawRecord := RegistrationNativePlatformLorWorldDictionary.record_run setup wire sign
    (RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar)
    (RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) provider query before.1
  simp only [StateT.run] at rawRecord
  rw [rawRecord]
  simp only [RegistrationNativePlatformLorWorldDictionary.world,RegistrationNativePlatformLorOpenDictionary.embed,
    simulateQ_map,simulateQ_spec_query,closing,map_apply,lift_apply,
    RegistrationNativeSelectiveHiddenInterpreter.handler,RegistrationNativeSelectiveHiddenInterpreter.onBase,
    RegistrationNativeHiddenInterpreter.handler,StateT.run,Functor.map_map,Prod.map_apply,id_eq]
  rfl

theorem publication_source (provider : RegistrationNativeSecretWordInterpreter.Provider KemSK)
    (nativeProvider : RegistrationNativeHiddenInterpreter.Provider KemSK RegistrationNativeKemSwitchSource.Phase)
    (query : RegistrationBoundPublication.Spec.Domain) (before : Symbolic n KemSK) :
    Prod.map id (frame candidate) <$>
      ((lower setup wire sign seed scalar candidate unused provider) (.inl (.inr (.inl (.inr (.inl query)))))).run before =
      ((RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate nativeProvider)
        (.inl (.inr (.inl (.inr (.inl query)))))).run (frame candidate before) := by
  rw [lower,QueryImpl.flattenStateT_mapStateTBase_apply_run]
  simp only [RegistrationNativePlatformLorOpenDictionary.handler,QueryImpl.mapStateTBase,StateT.mk,
    RegistrationNativePlatformLorWorldDictionary.handler,RegistrationNativePlatformLorWorldDictionary.common,
    RegistrationNativePlatformLorWorldDictionary.publication,StateT.run,simulateQ_map,map_apply]
  have transported := effect_source setup seed scalar candidate unused
    ((RegistrationBoundSourceCompiler.compiler setup.source (RegistrationNativeWire.ledgerCodec wire).frameWrite sign query).run before.1.ordinary.receipts) before.2
  simp only [StateT.run] at transported
  rw [transported]
  simp only [RegistrationNativeSelectiveHiddenInterpreter.handler,RegistrationNativeSelectiveHiddenInterpreter.onBase,
    RegistrationNativeHiddenInterpreter.handler,RegistrationNativeHiddenInterpreter.publication,StateT.run,
    Functor.map_map,Prod.map_apply,id_eq,frame]
  rfl

theorem effect_query_source (provider : RegistrationNativeSecretWordInterpreter.Provider KemSK)
    (nativeProvider : RegistrationNativeHiddenInterpreter.Provider KemSK RegistrationNativeKemSwitchSource.Phase)
    (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) (before : Symbolic n KemSK) :
    Prod.map id (frame candidate) <$>
      ((lower setup wire sign seed scalar candidate unused provider) (.inl (.inr (.inl (.inr (.inr query)))))).run before =
      ((RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate nativeProvider)
        (.inl (.inr (.inl (.inr (.inr query)))))).run (frame candidate before) := by
  rw [lower,QueryImpl.flattenStateT_mapStateTBase_apply_run]
  simp only [RegistrationNativePlatformLorOpenDictionary.handler,QueryImpl.mapStateTBase,StateT.mk,StateT.run,
    RegistrationNativePlatformLorWorldDictionary.handler,RegistrationNativePlatformLorWorldDictionary.common,
    RegistrationNativePlatformLorWorldDictionary.effect,lift_apply,simulateQ_map,
    RegistrationNativePlatformLorWorldDictionary.world,RegistrationNativePlatformLorOpenDictionary.embed,
    simulateQ_spec_query,closing,map_apply,
    RegistrationNativeSelectiveHiddenInterpreter.handler,RegistrationNativeSelectiveHiddenInterpreter.onBase,
    RegistrationNativeHiddenInterpreter.handler,RegistrationNativeHiddenInterpreter.effect,Functor.map_map,frame,Prod.map_apply,id_eq]
  rfl

theorem query_source (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
    (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain) (before : Symbolic n KemSK) :
    Prod.map (nativeReply candidate query) (frame candidate) <$>
      ((lower setup wire sign seed scalar candidate unused
        (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge)) query).run before =
      ((RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate
        (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected pairs publicKey challenge candidate))
        (nativeQuery candidate query)).run (frame candidate before) := by
  rcases query with (message | (message | commonQuery) | routedQuery) | recordQuery
  · exact prepare_source setup wire sign seed scalar candidate unused _ _ message before
  · exact demand_source setup wire sign seed scalar candidate unused _ _ message before
  · rcases commonQuery with publicationQuery | effectQuery
    · exact publication_source setup wire sign seed scalar candidate unused _ _ publicationQuery before
    · exact effect_query_source setup wire sign seed scalar candidate unused _ _ effectQuery before
  · exact kem_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge routedQuery before
  · exact record_source setup wire sign seed scalar candidate unused _ _ recordQuery before

variable {Physical : Type}
theorem physical_query (physical : QueryImpl (WorldSpec n) (StateT Physical ProbComp))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
    (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain)
    (before : Symbolic n KemSK) (physicalBefore : Physical) :
    Prod.map (Prod.map (nativeReply candidate query) (frame candidate)) id <$>
      (simulateQ physical
        ((lower setup wire sign seed scalar candidate unused
          (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge)
          query).run before)).run physicalBefore =
      (simulateQ physical
        ((RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate
          (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected pairs publicKey challenge candidate)
          (nativeQuery candidate query)).run (frame candidate before))).run physicalBefore := by
  have sourceEq := congrArg (fun work => (simulateQ physical work).run physicalBefore)
    (query_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge query before)
  simpa only [simulateQ_map,StateT.run_map,Prod.map_def,id_eq] using sourceEq

end BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxLeaves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxLeaves.world_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxLeaves.world_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxLeaves.effect_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxLeaves.effect_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxLeaves.provider_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxLeaves.provider_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxLeaves.kem_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxLeaves.kem_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxLeaves.prepare_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxLeaves.prepare_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxLeaves.demand_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxLeaves.demand_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxLeaves.record_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxLeaves.record_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxLeaves.publication_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxLeaves.publication_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxLeaves.effect_query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxLeaves.effect_query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxLeaves.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxLeaves.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxLeaves.physical_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxLeaves.physical_query
