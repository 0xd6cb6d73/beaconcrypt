-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationWorldAgreement

/-!
The actual related-root family stage retains the complete instrumented World as its native auxiliary state. Agreement makes no CTX queries: the outer cache coordinate is a redundant retained value, and all actual World cache/signing/count state stays in the auxiliary coordinate. The source projection below is proved from actual callbacks, rather than supplied as a frontend simulation. Root-family state and HMAC history remain in the result until the explicitly stated projection forgets them.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option maxRecDepth 2048
namespace BeaconcryptCore.Computational.RegistrationWorldRoot
open PqxdhJointIdentity
open PqxdhBeaconPhase2Preparation (Word32)
open RegistrationWorldAgreement (State)
variable {n : Nat} {Auxiliary : Type}

noncomputable def primitive (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (native : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp)) :
    QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT (State n Auxiliary) ProbComp) :=
  fun query => RegistrationWorldAgreement.agreement source native query.toRequest

/-- The root branch is already the actual pure source HKDF; every other branch executes the original instrumented native callback. -/
theorem auxiliary_exact (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (native : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (query : RegistrationAgreementExecutor.Request) :
    RegistrationAgreementShared.auxiliary source (primitive source native) query =
      RegistrationWorldAgreement.agreement (n := n) source native query := by
  cases query <;> try rfl
  funext state
  simp only [RegistrationAgreementShared.auxiliary, RegistrationWorldAgreement.agreement,
    RegistrationWorldAgreement.recorded, List.append_nil, ]
  rfl

/-- The unused outer cache is retained verbatim and can be forgotten without changing any actual World operation. -/
theorem backend_project (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (native : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (query : RegistrationAgreementExecutor.Request)
    (before : RawCtxSharedPrimitive.SharedState (State n Auxiliary)) :
    Prod.map id Prod.fst <$>
      (RegistrationAgreementShared.implementation source (primitive source native) query).run before =
      (RegistrationWorldAgreement.agreement source native query).run before.1 := by
  simp only [RegistrationAgreementShared.implementation, StateT.run, auxiliary_exact,
    Functor.map_map, Prod.map, id_eq, Prod.mk.eta]
  exact id_map _

/-- The selected static-DH call records its actual public operand, including a failed optional result. -/
def visit (point : Word32) : StateT (State n Auxiliary) ProbComp Unit := fun before =>
  pure ((), { before with requests := before.requests ++ [.dh ⟨.LocalIdentity, point⟩] })

def visitShared (point : Word32) : StateT (RawCtxSharedPrimitive.SharedState (State n Auxiliary)) ProbComp Unit :=
  fun before => (fun result => (result.1, (result.2, before.2))) <$> (visit point).run before.1

/-- The actual selected static callback and the untouched redundant cache obey the same projection as every native callback. -/
theorem source_project (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (joint : Primitives) (seed : IdentitySeed)
    (native : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (query : RegistrationAgreementExecutor.Request)
    (before : RawCtxSharedPrimitive.SharedState (State n Auxiliary)) :
    Prod.map id Prod.fst <$>
      (RegistrationAgreementInterpreter.sourceImpl joint seed
        (RegistrationAgreementShared.implementation source (primitive source native)) visitShared query).run before =
      (RegistrationAgreementInterpreter.sourceImpl joint seed
        (RegistrationWorldAgreement.agreement source native) visit query).run before.1 := by
  cases query with
  | dh request =>
    cases role : request.secret_role with
    | LocalIdentity =>
      simp only [RegistrationAgreementInterpreter.sourceImpl, role]
      let response := RegistrationAgreementRoot.nativeOption
        ((joint.staticDh seed (PqxdhPhase2GapDhSource.peer request.public_key)).map PqxdhRootTableInitialization.rootArray)
      change Prod.map id Prod.fst <$> (do
        let visited ← (visitShared request.public_key).run before
        pure (response, visited.2)) = (do
          let visited ← (visit request.public_key).run before.1
          pure (response, visited.2))
      simp only [visitShared, visit, StateT.run, map_pure, pure_bind]
      rfl
    | ServerEphemeral =>
      simpa only [RegistrationAgreementInterpreter.sourceImpl, role] using backend_project source native (.dh request) before
    | BeaconPrekey =>
      simpa only [RegistrationAgreementInterpreter.sourceImpl, role] using backend_project source native (.dh request) before
    | BeaconOneTime =>
      simpa only [RegistrationAgreementInterpreter.sourceImpl, role] using backend_project source native (.dh request) before
  | root request => exact backend_project source native (.root request) before
  | convertPublic key => exact backend_project source native (.convertPublic key) before
  | convertSecret role => exact backend_project source native (.convertSecret role) before
  | generate role => exact backend_project source native (.generate role) before
  | encapsulate key => exact backend_project source native (.encapsulate key) before
  | decapsulate ciphertext => exact backend_project source native (.decapsulate ciphertext) before

theorem source_program_project {Result : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (joint : Primitives) (seed : IdentitySeed)
    (native : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (work : OracleComp RegistrationAgreementExecutor.Spec Result)
    (before : RawCtxSharedPrimitive.SharedState (State n Auxiliary)) :
    Prod.map id Prod.fst <$>
      (simulateQ (RegistrationAgreementInterpreter.sourceImpl joint seed
        (RegistrationAgreementShared.implementation source (primitive source native)) visitShared) work).run before =
      (simulateQ (RegistrationAgreementInterpreter.sourceImpl joint seed
        (RegistrationWorldAgreement.agreement source native) visit) work).run before.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst (source_project source joint seed native) work before

def cacheReceipts (state : State n Auxiliary) := (state.world.1.primitive.2, state.world.2)

/-- Neither native key agreement nor selected static-DH instrumentation changes the World cache or signing receipts. -/
theorem source_keeps (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (joint : Primitives) (seed : IdentitySeed)
    (native : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (query : RegistrationAgreementExecutor.Request) (before : State n Auxiliary)
    (result : RegistrationAgreementExecutor.Spec.Range query × State n Auxiliary)
    (supported : result ∈ support ((RegistrationAgreementInterpreter.sourceImpl joint seed
      (RegistrationWorldAgreement.agreement source native) visit query).run before)) :
    cacheReceipts result.2 = cacheReceipts before := by
  have regular : ∀ (query : RegistrationAgreementExecutor.Request)
      (result : RegistrationAgreementExecutor.Spec.Range query × State n Auxiliary),
      result ∈ support ((RegistrationWorldAgreement.agreement source native query).run before) →
      cacheReceipts result.2 = cacheReceipts before := by
    intro query result reached
    obtain ⟨cache, receipts, _⟩ := RegistrationWorldAgreement.agreement_cache_receipts source native query before result reached
    exact Prod.ext cache receipts
  cases query with
  | dh request =>
    cases role : request.secret_role with
    | LocalIdentity =>
      simp only [RegistrationAgreementInterpreter.sourceImpl, role, StateT.run] at supported
      change result ∈ support (pure (_, _) : ProbComp _) at supported
      simp only [mem_support_pure_iff] at supported
      subst result
      rfl
    | ServerEphemeral => exact regular (.dh request) result (by simpa only [RegistrationAgreementInterpreter.sourceImpl, role] using supported)
    | BeaconPrekey => exact regular (.dh request) result (by simpa only [RegistrationAgreementInterpreter.sourceImpl, role] using supported)
    | BeaconOneTime => exact regular (.dh request) result (by simpa only [RegistrationAgreementInterpreter.sourceImpl, role] using supported)
  | root request => exact regular (.root request) result supported
  | convertPublic key => exact regular (.convertPublic key) result supported
  | convertSecret role => exact regular (.convertSecret role) result supported
  | generate role => exact regular (.generate role) result supported
  | encapsulate key => exact regular (.encapsulate key) result supported
  | decapsulate ciphertext => exact regular (.decapsulate ciphertext) result supported

theorem source_program_keeps {Result : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (joint : Primitives) (seed : IdentitySeed)
    (native : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (work : OracleComp RegistrationAgreementExecutor.Spec Result) (before : State n Auxiliary)
    (result : Result × State n Auxiliary)
    (supported : result ∈ support ((simulateQ (RegistrationAgreementInterpreter.sourceImpl joint seed
      (RegistrationWorldAgreement.agreement source native) visit) work).run before)) :
    cacheReceipts result.2 = cacheReceipts before :=
  simulateQ_run_preservesInv _ (fun current => cacheReceipts current = cacheReceipts before)
    (fun query current earlier after reached =>
      (source_keeps source joint seed native query current after reached).trans earlier)
    work before rfl result supported

abbrev FullState (n : Nat) (Auxiliary : Type) := PqxdhServerRelatedRootConsumer.State (State n Auxiliary)

noncomputable def stage (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (joint : Primitives) (dh : PqxdhJointGapDh.DhInterface joint) (domain : PqxdhServerStaticDhSource.PublicDomain joint)
    (seed : IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (native : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    StateT (FullState n Auxiliary) ProbComp (RustM agreement.AgreementEffect) := fun before =>
  (fun result => (result.1, (result.2.1, result.2.2.1))) <$>
    (RegistrationRelatedRoot.stage domain
      (RegistrationAgreementInterpreter.prepImpl (RegistrationRootStage.lifted
        (RegistrationAgreementShared.implementation source (primitive source native))))
      (fun point => RegistrationRootStage.lift (visitShared point))
      (PqxdhJointDhExtractFamily.realImpl hmac joint dh seed scalar ∘ₛ PqxdhJointDhExtractRoot.reduction)
      RegistrationAgreementFinish.quiet packet authenticated).run
        (before.1, (before.2, before.2.world.1.primitive.2))

/-- Full real-family execution projects to the actual native Server controller with the same World counts, cache and signing receipts, without a frontend simulation premise. -/
theorem stage_project (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect source hmac)
    (joint : Primitives) (dh : PqxdhJointGapDh.DhInterface joint) (domain : PqxdhServerStaticDhSource.PublicDomain joint)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring source.crypto joint secretOfSeed)
    (seed : IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (native : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (control : pqxdh.ServerState) (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : FullState n Auxiliary) :
    Prod.map id Prod.snd <$> (stage source hmac joint dh domain seed scalar native packet authenticated).run before =
      (simulateQ (RegistrationAgreementInterpreter.sourceImpl joint seed
        (RegistrationWorldAgreement.agreement source native) visit)
        (RegistrationAgreementExecutor.server control .Fresh authenticated)).run before.2 := by
  have first := congrArg (fun work => Prod.map id Prod.fst <$> work)
    (RegistrationRootStage.stage_native source hmac correct joint dh domain secretOfSeed wiring seed scalar
      (primitive source native) visitShared control packet authenticated
      (before.1, (before.2, before.2.world.1.primitive.2)))
  have second := source_program_project source joint seed native
    (RegistrationAgreementExecutor.server control .Fresh authenticated)
    (before.2, before.2.world.1.primitive.2)
  have first' : Prod.map id Prod.snd <$> (stage source hmac joint dh domain seed scalar native packet authenticated).run before =
      Prod.map id Prod.fst <$>
        (simulateQ (RegistrationAgreementInterpreter.sourceImpl joint seed
          (RegistrationAgreementShared.implementation source (primitive source native)) visitShared)
          (RegistrationAgreementExecutor.server control .Fresh authenticated)).run
            (before.2, before.2.world.1.primitive.2) := by
    simpa only [stage, StateT.run, Functor.map_map, Prod.map, id_eq] using first
  exact first'.trans second

/-- The actual whole real-family phase derives cache/history stability; no diagonal-cache or history preservation assumption is supplied. -/
theorem stage_keeps (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect source hmac)
    (joint : Primitives) (dh : PqxdhJointGapDh.DhInterface joint) (domain : PqxdhServerStaticDhSource.PublicDomain joint)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring source.crypto joint secretOfSeed)
    (seed : IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (native : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (control : pqxdh.ServerState) (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : FullState n Auxiliary) (result : RustM agreement.AgreementEffect × FullState n Auxiliary)
    (supported : result ∈ support ((stage source hmac joint dh domain seed scalar native packet authenticated).run before)) :
    cacheReceipts result.2.2 = cacheReceipts before.2 := by
  apply source_program_keeps source joint seed native (RegistrationAgreementExecutor.server control .Fresh authenticated)
    before.2 (result.1, result.2.2)
  rw [← stage_project source hmac correct joint dh domain secretOfSeed wiring seed scalar native
    control packet authenticated before, support_map]
  exact Set.mem_image_of_mem (Prod.map id Prod.snd) supported

end BeaconcryptCore.Computational.RegistrationWorldRoot

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldRoot.auxiliary_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldRoot.auxiliary_exact

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldRoot.backend_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldRoot.backend_project

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldRoot.source_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldRoot.source_project

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldRoot.source_program_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldRoot.source_program_project

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldRoot.source_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldRoot.source_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldRoot.source_program_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldRoot.source_program_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldRoot.stage_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldRoot.stage_project

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldRoot.stage_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldRoot.stage_keeps
