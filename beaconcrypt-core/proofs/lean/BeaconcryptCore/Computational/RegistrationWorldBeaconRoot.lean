-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationWorldRoot
import BeaconcryptCore.Computational.RegistrationBeaconRootStage

/-! Beacon agreement retains the same full instrumented World and family state as Server agreement. The actual public-conversion callback is recorded before continuing. Its ordinary source conversion equation is derived from that concrete callback, so conversion effects are retained rather than bypassed by a local adapter. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationWorldBeaconRoot
open PqxdhJointIdentity PqxdhJointGapDh
open PqxdhBeaconPhase2Preparation (Word32)
open RegistrationWorldAgreement (State)
open RegistrationWorldRoot (primitive backend_project cacheReceipts)
variable {n : Nat} {Auxiliary : Type}

def visit (point : Word32) : StateT (State n Auxiliary) ProbComp Unit := fun before =>
  pure ((), { before with requests := before.requests ++ [.dh ⟨.BeaconPrekey, point⟩] })

def visitShared (point : Word32) : StateT (RawCtxSharedPrimitive.SharedState (State n Auxiliary)) ProbComp Unit :=
  fun before => (fun result => (result.1, (result.2, before.2))) <$> (visit point).run before.1

theorem source_project (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    {joint : Primitives} (dh : PqxdhJointGapDh.DhInterface joint) (scalar : PqxdhJointGapDh.ScalarBytes)
    (native : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (query : RegistrationAgreementExecutor.Request)
    (before : RawCtxSharedPrimitive.SharedState (State n Auxiliary)) :
    Prod.map id Prod.fst <$>
      (RegistrationBeaconRootInterpreter.sourceImpl dh scalar
        (RegistrationAgreementShared.implementation source (primitive source native)) visitShared query).run before =
      (RegistrationBeaconRootInterpreter.sourceImpl dh scalar
        (RegistrationWorldAgreement.agreement source native) visit query).run before.1 := by
  cases query with
  | dh request =>
    cases role : request.secret_role with
    | BeaconPrekey =>
      simp only [RegistrationBeaconRootInterpreter.sourceImpl, role]
      let response := RegistrationAgreementRoot.nativeOption
        ((dh.dh scalar (PqxdhPhase2GapDhSource.peer request.public_key)).map PqxdhPhase2GapDhSource.word)
      change Prod.map id Prod.fst <$> (do
        let visited ← (visitShared request.public_key).run before
        pure (response, visited.2)) = (do
          let visited ← (visit request.public_key).run before.1
          pure (response, visited.2))
      simp only [visitShared, visit, StateT.run, map_pure, pure_bind]
      rfl
    | ServerEphemeral =>
      simpa only [RegistrationBeaconRootInterpreter.sourceImpl, role] using backend_project source native (.dh request) before
    | LocalIdentity =>
      simpa only [RegistrationBeaconRootInterpreter.sourceImpl, role] using backend_project source native (.dh request) before
    | BeaconOneTime =>
      simpa only [RegistrationBeaconRootInterpreter.sourceImpl, role] using backend_project source native (.dh request) before
  | root request => exact backend_project source native (.root request) before
  | convertPublic key => exact backend_project source native (.convertPublic key) before
  | convertSecret role => exact backend_project source native (.convertSecret role) before
  | generate role => exact backend_project source native (.generate role) before
  | encapsulate key => exact backend_project source native (.encapsulate key) before
  | decapsulate ciphertext => exact backend_project source native (.decapsulate ciphertext) before

theorem source_program_project {Result : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    {joint : Primitives} (dh : PqxdhJointGapDh.DhInterface joint) (scalar : PqxdhJointGapDh.ScalarBytes)
    (native : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (work : OracleComp RegistrationAgreementExecutor.Spec Result)
    (before : RawCtxSharedPrimitive.SharedState (State n Auxiliary)) :
    Prod.map id Prod.fst <$>
      (simulateQ (RegistrationBeaconRootInterpreter.sourceImpl dh scalar
        (RegistrationAgreementShared.implementation source (primitive source native)) visitShared) work).run before =
      (simulateQ (RegistrationBeaconRootInterpreter.sourceImpl dh scalar
        (RegistrationWorldAgreement.agreement source native) visit) work).run before.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst (source_project source dh scalar native) work before


/-- Actual instrumented conversion success implies the source conversion equation while retaining its complete reached World state. -/
theorem conversion_sound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (native : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (key converted : Word32) (before after : State n Auxiliary)
    (supported : (.Some converted, after) ∈ support
      ((RegistrationWorldAgreement.agreement source (RegistrationPublicConversion.primitive source.crypto native)
        (.convertPublic key)).run before)) :
    source.crypto.xpkConv (absBytes key) = some (absBytes converted) := by
  apply RegistrationPublicConversion.query_sound source native key converted
    (RegistrationWorldAgreement.project before) (RegistrationWorldAgreement.project after)
  rw [← RegistrationWorldAgreement.agreement_project source
    (RegistrationPublicConversion.primitive source.crypto native) (.convertPublic key) before, support_map]
  exact Set.mem_image_of_mem (Prod.map id RegistrationWorldAgreement.project) supported

theorem aux_conversion (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (native : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (authenticated : registration.AuthenticatedResponse) (key : Word32)
    (before : RawCtxSharedPrimitive.SharedState (State n Auxiliary)) (converted : Word32)
    (after : RawCtxSharedPrimitive.SharedState (State n Auxiliary))
    (supported : (some converted, after) ∈ support
      ((RegistrationBeaconRootInterpreter.auxImpl
        (RegistrationAgreementShared.implementation source
          (primitive source (RegistrationPublicConversion.primitive source.crypto native)))
        authenticated (.publicConversion key)).run before)) :
    source.crypto.xpkConv (absBytes key) = some (absBytes converted) := by
  simp only [RegistrationBeaconRootInterpreter.auxImpl, RegistrationBeaconAgreementRoot.callbacks,
    simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map] at supported
  obtain ⟨⟨reply, reached⟩, member, same⟩ := supported
  cases reply with
  | none => simp only [RegistrationAgreementRoot.option, Prod.mk.injEq, reduceCtorEq, false_and] at same
  | some word =>
    have equal : word = converted := Option.some.inj (congrArg Prod.fst same)
    subst word
    have actual : (.Some converted, reached.1) ∈ support
        ((RegistrationWorldAgreement.agreement source (RegistrationPublicConversion.primitive source.crypto native)
          (.convertPublic key)).run before.1) := by
      rw [← backend_project source (RegistrationPublicConversion.primitive source.crypto native)
        (.convertPublic key) before, support_map]
      exact Set.mem_image_of_mem (Prod.map id Prod.fst) member
    exact conversion_sound source native key converted before.1 reached.1 actual

theorem source_keeps (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    {joint : Primitives} (dh : DhInterface joint) (scalar : ScalarBytes)
    (native : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (query : RegistrationAgreementExecutor.Request) (before : State n Auxiliary)
    (result : RegistrationAgreementExecutor.Spec.Range query × State n Auxiliary)
    (supported : result ∈ support ((RegistrationBeaconRootInterpreter.sourceImpl dh scalar
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
    | BeaconPrekey =>
      simp only [RegistrationBeaconRootInterpreter.sourceImpl, role, StateT.run] at supported
      change result ∈ support (pure (_, _) : ProbComp _) at supported
      simp only [mem_support_pure_iff] at supported
      subst result
      rfl
    | ServerEphemeral => exact regular (.dh request) result (by simpa only [RegistrationBeaconRootInterpreter.sourceImpl, role] using supported)
    | LocalIdentity => exact regular (.dh request) result (by simpa only [RegistrationBeaconRootInterpreter.sourceImpl, role] using supported)
    | BeaconOneTime => exact regular (.dh request) result (by simpa only [RegistrationBeaconRootInterpreter.sourceImpl, role] using supported)
  | root request => exact regular (.root request) result supported
  | convertPublic key => exact regular (.convertPublic key) result supported
  | convertSecret role => exact regular (.convertSecret role) result supported
  | generate role => exact regular (.generate role) result supported
  | encapsulate key => exact regular (.encapsulate key) result supported
  | decapsulate ciphertext => exact regular (.decapsulate ciphertext) result supported

theorem source_program_keeps {Result : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    {joint : Primitives} (dh : DhInterface joint) (scalar : ScalarBytes)
    (native : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (work : OracleComp RegistrationAgreementExecutor.Spec Result) (before : State n Auxiliary)
    (result : Result × State n Auxiliary)
    (supported : result ∈ support ((simulateQ (RegistrationBeaconRootInterpreter.sourceImpl dh scalar
      (RegistrationWorldAgreement.agreement source native) visit) work).run before)) :
    cacheReceipts result.2 = cacheReceipts before :=
  simulateQ_run_preservesInv _ (fun current => cacheReceipts current = cacheReceipts before)
    (fun query current earlier after reached =>
      (source_keeps source dh scalar native query current after reached).trans earlier)
    work before rfl result supported


abbrev FullState (n : Nat) (Auxiliary : Type) := RegistrationWorldRoot.FullState n Auxiliary

noncomputable def stage (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (hmac : PqxdhSecretInputKdf.HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (domain : PqxdhPhase2GapDhSource.PublicDomain dh) (seed : IdentitySeed) (scalar : ScalarBytes)
    (native : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (authenticated : registration.AuthenticatedResponse) :
    StateT (FullState n Auxiliary) ProbComp (RustM agreement.AgreementEffect) := fun before =>
  (fun result => (result.1, (result.2.1, result.2.2.1))) <$>
    (RegistrationBeaconRootStage.stage domain
      (RegistrationAgreementShared.implementation source
        (primitive source (RegistrationPublicConversion.primitive source.crypto native))) visitShared
      (PqxdhJointDhExtractFamily.realImpl hmac joint dh seed scalar ∘ₛ PqxdhJointDhExtractRoot.reduction)
      (challenge joint dh seed scalar) authenticated).run
        (before.1, (before.2, before.2.world.1.primitive.2))

/-- The real related-DH Beacon stage equals the actual native Beacon controller with the same complete World, including reached conversion and selected-prekey DH requests. -/
theorem stage_project (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (hmac : PqxdhSecretInputKdf.HmacSha512) (correct : PqxdhSecretInputKdf.SourceRootCorrect source hmac)
    (joint : Primitives) (dh : DhInterface joint)
    (domain : PqxdhPhase2GapDhSource.PublicDomain dh) (seed : IdentitySeed) (scalar : ScalarBytes)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring source.crypto joint secretOfSeed)
    (native : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (authenticated : registration.AuthenticatedResponse)
    (pin : absBytes authenticated.pending.control.expected_server_binding.identity_public_key =
      (joint.publicKeys seed).ed25519.toList)
    (coherent : authenticated.pending.control.expected_server_binding = authenticated.pending.binding.server_pin.binding)
    (before : FullState n Auxiliary) :
    Prod.map id Prod.snd <$> (stage source hmac joint dh domain seed scalar native authenticated).run before =
      (simulateQ (RegistrationBeaconRootInterpreter.sourceImpl dh scalar
        (RegistrationWorldAgreement.agreement source (RegistrationPublicConversion.primitive source.crypto native)) visit)
        (RegistrationAgreementExecutor.beacon authenticated)).run before.2 := by
  have first := congrArg (fun work => Prod.map id Prod.fst <$> work)
    (RegistrationBeaconRootStage.stage_real_effectful source hmac correct joint dh domain seed scalar secretOfSeed wiring
      (primitive source (RegistrationPublicConversion.primitive source.crypto native))
      authenticated (aux_conversion source native authenticated) visitShared pin coherent
      (before.1, (before.2, before.2.world.1.primitive.2)))
  have first' : Prod.map id Prod.snd <$> (stage source hmac joint dh domain seed scalar native authenticated).run before =
      Prod.map id Prod.fst <$>
        (simulateQ (RegistrationBeaconRootInterpreter.sourceImpl dh scalar
          (RegistrationAgreementShared.implementation source
            (primitive source (RegistrationPublicConversion.primitive source.crypto native))) visitShared)
          (RegistrationAgreementExecutor.beacon authenticated)).run
            (before.2, before.2.world.1.primitive.2) := by
    simpa only [stage, StateT.run, Functor.map_map, Prod.map, id_eq] using first
  exact first'.trans (source_program_project source dh scalar (RegistrationPublicConversion.primitive source.crypto native)
    (RegistrationAgreementExecutor.beacon authenticated) (before.2, before.2.world.1.primitive.2))

/-- Agreement derives preservation of the actual shared cache and chronological ML receipts through the whole related-root family stage. -/
theorem stage_keeps (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (hmac : PqxdhSecretInputKdf.HmacSha512) (correct : PqxdhSecretInputKdf.SourceRootCorrect source hmac)
    (joint : Primitives) (dh : DhInterface joint)
    (domain : PqxdhPhase2GapDhSource.PublicDomain dh) (seed : IdentitySeed) (scalar : ScalarBytes)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring source.crypto joint secretOfSeed)
    (native : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (authenticated : registration.AuthenticatedResponse)
    (pin : absBytes authenticated.pending.control.expected_server_binding.identity_public_key =
      (joint.publicKeys seed).ed25519.toList)
    (coherent : authenticated.pending.control.expected_server_binding = authenticated.pending.binding.server_pin.binding)
    (before : FullState n Auxiliary) (result : RustM agreement.AgreementEffect × FullState n Auxiliary)
    (supported : result ∈ support ((stage source hmac joint dh domain seed scalar native authenticated).run before)) :
    cacheReceipts result.2.2 = cacheReceipts before.2 := by
  apply source_program_keeps source dh scalar (RegistrationPublicConversion.primitive source.crypto native)
    (RegistrationAgreementExecutor.beacon authenticated) before.2 (result.1, result.2.2)
  rw [← stage_project source hmac correct joint dh domain seed scalar secretOfSeed wiring native
    authenticated pin coherent before, support_map]
  exact Set.mem_image_of_mem (Prod.map id Prod.snd) supported

end BeaconcryptCore.Computational.RegistrationWorldBeaconRoot

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldBeaconRoot.source_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldBeaconRoot.source_project

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldBeaconRoot.source_program_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldBeaconRoot.source_program_project

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldBeaconRoot.conversion_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldBeaconRoot.conversion_sound

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldBeaconRoot.aux_conversion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldBeaconRoot.aux_conversion

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldBeaconRoot.source_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldBeaconRoot.source_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldBeaconRoot.source_program_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldBeaconRoot.source_program_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldBeaconRoot.stage_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldBeaconRoot.stage_project

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldBeaconRoot.stage_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldBeaconRoot.stage_keeps
