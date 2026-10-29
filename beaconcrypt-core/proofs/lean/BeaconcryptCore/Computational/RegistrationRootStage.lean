-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAgreementFinish
import BeaconcryptCore.Computational.RegistrationAgreementInterpreter

/-! The real related-root stage projects to the complete native server agreement execution. Root-family instrumentation keeps the actual auxiliary effects and CTX cache, and the source prefix derives its credential and private-coordinate references. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace BeaconcryptCore.Computational.RegistrationRootStage

open RegistrationAgreementExecutor
open PqxdhBeaconPhase2Preparation (Word32)
open PqxdhServerRelatedRootConsumer (State)
open PqxdhJointIdentity

def lift {Auxiliary Value : Type} (work : StateT Auxiliary ProbComp Value) :
    StateT (State Auxiliary) ProbComp Value := fun before =>
  (fun result => (result.1, (before.1, result.2))) <$> work.run before.2

theorem lift_project {Auxiliary Value : Type} (work : StateT Auxiliary ProbComp Value) (before : State Auxiliary) :
    Prod.map id Prod.snd <$> (lift work).run before = work.run before.2 := by
  simp only [lift, StateT.run, Functor.map_map, Prod.map, id_eq, Prod.mk.eta]
  exact id_map (work.run before.2)

def lifted {Auxiliary : Type} (backend : QueryImpl Spec (StateT Auxiliary ProbComp)) :
    QueryImpl Spec (StateT (State Auxiliary) ProbComp) := fun query => lift (backend query)

theorem lifted_program {Auxiliary Result : Type} (backend : QueryImpl Spec (StateT Auxiliary ProbComp))
    (work : OracleComp Spec Result) (before : State Auxiliary) :
    Prod.map id Prod.snd <$> (simulateQ (lifted backend) work).run before =
      (simulateQ backend work).run before.2 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.snd
    (fun query current => lift_project (backend query) current) work before

theorem prep_project {Auxiliary : Type} (backend : QueryImpl Spec (StateT Auxiliary ProbComp))
    (query : (PqxdhServerRootPreparation.Spec registration.InitPacket Unit Unit).Domain)
    (before : State Auxiliary) :
    Prod.map id Prod.snd <$> (RegistrationAgreementInterpreter.prepImpl (lifted backend) query).run before =
      (RegistrationAgreementInterpreter.prepImpl backend query).run before.2 := by
  cases query <;> simp only [RegistrationAgreementInterpreter.prepImpl]
  all_goals first | rfl | exact lifted_program backend _ before

theorem native_prep_project {Auxiliary : Type} (joint : Primitives) (seed : IdentitySeed)
    (backend : QueryImpl Spec (StateT Auxiliary ProbComp)) (visit : Word32 → StateT Auxiliary ProbComp Unit)
    (query : (PqxdhServerRootPreparation.Spec registration.InitPacket Unit Word32).Domain)
    (before : State Auxiliary) :
    Prod.map id Prod.snd <$>
      (PqxdhServerStaticDhSource.nativeImpl joint seed (RegistrationAgreementInterpreter.prepImpl (lifted backend))
        (fun point => lift (visit point)) query).run before =
      (PqxdhServerStaticDhSource.nativeImpl joint seed (RegistrationAgreementInterpreter.prepImpl backend) visit query).run before.2 := by
  cases query with
  | decode raw =>
    simpa only [PqxdhServerStaticDhSource.nativeImpl, StateT.run] using prep_project backend (.decode raw) before
  | identity packet =>
    simpa only [PqxdhServerStaticDhSource.nativeImpl, StateT.run] using prep_project backend (.identity packet) before
  | identityPoint key =>
    simpa only [PqxdhServerStaticDhSource.nativeImpl, StateT.run] using prep_project backend (.identityPoint key) before
  | pqField packet =>
    simpa only [PqxdhServerStaticDhSource.nativeImpl, StateT.run] using prep_project backend (.pqField packet) before
  | preField packet =>
    simpa only [PqxdhServerStaticDhSource.nativeImpl, StateT.run] using prep_project backend (.preField packet) before
  | oneField packet =>
    simpa only [PqxdhServerStaticDhSource.nativeImpl, StateT.run] using prep_project backend (.oneField packet) before
  | verify key signed =>
    simpa only [PqxdhServerStaticDhSource.nativeImpl, StateT.run] using prep_project backend (.verify key signed) before
  | registrationStatus rid =>
    simpa only [PqxdhServerStaticDhSource.nativeImpl, StateT.run] using prep_project backend (.registrationStatus rid) before
  | reserveRegistration =>
    simpa only [PqxdhServerStaticDhSource.nativeImpl, StateT.run] using prep_project backend (.reserveRegistration) before
  | parseDh point =>
    simpa only [PqxdhServerStaticDhSource.nativeImpl, StateT.run] using prep_project backend (.parseDh point) before
  | generate =>
    simpa only [PqxdhServerStaticDhSource.nativeImpl, StateT.run] using prep_project backend (.generate) before
  | parseKem key =>
    simpa only [PqxdhServerStaticDhSource.nativeImpl, StateT.run] using prep_project backend (.parseKem key) before
  | encapsulate key =>
    simpa only [PqxdhServerStaticDhSource.nativeImpl, StateT.run] using prep_project backend (.encapsulate key) before
  | publicConversion key =>
    simpa only [PqxdhServerStaticDhSource.nativeImpl, StateT.run] using prep_project backend (.publicConversion key) before
  | privateConversion =>
    simpa only [PqxdhServerStaticDhSource.nativeImpl, StateT.run] using prep_project backend (.privateConversion) before
  | ephemeralDh secret key =>
    simpa only [PqxdhServerStaticDhSource.nativeImpl, StateT.run] using prep_project backend (.ephemeralDh secret key) before
  | staticDh point =>
    change Prod.map id Prod.snd <$> (do
      let visited ← (lift (visit point)).run before
      pure ((joint.staticDh seed (PqxdhPhase2GapDhSource.peer point)).map PqxdhRootTableInitialization.rootArray, visited.2)) =
      (do let visited ← (visit point).run before.2
          pure ((joint.staticDh seed (PqxdhPhase2GapDhSource.peer point)).map PqxdhRootTableInitialization.rootArray, visited.2))
    simp only [lift, StateT.run, bind_map_left, map_bind, map_pure, Prod.map, id_eq]

theorem native_prefix_project {Auxiliary Result : Type} (joint : Primitives) (seed : IdentitySeed)
    (backend : QueryImpl Spec (StateT Auxiliary ProbComp)) (visit : Word32 → StateT Auxiliary ProbComp Unit)
    (work : OracleComp (PqxdhServerRootPreparation.Spec registration.InitPacket Unit Word32) Result)
    (before : State Auxiliary) :
    Prod.map id Prod.snd <$>
      (simulateQ (PqxdhServerStaticDhSource.nativeImpl joint seed (RegistrationAgreementInterpreter.prepImpl (lifted backend))
        (fun point => lift (visit point))) work).run before =
      (simulateQ (PqxdhServerStaticDhSource.nativeImpl joint seed
        (RegistrationAgreementInterpreter.prepImpl backend) visit) work).run before.2 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.snd
    (native_prep_project joint seed backend visit) work before

theorem finish_impl {m : Type → Type} [Monad m] [LawfulMonad m]
    (joint : Primitives) (seed : IdentitySeed) (backend : QueryImpl Spec m) (visit : Word32 → m Unit)
    (control : pqxdh.ServerState) (authenticated : registration.AuthenticatedInit)
    (input : PqxdhServerRootPreparation.Inputs registration.InitPacket Unit Word32)
    (credential : PqxdhProtocolAcceptance.verified input.verified.identity input.verified.keys = authenticated.registration) :
    simulateQ (RegistrationAgreementInterpreter.sourceImpl joint seed backend visit)
        (RegistrationAgreementRoot.finish control authenticated input) =
      simulateQ backend (RegistrationAgreementRoot.finish control authenticated input) := by
  rw [RegistrationAgreementFinish.finish_source control authenticated input credential]
  obtain ⟨accepted, acceptedRun⟩ := BeaconcryptCore.PanicFreedom.server_accept_ok control
    (PqxdhProtocolAcceptance.verified input.verified.identity input.verified.keys)
    .Fresh authenticated.binding.server_pin.binding ⟨input.ephemeral.publicKey, input.ciphertext⟩
    (PqxdhServerRelatedRootInput.secrets input)
  have actual : PqxdhServerRelatedRootInput.accept control authenticated.binding.server_pin.binding input = .ok accepted :=
    acceptedRun
  cases accepted with
  | Err error => simp only [RegistrationAgreementFinish.finishSource, actual, continueWith, simulateQ_pure]
  | Ok pair =>
      rcases pair with ⟨next, original⟩
      have requested : (⟨.Server original authenticated.binding⟩ : agreement.RootKdfPending).request =
          .ok ⟨original.root_key_input.bytes, pqxdh.PQXDH_INFO⟩ := by
        simp only [agreement.RootKdfPending.request, pqxdh.PendingServerRegistration.impl.root_key_input,
          pqxdh.RootKeyInput.as_bytes, bind_tc_ok]
      simp only [RegistrationAgreementFinish.finishSource, actual, continueWith]
      rw [RegistrationAgreementFinish.root_step _ _ requested]
      simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, RegistrationAgreementInterpreter.sourceImpl]

/-- A reached native prefix, rather than an assumed credential tuple, discharges root admission. -/
theorem reached_credential {Auxiliary : Type} (joint : Primitives) (seed : IdentitySeed)
    (backend : QueryImpl Spec (StateT Auxiliary ProbComp)) (visit : Word32 → StateT Auxiliary ProbComp Unit)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before after : State Auxiliary)
    (input : PqxdhServerRootPreparation.Inputs registration.InitPacket Unit Word32)
    (supported : (some input, after) ∈ support
      ((simulateQ (PqxdhServerStaticDhSource.nativeImpl joint seed
        (RegistrationAgreementInterpreter.prepImpl (lifted backend)) (fun point => lift (visit point)))
        (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated))).run before)) :
    PqxdhProtocolAcceptance.verified input.verified.identity input.verified.keys = authenticated.registration := by
  have openMember : some input ∈ support
      (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated)) := by
    apply OracleComp.support_simulateQ_run'_subset
      (PqxdhServerStaticDhSource.nativeImpl joint seed
        (RegistrationAgreementInterpreter.prepImpl (lifted backend)) (fun point => lift (visit point)))
      (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated)) before
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst supported
  rw [RegistrationRootInput.collected_verified (RegistrationRootInput.verified packet authenticated) input openMember]
  exact RegistrationRootInput.verified_native packet authenticated

/-- The complete actual Server agreement prefix and root completion retain the original auxiliary state and shared cache after forgetting only root-family instrumentation. -/
theorem native_stage_project {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (joint : Primitives) (seed : IdentitySeed)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (visit : Word32 → StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp Unit)
    (control : pqxdh.ServerState) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit)
    (before : State (RawCtxSharedPrimitive.SharedState Auxiliary)) :
    Prod.map id Prod.snd <$>
      (RegistrationRelatedRoot.nativeStage source hmac joint seed
        (RegistrationAgreementInterpreter.prepImpl (lifted (RegistrationAgreementShared.implementation source primitive)))
        (fun point => lift (visit point)) RegistrationAgreementFinish.quiet control packet authenticated).run before =
      (simulateQ (RegistrationAgreementInterpreter.sourceImpl joint seed
        (RegistrationAgreementShared.implementation source primitive) visit)
        (server control .Fresh authenticated)).run before.2 := by
  rw [RegistrationAgreementInterpreter.server_source joint seed
    (RegistrationAgreementShared.implementation source primitive) visit control packet authenticated]
  simp only [RegistrationRelatedRoot.nativeStage, StateT.run_bind, map_bind]
  rw [← native_prefix_project joint seed (RegistrationAgreementShared.implementation source primitive) visit
    (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated)) before]
  rw [bind_map_left]
  apply bind_congr_of_forall_mem_support
  rintro ⟨input, after⟩ reached
  cases input with
  | none => simp only [StateT.run_pure, map_pure]; rfl
  | some input =>
    have credential := reached_credential joint seed (RegistrationAgreementShared.implementation source primitive)
      visit packet authenticated before after input reached
    change Prod.map id Prod.snd <$>
        (RegistrationRelatedRoot.source source hmac RegistrationAgreementFinish.quiet control authenticated.binding input).run after =
      (simulateQ (RegistrationAgreementInterpreter.sourceImpl joint seed
        (RegistrationAgreementShared.implementation source primitive) visit)
        (RegistrationAgreementRoot.finish control authenticated input)).run after.2
    rw [← RegistrationAgreementFinish.finish_native source hmac primitive control authenticated.binding input]
    rw [RegistrationAgreementFinish.instrument_program]
    rw [← RegistrationAgreementFinish.finish_source control authenticated input credential]
    rw [finish_impl joint seed (RegistrationAgreementShared.implementation source primitive) visit
      control authenticated input credential]

/-- The real related-root family implements the complete actual authenticated Server agreement, preserving every reached auxiliary effect, the shared CTX cache and the populated native binding. Functional primitive correctness supplies the family realization; no registration or root-stage simulation is assumed. -/
theorem stage_native {Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect source hmac)
    (joint : Primitives) (dh : PqxdhJointGapDh.DhInterface joint) (domain : PqxdhServerStaticDhSource.PublicDomain joint)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring source.crypto joint secretOfSeed)
    (seed : IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (visit : Word32 → StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp Unit)
    (control : pqxdh.ServerState) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit)
    (before : State (RawCtxSharedPrimitive.SharedState Auxiliary)) :
    Prod.map id Prod.snd <$>
      (RegistrationRelatedRoot.stage domain
        (RegistrationAgreementInterpreter.prepImpl (lifted (RegistrationAgreementShared.implementation source primitive)))
        (fun point => lift (visit point))
        (PqxdhJointDhExtractFamily.realImpl hmac joint dh seed scalar ∘ₛ PqxdhJointDhExtractRoot.reduction)
        RegistrationAgreementFinish.quiet packet authenticated).run before =
      (simulateQ (RegistrationAgreementInterpreter.sourceImpl joint seed
        (RegistrationAgreementShared.implementation source primitive) visit)
        (server control .Fresh authenticated)).run before.2 := by
  rw [RegistrationRelatedRoot.stage_real source hmac correct joint dh domain secretOfSeed wiring seed scalar
    (RegistrationAgreementInterpreter.prepImpl (lifted (RegistrationAgreementShared.implementation source primitive)))
    (fun point => lift (visit point)) RegistrationAgreementFinish.quiet control packet authenticated]
  exact native_stage_project source hmac joint seed primitive visit control packet authenticated before

end BeaconcryptCore.Computational.RegistrationRootStage

/-- info: 'BeaconcryptCore.Computational.RegistrationRootStage.lift_project' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRootStage.lift_project

/-- info: 'BeaconcryptCore.Computational.RegistrationRootStage.lifted_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRootStage.lifted_program

/-- info: 'BeaconcryptCore.Computational.RegistrationRootStage.prep_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRootStage.prep_project

/-- info: 'BeaconcryptCore.Computational.RegistrationRootStage.native_prep_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRootStage.native_prep_project

/-- info: 'BeaconcryptCore.Computational.RegistrationRootStage.native_prefix_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRootStage.native_prefix_project

/-- info: 'BeaconcryptCore.Computational.RegistrationRootStage.finish_impl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRootStage.finish_impl

/-- info: 'BeaconcryptCore.Computational.RegistrationRootStage.reached_credential' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRootStage.reached_credential

/-- info: 'BeaconcryptCore.Computational.RegistrationRootStage.native_stage_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRootStage.native_stage_project

/-- info: 'BeaconcryptCore.Computational.RegistrationRootStage.stage_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationRootStage.stage_native
