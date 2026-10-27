import BeaconcryptCore.Computational.PqxdhServerAuthSendFactor
import BeaconcryptCore.Computational.PqxdhServerAuthExperiment

/-!
The Server-send factor with the authentication experiment's seal log retained.
This module connects the abstract primitive-level builder to the actual logging
tail and preserves complete state, optional output, auxiliary log and CTX cache.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete PqxdhRefinement
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhServerAuthLoggedSendFactor
open PqxdhServerRegistrationPublication (AuxSpec TailSpec Response registrationWitness)
open PqxdhSecretInputKdf PqxdhJointKdfGame
open PqxdhServerAuthSendFactor (Kernel Factor Settled StateSettled known resolve embed)
open RawCtxSelectedChain (Slot nativeKernel)

section Generic
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable {K Metadata PeerMetadata Consumed : Type}

/-- Interpret the two branches of the registration tail without dropping any effect. -/
def joined (prim : QueryImpl RawCtxSourceSend.PrimitiveSpec m) (aux : QueryImpl AuxSpec m) :
    QueryImpl TailSpec m
  | .inl query => prim query
  | .inr query => aux query

/-- The generic publication path preserves an arbitrary complete primitive interpreter. -/
theorem after_primitive (interpret : K → ConcreteRatchetKernel)
    (calls : RawCtxChainOwner.Calls K m) (prim : QueryImpl RawCtxSourceSend.PrimitiveSpec m)
    (aux : QueryImpl AuxSpec m)
    (sendRealized : ∀ entry context,
      simulateQ (prim ∘ₛ RawCtxSourceSend.adapter) (RawCtxSourceSend.send (interpret entry) context) =
        (fun result => (interpret result.1, result.2)) <$> calls.send entry context)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes)
    (kernel : K) (metadata : PeerMetadata)
    (state : PqxdhInitialGenericPublication.State K Metadata PeerMetadata Consumed) :
    simulateQ (joined prim aux)
        (PqxdhServerRegistrationPublication.afterInitialization candidate authenticated
          (interpret kernel) metadata (PqxdhInitialGenericPublication.native interpret state)) =
      Prod.map id (PqxdhInitialGenericPublication.native interpret) <$>
        PqxdhInitialGenericPublication.afterInitialization calls aux candidate authenticated kernel metadata state := by
  have lifted : (joined prim aux ∘ₛ PqxdhServerRegistrationPublication.sendLift) = prim := by
    funext query
    simp only [QueryImpl.apply_compose, PqxdhServerRegistrationPublication.sendLift,
      simulateQ_spec_query, joined]
  simp only [PqxdhServerRegistrationPublication.afterInitialization,
    PqxdhInitialGenericPublication.afterInitialization, simulateQ_bind,
    ← QueryImpl.simulateQ_compose (joined prim aux) PqxdhServerRegistrationPublication.sendLift,
    lifted, ← QueryImpl.simulateQ_compose prim RawCtxSourceSend.adapter,
    sendRealized, bind_map_left, map_bind, simulateQ_spec_query, joined]
  refine bind_congr fun ⟨advanced, encrypted⟩ => bind_congr fun _ => ?_
  cases encrypted <;> simp only [simulateQ_pure, map_pure, Prod.map_apply, id_eq,
    simulateQ_bind, simulateQ_spec_query, joined, map_bind]
  refine bind_congr fun written => ?_
  cases written <;> simp only [simulateQ_pure, map_pure, Prod.map_apply, id_eq,
    PqxdhInitialGenericPublication.publish_native]


/-- Candidate validation, allocation and initialization preserve the same primitive-level map. -/
theorem candidate_primitive (interpret : K → ConcreteRatchetKernel)
    (calls : RawCtxChainOwner.Calls K m) (prim : QueryImpl RawCtxSourceSend.PrimitiveSpec m)
    (aux : QueryImpl AuxSpec m)
    (sendRealized : ∀ entry context,
      simulateQ (prim ∘ₛ RawCtxSourceSend.adapter) (RawCtxSourceSend.send (interpret entry) context) =
        (fun result => (interpret result.1, result.2)) <$> calls.send entry context)
    (initial : RustM K) (pending : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (state : PqxdhInitialGenericPublication.State K Metadata PeerMetadata Consumed) :
    simulateQ (joined prim aux)
        (PqxdhInitialBuilderCut.candidate (interpret <$> initial) pending data metadata
          (PqxdhInitialGenericPublication.native interpret state)) =
      Functor.map (Prod.map id (PqxdhInitialGenericPublication.native interpret)) <$>
        PqxdhInitialGenericBuilder.candidate calls aux initial pending data metadata state := by
  simp only [PqxdhInitialBuilderCut.candidate, PqxdhInitialGenericBuilder.candidate,
    simulateQ_bind, simulateQ_spec_query, joined, map_bind]
  refine bind_congr fun valid => ?_
  cases valid <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true,
    ite_false, simulateQ_pure, map_pure, RawCtxMaterialInterpretation.rust_map_ok,
    Prod.map_apply, id_eq, simulateQ_bind, simulateQ_spec_query, joined, map_bind]
  refine bind_congr fun reserved => ?_
  cases reserved <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true,
    ite_false, simulateQ_pure, map_pure, RawCtxMaterialInterpretation.rust_map_ok, Prod.map_apply, id_eq]
  cases initial <;> simp only [PqxdhServerRegistrationPublication.continueRust,
    PqxdhInitialGenericBuilder.continueRust, map_pure,
    RawCtxMaterialInterpretation.rust_map_ok]
  case true.true.ok kernel =>
    by_cases empty : (data.getD PqxdhServerRegistrationPublication.registrationWitness).isEmpty = true
    all_goals simp only [empty, Bool.false_eq_true, ite_true, ite_false, simulateQ_pure, map_pure,
      RawCtxMaterialInterpretation.rust_map_ok, Prod.map_apply, id_eq]
    by_cases fits : 8 + (data.getD PqxdhServerRegistrationPublication.registrationWitness).length ≤ Usize.max
    all_goals simp only [fits, ite_true, ite_false, simulateQ_bind, simulateQ_spec_query,
      joined, map_bind, simulateQ_pure, map_pure, RawCtxMaterialInterpretation.rust_map_ok, Prod.map_apply, id_eq]
    refine bind_congr fun allocated => ?_
    cases allocated <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ite_true, ite_false, simulateQ_pure, map_pure, RawCtxMaterialInterpretation.rust_map_ok,
      Prod.map_apply, id_eq]
    cases pending.key_id_binding <;> simp only [simulateQ_pure, map_pure, simulateQ_map,
      after_primitive interpret calls prim aux sendRealized, Functor.map_map]
    all_goals rfl
  all_goals exact simulateQ_pure _ _


/-- The full preparation gates preserve the primitive-level builder equation. -/
theorem build_primitive (interpret : K → ConcreteRatchetKernel)
    (calls : RawCtxChainOwner.Calls K m) (prim : QueryImpl RawCtxSourceSend.PrimitiveSpec m)
    (aux : QueryImpl AuxSpec m)
    (sendRealized : ∀ entry context,
      simulateQ (prim ∘ₛ RawCtxSourceSend.adapter) (RawCtxSourceSend.send (interpret entry) context) =
        (fun result => (interpret result.1, result.2)) <$> calls.send entry context)
    (initial : RustM K) (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (state : PqxdhInitialGenericPublication.State K Metadata PeerMetadata Consumed) :
    simulateQ (joined prim aux)
        (PqxdhServerAuthSendFactor.cutBuild (interpret <$> initial) pending data metadata
          (PqxdhInitialGenericPublication.native interpret state)) =
      Functor.map (Prod.map id (PqxdhInitialGenericPublication.native interpret)) <$>
        PqxdhServerAuthSendFactor.genericBuild calls aux initial pending data metadata state := by
  unfold PqxdhServerAuthSendFactor.cutBuild PqxdhServerAuthSendFactor.genericBuild
  change simulateQ (joined prim aux)
    (PqxdhServerRegistrationPublication.continueRust (pqxdh.server_next_key_id state.control) _) = _
  cases next : pqxdh.server_next_key_id state.control <;>
    simp only [PqxdhServerRegistrationPublication.continueRust, PqxdhInitialGenericBuilder.continueRust,
      simulateQ_pure, map_pure]
  case ok value =>
    cases value <;> simp only [simulateQ_pure, map_pure,
      RawCtxMaterialInterpretation.rust_map_ok, Prod.map_apply, id_eq]
    simp only [PqxdhInitialGenericPublication.native, RawCtxGenericRoleStorage.nativeServer,
      Option.isSome_map]
    rename_i key
    cases prepared : pqxdh.server_prepare_commit state.control pending
        ⟨state.server.identity, state.identityKeyId⟩
        (if (state.server.peers key).isSome then .Occupied else .Available) <;>
      simp only [simulateQ_pure, map_pure]
    case ok value =>
      cases value <;> simp only [simulateQ_pure, map_pure]
      case Err _ => rfl
      case Ok candidate =>
        exact candidate_primitive interpret calls prim aux sendRealized initial candidate data metadata state
    all_goals rfl
  all_goals rfl

end Generic

section PrimitiveFactor
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable {Metadata PeerMetadata Consumed : Type}

/-- The builder only calls `send`. The arbitrary `receive` callback is retained to expose
that the equation does not inspect or replace a receive implementation. -/
noncomputable def calls (receive : Kernel → Std.U64 → RawCtxWholeOwner.OpenContext →
    m (Kernel × core.option.Option RawCtxWholeOwner.Decrypted))
    (prim : QueryImpl RawCtxSourceSend.PrimitiveSpec m)
    (source : FixedHkdfSha512NoSaltSource) (challenge : RatchetKdfResponse) :
    RawCtxChainOwner.Calls Kernel m :=
  { receive := receive
    send := fun entry context => simulateQ (PqxdhServerAuthSendFactor.primLabels prim source challenge)
      (RawCtxChainSend.execute entry context) }

/-- A primitive-level send is either exhausted or advances to a settled kernel,
with every sealing effect retained in the same monad. -/
theorem send_shape (receiveCall : Kernel → Std.U64 → RawCtxWholeOwner.OpenContext →
    m (Kernel × core.option.Option RawCtxWholeOwner.Decrypted))
    (prim : QueryImpl RawCtxSourceSend.PrimitiveSpec m)
    (source : FixedHkdfSha512NoSaltSource) (challenge : RatchetKdfResponse) (entry : Kernel)
    (receive : ∃ chain, entry.receive_chain = .known chain) (context : RawCtxSourceSend.SealContext) :
    (calls receiveCall prim source challenge).send entry context = pure (entry, none) ∨
      ∃ (advanced : Kernel) (sealing : m (Option RawCtxSourceSend.Encrypted)),
        Settled advanced ∧ (calls receiveCall prim source challenge).send entry context =
          (fun sealed => (advanced, sealed)) <$> sealing := by
  rcases PqxdhServerAuthSendFactor.send_begin entry context with
    ⟨other, begun⟩ | ⟨pending, begun, entryEq, _⟩
  · left
    simp only [calls, RawCtxChainSend.execute, begun, RawCtxChainSend.program, simulateQ_pure]
  · right
    refine ⟨(RawCtxChainSend.ready pending (RawCtxSelectedChain.step source challenge pending.request)).advanced,
      PqxdhServerAuthSendFactor.primLabels prim source challenge
        (.inr (RawCtxChainSend.ready pending (RawCtxSelectedChain.step source challenge pending.request))),
      ⟨⟨_, rfl⟩, ?_⟩, ?_⟩
    · simpa only [RawCtxChainSend.ready, entryEq] using receive
    · simp only [calls, RawCtxChainSend.execute, begun, RawCtxChainSend.program,
        simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
      simp only [PqxdhServerAuthSendFactor.primLabels, pure_bind, bind_pure_comp]

section Settle
variable (receiveCall : Kernel → Std.U64 → RawCtxWholeOwner.OpenContext →
    m (Kernel × core.option.Option RawCtxWholeOwner.Decrypted))
    (prim : QueryImpl RawCtxSourceSend.PrimitiveSpec m)
    (source : FixedHkdfSha512NoSaltSource) (aux : QueryImpl AuxSpec m)
    (challenge : RatchetKdfResponse) (chain : RatchetChain)

theorem settle_after (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes)
    (entry : Kernel) (receive : ∃ c, entry.receive_chain = .known c) (metadata : PeerMetadata)
    (state : PqxdhInitialGenericPublication.State Kernel Metadata PeerMetadata Consumed)
    (settled : StateSettled state) :
    Prod.map id (PqxdhInitialGenericPublication.native (nativeKernel chain)) <$>
      PqxdhInitialGenericPublication.afterInitialization (calls receiveCall prim source challenge) aux
        candidate authenticated entry metadata state =
    Prod.map id (PqxdhInitialGenericPublication.native resolve) <$>
      PqxdhInitialGenericPublication.afterInitialization (calls receiveCall prim source challenge) aux
        candidate authenticated entry metadata state := by
  have base := PqxdhServerAuthSendFactor.native_settled chain state settled
  simp only [PqxdhInitialGenericPublication.afterInitialization]
  rcases send_shape receiveCall prim source challenge entry receive (PqxdhServerRegistrationPublication.firstContext candidate authenticated)
    with sent | ⟨advanced, sealing, fresh, sent⟩
  · rw [sent]
    simp only [pure_bind, map_bind, map_pure, Prod.map_apply, id_eq, base]
  · rw [sent]
    simp only [bind_map_left, map_bind]
    refine bind_congr fun sealed => bind_congr fun _ => ?_
    cases sealed with
    | none => simp only [map_pure, Prod.map_apply, id_eq, base]
    | some encrypted =>
        simp only [map_bind]
        refine bind_congr fun written => ?_
        cases written with
        | none => simp only [map_pure, Prod.map_apply, id_eq, base]
        | some bytes =>
            simp only [map_pure, Prod.map_apply, id_eq,
              PqxdhServerAuthSendFactor.native_settled chain _ (PqxdhServerAuthSendFactor.publish_settled state settled candidate advanced fresh metadata)]

theorem settle_candidate (otherChain : RootOutput) (candidate : pqxdh.ServerRegistrationCandidate)
    (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhInitialGenericPublication.State Kernel Metadata PeerMetadata Consumed)
    (settled : StateSettled state) :
    Functor.map (Prod.map id (PqxdhInitialGenericPublication.native (nativeKernel chain))) <$>
      PqxdhInitialGenericBuilder.candidate (calls receiveCall prim source challenge) aux
        (RawCtxSelectedInitialConstructor.initial false otherChain) candidate data metadata state =
    Functor.map (Prod.map id (PqxdhInitialGenericPublication.native resolve)) <$>
      PqxdhInitialGenericBuilder.candidate (calls receiveCall prim source challenge) aux
        (RawCtxSelectedInitialConstructor.initial false otherChain) candidate data metadata state := by
  have base := PqxdhServerAuthSendFactor.native_settled chain state settled
  obtain ⟨kernel, built, receive⟩ := PqxdhServerAuthSendFactor.initial_ok otherChain
  simp only [PqxdhInitialGenericBuilder.candidate, built, PqxdhInitialGenericBuilder.continueRust, map_bind]
  refine bind_congr fun valid => ?_
  cases valid
  · simp only [Bool.not_false, ite_true, map_pure, RawCtxMaterialInterpretation.rust_map_ok, Prod.map_apply, id_eq, base]
  · simp only [Bool.not_true, Bool.false_eq_true, ite_false, map_bind]
    refine bind_congr fun reserved => ?_
    cases reserved
    · simp only [Bool.not_false, ite_true, map_pure, RawCtxMaterialInterpretation.rust_map_ok, Prod.map_apply, id_eq, base]
    · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
      by_cases empty : (data.getD registrationWitness).isEmpty = true
      · simp only [empty, ite_true, map_pure, RawCtxMaterialInterpretation.rust_map_ok, Prod.map_apply, id_eq, base]
      · simp only [empty, Bool.false_eq_true, ite_false]
        by_cases fits : 8 + (data.getD registrationWitness).length ≤ Usize.max
        · simp only [fits, ite_true, map_bind]
          refine bind_congr fun allocated => ?_
          cases allocated
          · simp only [Bool.not_false, ite_true, map_pure, RawCtxMaterialInterpretation.rust_map_ok, Prod.map_apply, id_eq, base]
          · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
            cases bound : candidate.key_id_binding with
            | fail error => simp only [map_pure]; rfl
            | div => simp only [map_pure]; rfl
            | ok binding =>
                simp only [Functor.map_map]
                have after := settle_after receiveCall prim source aux challenge chain candidate
                  (absBytes binding.bytes ++ data.getD registrationWitness) kernel ⟨_, receive⟩ metadata state settled
                have lifted := congrArg (fun work => RustM.ok <$> work) after
                simpa only [Functor.map_map, Function.comp_def, RawCtxMaterialInterpretation.rust_map_ok] using lifted
        · simp only [fits, ite_false, map_pure, RawCtxMaterialInterpretation.rust_map_ok, Prod.map_apply, id_eq, base]

theorem settle_generic (otherChain : RootOutput) (pending : pqxdh.PendingServerRegistration)
    (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhInitialGenericPublication.State Kernel Metadata PeerMetadata Consumed)
    (settled : StateSettled state) :
    Functor.map (Prod.map id (PqxdhInitialGenericPublication.native (nativeKernel chain))) <$>
      PqxdhServerAuthSendFactor.genericBuild (calls receiveCall prim source challenge) aux
        (RawCtxSelectedInitialConstructor.initial false otherChain) pending data metadata state =
    Functor.map (Prod.map id (PqxdhInitialGenericPublication.native resolve)) <$>
      PqxdhServerAuthSendFactor.genericBuild (calls receiveCall prim source challenge) aux
        (RawCtxSelectedInitialConstructor.initial false otherChain) pending data metadata state := by
  have base := PqxdhServerAuthSendFactor.native_settled chain state settled
  unfold PqxdhServerAuthSendFactor.genericBuild
  cases next : pqxdh.server_next_key_id state.control with
  | fail error => simp only [PqxdhInitialGenericBuilder.continueRust, map_pure]; rfl
  | div => simp only [PqxdhInitialGenericBuilder.continueRust, map_pure]; rfl
  | ok result =>
      cases result with
      | Err error =>
          simp only [PqxdhInitialGenericBuilder.continueRust, map_pure,
            RawCtxMaterialInterpretation.rust_map_ok, Prod.map_apply, id_eq, base]
      | Ok key =>
          simp only [PqxdhInitialGenericBuilder.continueRust]
          cases prepared : pqxdh.server_prepare_commit state.control pending ⟨state.server.identity, state.identityKeyId⟩
            (if (state.server.peers key).isSome then pqxdh.KeyIdAvailability.Occupied else .Available) with
          | fail error => simp only [map_pure]; rfl
          | div => simp only [map_pure]; rfl
          | ok value => cases value with
            | Err error =>
                simp only [map_pure, RawCtxMaterialInterpretation.rust_map_ok, Prod.map_apply, id_eq, base]
            | Ok value =>
                exact settle_candidate receiveCall prim source aux challenge chain otherChain value data metadata state settled

end Settle

/-- A complete build continuation with no root or hidden chain argument. Its receive
callback is arbitrary because the builder calls only send. All monadic effects remain. -/
noncomputable def factored (receiveCall : Kernel → Std.U64 → RawCtxWholeOwner.OpenContext →
    m (Kernel × core.option.Option RawCtxWholeOwner.Decrypted))
    (prim : QueryImpl RawCtxSourceSend.PrimitiveSpec m)
    (source : FixedHkdfSha512NoSaltSource) (aux : QueryImpl AuxSpec m)
    (value : Factor) (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) :
    m (RustM (Option Response × PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed)) :=
  Functor.map (Prod.map id (PqxdhInitialGenericPublication.native resolve)) <$>
    PqxdhServerAuthSendFactor.genericBuild (calls receiveCall prim source value.1) aux
      (RawCtxSelectedInitialConstructor.initial false value.2) pending data metadata (embed state)

/-- Primitive-level factorization preserves the entire result in an arbitrary lawful
monad, provided its KDF branch implements the fixed real source. -/
theorem primitive_factor (receiveCall : Kernel → Std.U64 → RawCtxWholeOwner.OpenContext →
    m (Kernel × core.option.Option RawCtxWholeOwner.Decrypted))
    (prim : QueryImpl RawCtxSourceSend.PrimitiveSpec m)
    (source : FixedHkdfSha512NoSaltSource) (aux : QueryImpl AuxSpec m)
    (kdf : ∀ request, prim (.inl request) = pure (RawCtxSourceHkdf.response source.crypto request))
    (pending : pqxdh.PendingServerRegistration) (root : RootOutput) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) :
    simulateQ (joined prim aux) (PqxdhServerRegistrationPublication.build source pending root data metadata state) =
      factored receiveCall prim source aux (PqxdhServerAuthSendFactor.factor source root)
        pending data metadata state := by
  rw [← PqxdhServerAuthSendFactor.cut_source, PqxdhServerAuthSendFactor.initial_factor,
    ← PqxdhServerAuthSendFactor.native_embed
      (RawCtxFreshChainCut.concreteChain (PqxdhServerAuthSendFactor.target source root)) state]
  rw [build_primitive _ (calls receiveCall prim source (PqxdhServerAuthSendFactor.factor source root).1)
    prim aux (fun entry context => PqxdhServerAuthSendFactor.prim_send_source prim source kdf
      (RawCtxFreshChainCut.concreteChain (PqxdhServerAuthSendFactor.target source root)) entry context)]
  rw [PqxdhServerAuthSendFactor.native_embed]
  exact settle_generic receiveCall prim source aux _ _ _ pending data metadata
    (embed state) (PqxdhServerAuthSendFactor.embed_settled state)

end PrimitiveFactor

section Logged
open PqxdhServerAuthExperiment (Setup Codec Checks tailImpl nativeTail)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader WireResponse : Type}

abbrev Logged := StateT (RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)) ProbComp

noncomputable def loggedPrim (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse) (checks : Checks) :
    QueryImpl RawCtxSourceSend.PrimitiveSpec Logged := fun query => tailImpl setup codec checks (.inl query)

noncomputable def loggedAux (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse) (checks : Checks) :
    QueryImpl AuxSpec Logged := fun query => tailImpl setup codec checks (.inr query)

/-- Splitting the actual logging tail into its primitive and auxiliary callbacks is exact. -/
theorem joined_logged (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse) (checks : Checks) :
    joined (loggedPrim setup codec checks) (loggedAux setup codec checks) = tailImpl setup codec checks := by
  funext query
  cases query <;> rfl

/-- The actual logging tail's KDF branch is the real deterministic KDF and has no state effect. -/
theorem logged_kdf (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse) (checks : Checks)
    (request : SymmetricRatchetKdfRequest) :
    loggedPrim setup codec checks (.inl request) = pure (RawCtxSourceHkdf.response setup.source.crypto request) := by
  simp only [loggedPrim, tailImpl, nativeTail, QueryImpl.apply_compose,
    PqxdhServerRegistrationPublication.nativeAdapter, RawCtxSourceSeal.nativeAdapter,
    simulateQ_spec_query, PqxdhRegistrationProtocolState.registrationImpl,
    RawCtxMixedOwner.sendLift, RawCtxMixedShared.sharedImpl, RawCtxMixedShared.sharedAdapter]
  change RawCtxSourceHkdf.kdfImpl setup.source request = _
  funext state
  exact RawCtxSourceHkdf.kdf_step setup.source request state

/-- The actual authentication experiment's complete logged Server build uses the root
only through the source 108-byte factor. This equality retains the seal log and CTX cache. -/
theorem logged_server_send_factor {Metadata PeerMetadata Consumed : Type}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse) (checks : Checks)
    (receiveCall : Kernel → Std.U64 → RawCtxWholeOwner.OpenContext →
      Logged (Kernel × core.option.Option RawCtxWholeOwner.Decrypted))
    (pending : pqxdh.PendingServerRegistration) (root : RootOutput) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) :
    simulateQ (tailImpl setup codec checks)
        (PqxdhServerRegistrationPublication.build setup.source pending root data metadata state) =
      factored receiveCall (loggedPrim setup codec checks) setup.source (loggedAux setup codec checks)
        (PqxdhServerAuthSendFactor.factor setup.source root) pending data metadata state := by
  rw [← joined_logged]
  exact primitive_factor receiveCall _ setup.source _ (logged_kdf setup codec checks)
    pending root data metadata state

/-- Evaluating both builds from the same complete log/cache state gives the same joint
result distribution, including the final log, cache and Server state. -/
theorem logged_server_send_run {Metadata PeerMetadata Consumed : Type}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse) (checks : Checks)
    (receiveCall : Kernel → Std.U64 → RawCtxWholeOwner.OpenContext →
      Logged (Kernel × core.option.Option RawCtxWholeOwner.Decrypted))
    (pending : pqxdh.PendingServerRegistration) (root : RootOutput) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed)
    (shared : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)) :
    (simulateQ (tailImpl setup codec checks)
        (PqxdhServerRegistrationPublication.build setup.source pending root data metadata state)).run shared =
      (factored receiveCall (loggedPrim setup codec checks) setup.source (loggedAux setup codec checks)
        (PqxdhServerAuthSendFactor.factor setup.source root) pending data metadata state).run shared := by
  rw [logged_server_send_factor setup codec checks receiveCall]

end Logged

end BeaconcryptCore.Computational.PqxdhServerAuthLoggedSendFactor

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthLoggedSendFactor.after_primitive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthLoggedSendFactor.after_primitive

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthLoggedSendFactor.candidate_primitive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthLoggedSendFactor.candidate_primitive

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthLoggedSendFactor.build_primitive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthLoggedSendFactor.build_primitive

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthLoggedSendFactor.send_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthLoggedSendFactor.send_shape

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthLoggedSendFactor.settle_after' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthLoggedSendFactor.settle_after

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthLoggedSendFactor.settle_candidate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthLoggedSendFactor.settle_candidate

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthLoggedSendFactor.settle_generic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthLoggedSendFactor.settle_generic

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthLoggedSendFactor.primitive_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthLoggedSendFactor.primitive_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthLoggedSendFactor.joined_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthLoggedSendFactor.joined_logged

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthLoggedSendFactor.logged_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthLoggedSendFactor.logged_kdf

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthLoggedSendFactor.logged_server_send_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthLoggedSendFactor.logged_server_send_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthLoggedSendFactor.logged_server_send_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthLoggedSendFactor.logged_server_send_run
