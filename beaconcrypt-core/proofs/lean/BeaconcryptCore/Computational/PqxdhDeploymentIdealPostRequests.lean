-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSteps

/-!
# Item 2's per-request steps against the middle execution: HMAC, field reads, creates and bundles (CE-11b, unit U6, third part)

Item 2's side of the post-challenge simulation needs `PqxdhDeploymentIdealPostSteps.StepAt` (the per-request obligation of `PqxdhDeploymentIdealPostSim.sim_option` at item 2's view `encodeMid` of the middle state) for every request the compiled program can send. `PqxdhDeploymentIdealPostSteps` proved it for the coins, the BLAKE2b request and the Server kernel reveal. This module adds the public HMAC, the local field reads, the create and the bundle, together with the router facts that every private-service request needs.

- `step_hmac`: the skeleton's HMAC step (a direct table read on the zero-key 192-byte slice, the real function elsewhere) against the source's native HMAC through the ROM family (`PqxdhExtractRomFamily.rom_forward`, `rom_public_oracle`); the family history and the adversary touch are erased by item 2's view.
- `step_read`: a field read that item 2's client answers from the encoded owner without a private-service call (prekey, one-time prekey, established kernel; `LocalField`) against the source's current-field read (`localValue_encode`). This covers the kernel read `.inr 4`, the only field read that `sim_option`'s allowed class admits.
- Router: away from the decapsulation of the selected challenge ciphertext (`challengeDecaps`), the post-challenge router holding any candidate, under the CCA evaluation, is the stopped source router (`postDecapsulation_fresh`, `kemStep_fresh`, `jointStep_fresh`, `jointProgram_fresh`: item 2's `PqxdhDynamicKemPost.decapsulation_source`, `step_pre`, `PqxdhDynamicKemJointRouter.post_step` and `post_program` without their agreement premise, which only that decapsulation uses). `fresh_of_noDecaps` discharges the side condition for programs without decapsulation.
- Service layers: a private-service request of the skeleton (`poolUp`) passes through item 2's service layers as a request of the post-challenge router `postRouter` under the CCA evaluation, keeping the table state (`service_pool`, `service_poolProgram`); with the stopped router at the challenger's pool (`PqxdhDeploymentIdealPoolSource.stopped_program`), a private-service program with creations within the pool, no KEM reveal and no decapsulation of the selected challenge ciphertext runs through item 2's erased service layers as under the reserved services (`lowerE_pool`).
- `step_create`: item 2's constructor client through the router reads the challenger's pool at the router's creation count (`PqxdhDeploymentIdealPoolSource.client_reserved`), which is the middle's pool create (`createSourcePool`) when the KEM pool is a prefix of the challenger's pool with one key pair per owner and room for one more creation (the costly class of `sim_option` with the router's remaining reservation as the room).
- `step_bundle`: an owner's bundle program creates no KEM key and decapsulates nothing, so the router runs it as the actual services (`PqxdhDeploymentIdealPoolSource.reserved_noCreate`), which is the annotated source's bundle trace under item 2's ownership invariant (`PqxdhRegistrationJointBundleCompiler.bundle_source`).

These are program equalities. They charge nothing and make no security claim.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhKemIndCca (MlKem768PublicKey MlKem768Ciphertext)
open PqxdhRegistrationJointKemPostSkeleton (Enc TSpec SkelSpec SkelState fwd fwdOption coinLift clean)
open PqxdhRegistrationJointKemEntryFactor (Output factoredServices)
open PqxdhDeploymentIdealPostSim (SlotState ServiceState tableLayer serviceLayer upperLayer eraseService)
open PqxdhDeploymentIdealPostSource (Mid sourceMid)
open PqxdhDeploymentIdealPostItem (cleanSkel cleanUpper)
open PqxdhDeploymentIdealPostSteps (encodeMid upperE lowerE StepAt)
open PqxdhDeploymentIdealParams (Target Params)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

section Hmac
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- The upper layers on the public HMAC: the skeleton's HMAC step on its state. -/
theorem upperLayer_hmac (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes)
    (state : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry × SkelState KemSK Output) :
    (upperLayer setup codec checks created.server.server.metadata.identityIndex created.publicIdentity t.kem.val
        p.challenge (factoredServices setup codec checks) (.inl (.inr (.hmac key message)))).run state =
      (fun result => (result.1, (state.1, result.2))) <$> simulateQ (fwd (T := TSpec Output) (coinLift (KemSK := KemSK)))
        ((PqxdhRegistrationJointKemPostSkeleton.hmacStep (KemSK := KemSK) (V := Output) setup key message).run
          state.2) := by
  simp only [upperLayer, QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run_mk,
    PqxdhRegistrationJointKemPostSkeleton.groupedClient, PqxdhRegistrationJointRevealSchedule.client,
    PqxdhRegistrationJointServiceSchedule.handler]
  simp only [PqxdhRegistrationJointKemPostSkeleton.liftGrouped, StateT.run, StateT.lift, bind_pure_comp,
    simulateQ_map, simulateQ_spec_query, PqxdhRegistrationJointKemPostSkeleton.groupedLift,
    PqxdhRegistrationJointKemPostSkeleton.skelImpl]
  change (fun x => (x.1.1, x.1.2, x.2)) <$> StateT.run ((fun a => (a, state.1)) <$>
    PqxdhRegistrationJointKemPostSkeleton.liftT (V := Output)
      (PqxdhRegistrationJointKemPostSkeleton.hmacStep setup key message)) state.2 = _
  rw [StateT.run_map, Functor.map_map]
  rfl

/-- The public HMAC. -/
theorem step_hmac (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes) (m : Mid KemSK) :
    StepAt setup codec route checks t p created (.inl (.inr (.hmac key message))) m := by
  unfold StepAt
  rw [PqxdhDeploymentIdealPostSteps.upperE_run setup codec checks t p created _ _
      (PqxdhDeploymentIdealPostSteps.encodeMid_clean setup m), upperLayer_hmac, Functor.map_map,
    simulateQ_map, OptionT.run_map, StateT.run_map,
    PqxdhDeploymentIdealPostSteps.lowerE_native setup t p _ _ (PqxdhDeploymentIdealPostSteps.encodeMid_erased setup m)]
  change _ = _ <$> ((fun r => (r.1, { m with joint := r.2 })) <$>
    ((fun r => (r.1, { m.joint with shared := r.2 })) <$>
      PqxdhServerAuthNative.nativeHmac (KemSK := KemSK) setup created.seed PqxdhRegistrationSchedule.observationScalar
        key message m.joint.shared))
  by_cases slice : key = PqxdhSecretInputKdf.zeroSalt ∧ message.length = 192
  · have left : PqxdhRegistrationJointKemPostSkeleton.hmacStep (KemSK := KemSK) (V := Output) setup key message =
        PqxdhRegistrationJointKemPostSkeleton.tableRead message := by
      simp only [PqxdhRegistrationJointKemPostSkeleton.hmacStep, slice, and_self, ite_true]
    have read : ∀ (s : SkelState KemSK Output) (c : PqxdhSecretInputKdf.HmacOracle.QueryCache × SlotState),
        (simulateQ tableLayer (StateT.run (PqxdhRegistrationJointKemPostSkeleton.tableRead (KemSK := KemSK)
          (V := Output) message) s)).run c =
        (fun result => ((result.1, s), (result.2, c.2))) <$>
          (PqxdhSecretInputKdf.HmacOracle.randomOracle message).run c.1 := by
      intro s c
      change (simulateQ tableLayer ((fun reply => (reply, s)) <$>
        ((SkelSpec Output).query (.inr (.inr message)) : OracleComp (SkelSpec Output) _))).run c = _
      rw [simulateQ_map, simulateQ_spec_query, StateT.run_map, PqxdhDeploymentIdealPostSteps.tableLayer_direct,
        Functor.map_map]
    have right : ∀ st : PqxdhServerAuthNative.NativeState KemSK,
        PqxdhServerAuthNative.nativeHmac (KemSK := KemSK) setup created.seed PqxdhRegistrationSchedule.observationScalar
          key message st =
        (fun result => (result.1, ((⟨st.1.history ++ [.publicHmac key message result.1], result.2⟩ :
            PqxdhJointDhExtractFamily.State),
          { st.2 with ghost := { st.2.ghost with touches := st.2.ghost.touches ++ [.adversary message] } }))) <$>
          (PqxdhSecretInputKdf.HmacOracle.randomOracle message).run st.1.cache := by
      intro st
      change StateT.run (PqxdhServerAuthNative.nativeHmac (KemSK := KemSK) setup created.seed
        PqxdhRegistrationSchedule.observationScalar key message) st = _
      simp only [PqxdhServerAuthNative.nativeHmac, eq_true slice, ↓reduceIte, StateT.run_bind]
      rw [show StateT.run (PqxdhServerAuthNative.nativeTouch (KemSK := KemSK) (.adversary message)) st =
        pure ((), (st.1, { st.2 with ghost := { st.2.ghost with touches := st.2.ghost.touches ++ [.adversary message] } }))
        from rfl, pure_bind]
      change (fun result => (result.1, (result.2, _))) <$> ((PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh
        created.seed PqxdhRegistrationSchedule.observationScalar ∘ₛ PqxdhJointDhExtractRoot.reduction)
          (.inr (.publicHmac key message))).run st.1 = _
      rw [(PqxdhExtractRomFamily.rom_forward setup.hmac setup.joint setup.dh created.seed
        PqxdhRegistrationSchedule.observationScalar).2.2 key message,
        PqxdhExtractRomFamily.rom_public_oracle _ _ _ _ _ key message slice, Functor.map_map]
    rw [left, read, right]
    simp only [Functor.map_map]
    rfl
  · have left : PqxdhRegistrationJointKemPostSkeleton.hmacStep (KemSK := KemSK) (V := Output) setup key message =
        pure (setup.hmac.eval key message) := by
      simp only [PqxdhRegistrationJointKemPostSkeleton.hmacStep, eq_false slice, ↓reduceIte]
    have right : ∀ st : PqxdhServerAuthNative.NativeState KemSK,
        PqxdhServerAuthNative.nativeHmac (KemSK := KemSK) setup created.seed PqxdhRegistrationSchedule.observationScalar
          key message st =
        pure (setup.hmac.eval key message, ({ st.1 with history := st.1.history ++
          [.publicHmac key message (setup.hmac.eval key message)] }, st.2)) := by
      intro st
      change StateT.run (PqxdhServerAuthNative.nativeHmac (KemSK := KemSK) setup created.seed
        PqxdhRegistrationSchedule.observationScalar key message) st = _
      simp only [PqxdhServerAuthNative.nativeHmac, eq_false slice, ↓reduceIte]
      change (fun result => (result.1, (result.2, _))) <$> ((PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh
        created.seed PqxdhRegistrationSchedule.observationScalar ∘ₛ PqxdhJointDhExtractRoot.reduction)
          (.inr (.publicHmac key message))).run st.1 = _
      rw [(PqxdhExtractRomFamily.rom_forward setup.hmac setup.joint setup.dh created.seed
        PqxdhRegistrationSchedule.observationScalar).2.2 key message]
      change (fun result => (result.1, (result.2, _))) <$> PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh
        created.seed PqxdhRegistrationSchedule.observationScalar (.inr (.publicHmac key message)) st.1 = _
      simp only [PqxdhExtractRomFamily.romImpl, eq_false slice, ↓reduceIte, map_pure]
    rw [left, right, StateT.run_pure, simulateQ_pure, StateT.run_pure]
    simp only [map_pure]
    rfl

end Hmac

/-! ### Local field reads -/

section Read
open PqxdhRegistrationJointLiveRead (Field localValue)
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- A field that is read from the owner's current phase without a private-service call: the prekey, the one-time prekey and the established kernel. -/
def LocalField : Field → Prop
  | .prekey | .oneTime | .kernel => True
  | _ => False

/-- The encoding of an owner keeps its local fields. -/
theorem localValue_encode (field : Field) (entry : PqxdhRegistrationJointOwnership.Entry KemSK) :
    (localValue field (PqxdhRegistrationJointGeneratedFinish.encodeEntry setup entry).2.2 : Option (PqxdhRegistrationJointLiveRead.Value KemSK)) =
      localValue field entry.owner := by
  rcases entry with ⟨identityIndex, kemIndex, ⟨⟨identity, keyId, server, phase⟩, attempts⟩⟩
  cases field <;> cases phase <;> rfl

/-- A local field read. -/
theorem step_read (address : ℕ) (field : Field) (direct : LocalField field) (m : Mid KemSK) :
    StepAt setup codec route checks t p created (.inr (address, field)) m := by
  have upper : ∀ state : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry × SkelState KemSK Output,
      (upperLayer setup codec checks created.server.server.metadata.identityIndex created.publicIdentity t.kem.val
        p.challenge (factoredServices setup codec checks) (.inr (address, field))).run state =
      pure ((state.1[address]?).bind fun entry => localValue field entry.2.2, state) := by
    intro state
    rcases state with ⟨owners, skel⟩
    simp only [upperLayer, QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run_mk,
      PqxdhRegistrationJointKemPostSkeleton.groupedClient, PqxdhRegistrationJointRevealSchedule.client]
    change (fun x => (x.1.1, x.1.2, x.2)) <$> StateT.run (simulateQ _
      (simulateQ PqxdhRegistrationJointKemPostSkeleton.groupedLift
        (PqxdhRegistrationJointLiveRead.clientStep (Response := Response) (address, field) owners))) skel = _
    rcases found : owners[address]? with _ | entry
    · simp [PqxdhRegistrationJointLiveRead.clientStep, found]
    · rcases field <;> simp_all [LocalField, PqxdhRegistrationJointLiveRead.clientStep,
        PqxdhRegistrationJointLiveRead.entryClient]
  unfold StepAt
  rw [PqxdhDeploymentIdealPostSteps.upperE_run setup codec checks t p created _ _
      (PqxdhDeploymentIdealPostSteps.encodeMid_clean setup m), upper, map_pure, simulateQ_pure]
  change _ = _ <$> ((fun r => (r.1, { m with joint := r.2 })) <$>
    (pure (PqxdhRegistrationJointLiveRead.sourceStep (address, field) m.joint) : ProbComp _))
  rw [map_pure, map_pure, OptionT.run_pure, StateT.run_pure]
  simp only [PqxdhRegistrationJointLiveRead.sourceStep]
  have encoded : (encodeMid setup m).1.1[address]? =
      (m.joint.owners[address]?).map (PqxdhRegistrationJointGeneratedFinish.encodeEntry setup) := by
    simp [encodeMid, PqxdhRegistrationJointGeneratedFinish.encodeState, List.getElem?_map]
  rw [encoded]
  rcases found : m.joint.owners[address]? with _ | entry
  · rfl
  · simp only [Option.map_some, Option.bind_some, localValue_encode]
    rcases field <;> simp_all [LocalField, PqxdhRegistrationJointLiveRead.entrySource]
    all_goals rfl

end Read
/-! ### The post-challenge router away from the selected challenge ciphertext -/

section Router
open PqxdhKemIndCca PqxdhPrivateKemSource PqxdhDynamicKemRouter

/-- Whether a private-service request decapsulates the challenge ciphertext at the selected creation index. -/
def challengeDecaps (selected : ℕ) (challenge : MlKem768Ciphertext) : (PqxdhLiveKemBirth.Spec KemSK).Domain → Bool
  | .inr (.inr (.decapsulate index ciphertext)) => decide (index = selected ∧ ciphertext = challenge)
  | _ => false

variable (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))

set_option backward.isDefEq.respectTransparency false in
/-- Away from the selected challenge ciphertext, the post-challenge decapsulation under the CCA evaluation is the prechallenge decapsulation under the local evaluation, for any candidate (item 2's `PqxdhDynamicKemPost.decapsulation_source` without its agreement premise). -/
theorem postDecapsulation_fresh (secret : KemSK) (selected : ℕ) (challenge : MlKem768Ciphertext)
    (candidate : MlKemSharedSecret) (keys : Reservation KemSK) (index : ℕ) (ciphertext : MlKem768Ciphertext)
    (fresh : ¬(index = selected ∧ ciphertext = challenge)) :
    PqxdhDynamicKemPost.evaluate baseImpl kem secret challenge
        (postDecapsulation kem selected challenge candidate keys index ciphertext) =
      evalKem baseImpl kem secret (PqxdhLiveKemRouting.pre kem selected keys (default, index) ciphertext) := by
  classical
  cases found : keys index with
  | none => simp [postDecapsulation, PqxdhLiveKemRouting.pre, found, PqxdhDynamicKemPost.evaluate, evalKem]
  | some pair =>
      by_cases owner : index = selected
      · subst index
        have same : ciphertext ≠ challenge := fun same => fresh ⟨rfl, same⟩
        simp [postDecapsulation, PqxdhLiveKemRouting.pre, found, same, PqxdhDynamicKemPost.evaluate, evalKem,
          PqxdhStatefulPhase1EufCma.localKemPreChallengeImpl, KEMScheme.IND_CCA_preChallengeImpl,
          KEMScheme.IND_CCA_postChallengeImpl, QueryImpl.add]
      · cases key : pair.2 <;>
          simp only [postDecapsulation, PqxdhLiveKemRouting.pre, found, ite_eq_right owner, key]
        · rfl
        · rw [PqxdhDynamicKemPost.ambient, evalKem_ambient]

set_option backward.isDefEq.respectTransparency false in
/-- Away from the selected challenge ciphertext, a post-challenge KEM router step under the CCA evaluation is the prechallenge step under the local evaluation, for any candidate (item 2's `PqxdhDynamicKemPost.step_pre` without its agreement premise). -/
theorem kemStep_fresh (secret : KemSK) (selected : ℕ) (challenge : MlKem768Ciphertext)
    (candidate : MlKemSharedSecret) (reservation : Reservation KemSK) (query : PqxdhLiveKemBirth.Query)
    (fresh : ∀ index ciphertext, query = .decapsulate index ciphertext → ¬(index = selected ∧ ciphertext = challenge))
    (state : State KemSK) :
    PqxdhDynamicKemPost.evaluate baseImpl kem secret challenge
        (((post kem selected reservation challenge candidate query).run).run state) =
      evalKem baseImpl kem secret (((pre kem selected reservation query).run).run state) := by
  cases query with
  | create =>
      cases found : reservation state.created <;>
        simp [post, pre, router, OptionT.run_mk, StateT.run, found, PqxdhDynamicKemPost.evaluate, evalKem]
  | reveal index =>
      cases found : lookup reservation state index with
      | none => simp [post, pre, router, OptionT.run_mk, StateT.run, found, PqxdhDynamicKemPost.evaluate, evalKem]
      | some pair =>
          by_cases chosen : index = selected
          · subst index
            simp [post, pre, router, OptionT.run_mk, StateT.run, found, PqxdhDynamicKemPost.evaluate, evalKem]
          · simp [post, pre, router, OptionT.run_mk, StateT.run, found, chosen, PqxdhDynamicKemPost.evaluate, evalKem]
  | decapsulate index ciphertext =>
      simp only [post, pre, router, OptionT.run_mk, StateT.run, bind_pure_comp]
      change PqxdhDynamicKemPost.evaluate baseImpl kem secret challenge
        ((fun reply => (some reply, record (.decapsulate index ciphertext) reply state)) <$>
          postDecapsulation kem selected challenge candidate (lookup reservation state) index ciphertext) =
        evalKem baseImpl kem secret
          ((fun reply => (some reply, record (.decapsulate index ciphertext) reply state)) <$>
            PqxdhLiveKemRouting.pre kem selected (lookup reservation state) (default, index) ciphertext)
      simpa only [PqxdhDynamicKemPost.evaluate, evalKem, simulateQ_map] using
        congrArg (Functor.map (fun reply => (some reply, record (.decapsulate index ciphertext) reply state)))
          (postDecapsulation_fresh baseImpl kem secret selected challenge candidate (lookup reservation state) index
            ciphertext (fresh index ciphertext rfl))

set_option backward.isDefEq.respectTransparency false in
/-- Away from the selected challenge ciphertext, a post-challenge joint router step under the CCA evaluation is the stopped source router's step, for any candidate (item 2's `PqxdhDynamicKemJointRouter.post_step` without its agreement premise). -/
theorem jointStep_fresh (primitives : PqxdhJointIdentity.Primitives) (selected : ℕ)
    (pairs : List (MlKem768PublicKey × KemSK)) (target : MlKem768PublicKey) (secret : KemSK)
    (present : pairs[selected]? = some (target, secret)) (challenge : MlKem768Ciphertext)
    (candidate : MlKemSharedSecret) (query : (PqxdhLiveKemBirth.Spec KemSK).Domain)
    (fresh : challengeDecaps selected challenge query = false) (state : PqxdhDynamicKemJointSource.State KemSK) :
    PqxdhDynamicKemPost.evaluate baseImpl kem secret challenge
      (((PqxdhDynamicKemJointRouter.post primitives kem selected (redact selected pairs) challenge candidate
        query).run).run state) =
        (((PqxdhDynamicKemJointRouter.stopped baseImpl primitives kem selected pairs query).run).run state) := by
  rcases query with joint | (coin | query)
  · simp only [PqxdhDynamicKemJointRouter.post, PqxdhDynamicKemJointRouter.stopped, PqxdhDynamicKemJointRouter.combine,
      OptionT.run_mk, StateT.run, PqxdhDynamicKemPost.evaluate, simulateQ_map]
    exact congrArg (fun work => (fun result => (some result.1, (result.2, state.2))) <$> work)
      (PqxdhDynamicKemJointRouter.post_coins baseImpl kem secret challenge
        ((PqxdhDynamicIdentityPool.lazyImpl primitives joint).run state.1))
  · simp only [PqxdhDynamicKemJointRouter.post, PqxdhDynamicKemJointRouter.stopped, PqxdhDynamicKemJointRouter.combine,
      OptionT.run_mk, StateT.run, PqxdhDynamicKemPost.evaluate, simulateQ_map]
    exact congrArg (fun work => (fun result => (some result, state)) <$> work)
      (PqxdhDynamicKemJointRouter.post_coins baseImpl kem secret challenge (unifSpec.query coin : ProbComp _))
  · simp only [PqxdhDynamicKemJointRouter.post, PqxdhDynamicKemJointRouter.stopped, PqxdhDynamicKemJointRouter.combine,
      OptionT.run_mk, StateT.run, PqxdhDynamicKemPost.evaluate, simulateQ_map]
    exact congrArg (fun work => (fun result => (result.1, (state.1, result.2))) <$> work)
      ((kemStep_fresh baseImpl kem secret selected challenge candidate (redact selected pairs) query
        (fun index ciphertext equal => by subst equal; simpa [challengeDecaps] using fresh) state.2).trans
        (PqxdhDynamicKemRouter.step_source baseImpl kem selected pairs target secret present query state.2))

set_option backward.isDefEq.respectTransparency false in
/-- A private-service program without a decapsulation of the selected challenge ciphertext, run by the post-challenge joint router under the CCA evaluation, is its run by the stopped source router, for any candidate. -/
theorem jointProgram_fresh {α : Type} (primitives : PqxdhJointIdentity.Primitives) (selected : ℕ)
    (pairs : List (MlKem768PublicKey × KemSK)) (target : MlKem768PublicKey) (secret : KemSK)
    (present : pairs[selected]? = some (target, secret)) (challenge : MlKem768Ciphertext)
    (candidate : MlKemSharedSecret) (client : OracleComp (PqxdhLiveKemBirth.Spec KemSK) α)
    (fresh : client.IsQueryBoundP (fun query => challengeDecaps (KemSK := KemSK) selected challenge query = true) 0)
    (state : PqxdhDynamicKemJointSource.State KemSK) :
    PqxdhDynamicKemPost.evaluate baseImpl kem secret challenge
      (((simulateQ (PqxdhDynamicKemJointRouter.post primitives kem selected (redact selected pairs) challenge candidate)
        client).run).run state) =
        (((simulateQ (PqxdhDynamicKemJointRouter.stopped baseImpl primitives kem selected pairs) client).run).run
          state) := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at fresh
    have first : challengeDecaps selected challenge query = false := by
      rcases fresh.1 with absent | impossible
      · simpa using absent
      · exact absurd impossible (Nat.lt_irrefl 0)
    simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind]
    change PqxdhDynamicKemPost.evaluate baseImpl kem secret challenge
      ((((PqxdhDynamicKemJointRouter.post primitives kem selected (redact selected pairs) challenge candidate
        query).run).run state) >>= fun result =>
        (result.1.elim (pure none) (fun value =>
          (simulateQ (PqxdhDynamicKemJointRouter.post primitives kem selected (redact selected pairs) challenge
            candidate) (next value)).run)).run result.2) = _
    unfold PqxdhDynamicKemPost.evaluate
    simp only [simulateQ_bind]
    rw [show simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl)
      (simulateQ (kem.IND_CCA_postChallengeImpl secret challenge)
        (((PqxdhDynamicKemJointRouter.post primitives kem selected (redact selected pairs) challenge candidate
          query).run).run state)) =
          (((PqxdhDynamicKemJointRouter.stopped baseImpl primitives kem selected pairs query).run).run state)
      from jointStep_fresh baseImpl kem primitives selected pairs target secret present challenge candidate query
        first state]
    apply bind_congr
    rintro ⟨none | reply, after⟩
    · rfl
    · exact ih reply (by simpa [first] using fresh.2 reply) after

/-- A decapsulation of the selected challenge ciphertext is a request of the decapsulation class. -/
theorem challengeDecaps_class (selected : ℕ) (challenge : MlKem768Ciphertext) (query : (PqxdhLiveKemBirth.Spec KemSK).Domain)
    (hit : challengeDecaps selected challenge query = true) :
    PqxdhRegistrationJointServiceCosts.poolClass (KemSK := KemSK) query = .decapsulate := by
  rcases query with (coin | request) | (coin | request)
  · simp [challengeDecaps] at hit
  · simp [challengeDecaps] at hit
  · simp [challengeDecaps] at hit
  · cases request <;> simp_all [challengeDecaps, PqxdhRegistrationJointServiceCosts.poolClass]

/-- A private-service program without decapsulation never decapsulates the selected challenge ciphertext. -/
theorem fresh_of_noDecaps {α : Type} (selected : ℕ) (challenge : MlKem768Ciphertext)
    (client : OracleComp (PqxdhLiveKemBirth.Spec KemSK) α)
    (none : client.IsQueryBoundP
      (fun query => PqxdhRegistrationJointServiceCosts.poolClass (KemSK := KemSK) query = .decapsulate) 0) :
    client.IsQueryBoundP (fun query => challengeDecaps (KemSK := KemSK) selected challenge query = true) 0 :=
  none.of_imp fun query hit => challengeDecaps_class selected challenge query hit

end Router

/-! ### Private-service programs through the service layers -/

section Service
variable (setup : Setup baseSpec KemSK) {count : ℕ} (selected : Fin (count + 1))
  (chosen : MlKem768PublicKey × KemSK) (others : Fin count → MlKem768PublicKey × KemSK)
  (challenge : MlKem768Ciphertext)

/-- The post-challenge router of item 2's service layers. -/
noncomputable abbrev postRouter :=
  PqxdhDynamicKemJointRouter.post setup.joint setup.kem selected.val
    (PqxdhDynamicKemRouter.selectedReservation selected chosen.1 others) challenge
      PqxdhRegistrationJointBeaconOpaqueFinishRouter.placeholder

/-- A private-service request sent by the skeleton to its exposed encapsulation interface. -/
def poolUp : QueryImpl (PqxdhLiveKemBirth.Spec KemSK) (OracleComp (Enc KemSK + TSpec Output)) :=
  fun query => (Enc KemSK + TSpec Output).query (.inl (.inl query))

/-- A private-service request passes through the actual encapsulator to the post-challenge router, whose KEM requests the CCA evaluation answers; the table state is kept. -/
theorem service_pool (query : (PqxdhLiveKemBirth.Spec KemSK).Domain) (state : ServiceState KemSK) :
    ((serviceLayer setup selected chosen others challenge (.inl (.inl query))).run).run state =
      (fun result => (result.1, (result.2, state.2))) <$>
        PqxdhDynamicKemPost.evaluate setup.baseImpl setup.kem chosen.2 challenge
          (((postRouter setup selected chosen others challenge query).run).run state.1) := by
  simp only [serviceLayer, PqxdhDeploymentIdealPostSim.optionLower, OptionT.run_mk, StateT.run_mk,
    QueryImpl.apply_compose, PqxdhRegistrationJointKemPostSkeleton.fwd_inl]
  have actual : PqxdhRegistrationJointKemEncapsulation.actual setup (.inl query) =
      ((PqxdhLiveKemBirth.Spec KemSK).query query : OracleComp (PqxdhLiveKemBirth.Spec KemSK) _) := rfl
  rw [actual]
  unfold PqxdhRegistrationJointKemPostSkeleton.fwdOption
  rw [QueryImpl.simulateQ_add_liftComp_left, simulateQ_spec_query]
  simp only [OptionT.run_mk, StateT.run_mk]
  rw [QueryImpl.simulateQ_compose, PqxdhDeploymentIdealPostItem.fwd_liftComp,
    ← PqxdhRegistrationJointKemPostSkeleton.evaluate_layer, PqxdhDeploymentIdealPostItem.tableLayer_lift,
    Functor.map_map]
  rfl

/-- A private-service program sent by the skeleton passes through the service layers as its run by the post-challenge router under the CCA evaluation; the table state is kept. -/
theorem service_poolProgram {α : Type} (client : OracleComp (PqxdhLiveKemBirth.Spec KemSK) α)
    (state : ServiceState KemSK) :
    ((simulateQ (serviceLayer setup selected chosen others challenge) (simulateQ poolUp client)).run).run state =
      (fun result => (result.1, (result.2, state.2))) <$>
        PqxdhDynamicKemPost.evaluate setup.baseImpl setup.kem chosen.2 challenge
          (((simulateQ (postRouter setup selected chosen others challenge) client).run).run state.1) := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, PqxdhDynamicKemPost.evaluate, OptionT.run_pure, StateT.run_pure]
      rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind]
      have up : simulateQ (serviceLayer setup selected chosen others challenge) (poolUp query) =
          serviceLayer setup selected chosen others challenge (.inl (.inl query)) := simulateQ_spec_query _ _
      rw [up, service_pool, bind_map_left]
      simp only [PqxdhRegistrationJointKemPostSkeleton.evaluate_layer] at ih ⊢
      rw [simulateQ_bind, map_bind]
      refine bind_congr fun result => ?_
      rcases result with ⟨_ | reply, after⟩
      · simp only [Option.elim_none, StateT.run_pure, simulateQ_pure, map_pure]
      · exact ih reply (after, state.2)

end Service

section Lowered
variable (setup : Setup baseSpec KemSK) {count : ℕ} (t : Target count) (p : Params KemSK count)

/-- A private-service program sent by the skeleton, with at most `qCreate` KEM creations within the challenger's pool, no KEM reveal and no decapsulation of the selected challenge ciphertext, runs through item 2's erased service layers from the erased router state of a prefix pool as its run under the reserved services, without stopping, with the erased router state of the final pool and the table state kept. -/
theorem lowerE_pool {α : Type} (client : OracleComp (PqxdhLiveKemBirth.Spec KemSK) α) (qCreate : ℕ)
    (bounded : client.IsQueryBoundP (PqxdhLiveKemReservation.IsCreate (KemSK := KemSK)) qCreate)
    (noReveal : client.IsQueryBoundP
      (fun query => PqxdhRegistrationJointServiceCosts.poolClass (KemSK := KemSK) query = .other) 0)
    (fresh : client.IsQueryBoundP (fun query => challengeDecaps (KemSK := KemSK) t.kem.val p.challenge query = true) 0)
    (joint : PqxdhDynamicIdentityPool.SourceState) (pool : PqxdhLiveKemBirth.Pool KemSK)
    (prefixed : PqxdhDeploymentIdealPoolSource.PoolPrefix (p.pool t) pool)
    (room : pool.keys.length + qCreate ≤ (p.pool t).length)
    (tables : PqxdhSecretInputKdf.HmacOracle.QueryCache × SlotState) :
    ((simulateQ (lowerE setup t p) (simulateQ poolUp client)).run).run
        (PqxdhRegistrationJointKemObserverFree.eraseJoint (joint, PqxdhDeploymentIdealPoolSource.routerOf pool), tables) =
      (fun result => (some result.1, (PqxdhRegistrationJointKemObserverFree.eraseJoint
          (result.2.1, PqxdhDeploymentIdealPoolSource.routerOf result.2.2), tables))) <$>
        (simulateQ (PqxdhDeploymentIdealPoolSource.reservedAt setup (p.pool t)) client).run (joint, pool) := by
  have run := PqxdhRegistrationJointKemObserverFree.run_eraseOption eraseService
    (fun state => by simp only [eraseService, Prod.map, PqxdhRegistrationJointKemObserverFree.eraseJoint_idem, id_eq])
    (serviceLayer setup t.kem p.chosen p.others p.challenge)
    (PqxdhDeploymentIdealPostSim.serviceLayer_neverRead setup t.kem p.chosen p.others p.challenge)
    (simulateQ poolUp client) ((joint, PqxdhDeploymentIdealPoolSource.routerOf pool), tables)
  change ((simulateQ (lowerE setup t p) (simulateQ poolUp client)).run).run
    (eraseService ((joint, PqxdhDeploymentIdealPoolSource.routerOf pool), tables)) = _
  rw [← run, service_poolProgram]
  have reservation : PqxdhDynamicKemRouter.selectedReservation t.kem p.chosen.1 p.others =
      PqxdhDynamicKemRouter.redact t.kem.val (p.pool t) := by
    rw [PqxdhDeploymentIdealParams.pool_eq, PqxdhDynamicKemRouter.selected_reservation]
  have present : (p.pool t)[t.kem.val]? = some (p.chosen.1, p.chosen.2) := PqxdhDeploymentIdealParams.pool_kem t p
  simp only [postRouter, reservation]
  rw [jointProgram_fresh setup.baseImpl setup.kem setup.joint t.kem.val (p.pool t) p.chosen.1 p.chosen.2 present
      p.challenge _ client fresh,
    PqxdhDeploymentIdealPoolSource.stopped_program setup t.kem.val (p.pool t) client qCreate bounded noReveal joint pool
      prefixed room]
  simp only [Functor.map_map]
  rfl

end Lowered

/-! ### The create request -/

section Create
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- A private-service program of the source client, through the grouped client and the skeleton, is sent to the exposed encapsulation interface unchanged, with the skeleton state kept. -/
theorem skel_pool {α : Type} (client : OracleComp (PqxdhLiveKemBirth.Spec KemSK) α) (state : SkelState KemSK Output) :
    (simulateQ (PqxdhRegistrationJointKemPostSkeleton.skelImpl setup codec checks created.server.server.metadata.identityIndex
        created.publicIdentity (factoredServices setup codec checks))
      (simulateQ (PqxdhRegistrationJointKemPostSkeleton.groupedLift (Response := Response))
        (simulateQ PqxdhRegistrationJointServiceSchedule.poolLift client))).run state =
      (fun value => (value, state)) <$> simulateQ poolUp client := by
  induction client using OracleComp.inductionOn with
  | pure value => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      have head : StateT.run (simulateQ (PqxdhRegistrationJointKemPostSkeleton.skelImpl setup codec checks
          created.server.server.metadata.identityIndex created.publicIdentity (factoredServices setup codec checks))
          (simulateQ (PqxdhRegistrationJointKemPostSkeleton.groupedLift (Response := Response))
            (PqxdhRegistrationJointServiceSchedule.poolLift query))) state =
          (fun reply => (reply, state)) <$> poolUp query := by
        rw [show simulateQ (PqxdhRegistrationJointKemPostSkeleton.groupedLift (Response := Response))
            (PqxdhRegistrationJointServiceSchedule.poolLift query) =
            PqxdhRegistrationJointKemPostSkeleton.groupedLift (.inl (.inl query)) from simulateQ_spec_query _ _,
          show simulateQ (PqxdhRegistrationJointKemPostSkeleton.skelImpl setup codec checks
            created.server.server.metadata.identityIndex created.publicIdentity (factoredServices setup codec checks))
            (PqxdhRegistrationJointKemPostSkeleton.groupedLift (Response := Response) (.inl (.inl query))) =
            PqxdhRegistrationJointKemPostSkeleton.skelImpl setup codec checks
              created.server.server.metadata.identityIndex created.publicIdentity (factoredServices setup codec checks)
              (.inl (.inl (.inl query))) from simulateQ_spec_query _ _]
        rfl
      rw [head, bind_map_left]
      exact bind_congr fun reply => ih reply

/-- The owners after a source client create. -/
def grown (pin : PqxdhBeaconPhase2Preparation.Word32) (keyId : Std.U64)
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) :
    Option PqxdhRegistrationJointCreation.Birth → List PqxdhRegistrationJointGeneratedFinish.EncodedEntry
  | none => owners
  | some value => owners ++ [PqxdhRegistrationJointServiceSchedule.birth pin keyId value]

/-- The upper layers on a create: the indexed constructor client sent to the exposed encapsulation interface, then the new encoded owner appended. -/
theorem upperLayer_create (pin : PqxdhBeaconPhase2Preparation.Word32) (keyId : Std.U64)
    (state : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry × SkelState KemSK Output) :
    (upperLayer setup codec checks created.server.server.metadata.identityIndex created.publicIdentity t.kem.val
        p.challenge (factoredServices setup codec checks) (.inl (.inr (.create pin keyId)))).run state =
      (fun value => (state.1.length, (grown pin keyId state.1 value, state.2))) <$>
        simulateQ poolUp (PqxdhRegistrationJointCreation.client (KemSK := KemSK)) := by
  simp only [upperLayer, QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run_mk,
    PqxdhRegistrationJointKemPostSkeleton.groupedClient, PqxdhRegistrationJointRevealSchedule.client,
    PqxdhRegistrationJointServiceSchedule.handler]
  change (fun x => (x.1.1, x.1.2, x.2)) <$> StateT.run (simulateQ _
    (simulateQ PqxdhRegistrationJointKemPostSkeleton.groupedLift
      (PqxdhRegistrationJointServiceSchedule.create (Response := Response) pin keyId state.1))) state.2 = _
  simp only [PqxdhRegistrationJointServiceSchedule.create, bind_pure_comp, simulateQ_map, StateT.run_map,
    skel_pool, Functor.map_map]
  refine congrArg (fun f => f <$> _) (funext fun value => ?_)
  cases value <;> rfl

/-- The middle source handler on a create is the annotated pool create. -/
theorem sourceMid_create (pin : PqxdhBeaconPhase2Preparation.Word32) (keyId : Std.U64) (m : Mid KemSK) :
    (sourceMid setup codec route checks t p created (.inl (.inr (.create pin keyId)))).run m =
      (fun result => (result.1, { m with joint := result.2 })) <$>
        (PqxdhDeploymentIdealPoolSource.createSourcePool setup (p.pool t) pin keyId).run m.joint := rfl

/-- A create: item 2's constructor client through the post-challenge router reads the challenger's pool at the router's creation count, which is the owner count, as the middle's pool create does; it needs the KEM pool to be a prefix of the challenger's pool with one owner per key pair and room for one more creation. -/
theorem step_create (pin : PqxdhBeaconPhase2Preparation.Word32) (keyId : Std.U64) (m : Mid KemSK)
    (counted : m.joint.pool.2.keys.length = m.joint.owners.length)
    (prefixed : PqxdhDeploymentIdealPoolSource.PoolPrefix (p.pool t) m.joint.pool.2)
    (room : m.joint.pool.2.keys.length + 1 ≤ (p.pool t).length) :
    StepAt setup codec route checks t p created (.inl (.inr (.create pin keyId))) m := by
  have bounded : (PqxdhRegistrationJointCreation.client (KemSK := KemSK)).IsQueryBoundP
      (PqxdhLiveKemReservation.IsCreate (KemSK := KemSK)) 1 := by
    refine (isQueryBoundP_congr_pred (fun query => ?_)).mpr
      (PqxdhRegistrationJointServiceCosts.creation_queries (KemSK := KemSK) .kemCreate)
    rw [PqxdhDeploymentIdealPoolSource.isCreate_class]
  have noReveal : (PqxdhRegistrationJointCreation.client (KemSK := KemSK)).IsQueryBoundP
      (fun query => PqxdhRegistrationJointServiceCosts.poolClass (KemSK := KemSK) query = .other) 0 := by
    simpa [PqxdhRegistrationJointServiceCosts.createCap] using
      PqxdhRegistrationJointServiceCosts.creation_queries (KemSK := KemSK) .other
  have fresh := fresh_of_noDecaps t.kem.val p.challenge (PqxdhRegistrationJointCreation.client (KemSK := KemSK)) (by
    simpa [PqxdhRegistrationJointServiceCosts.createCap] using
      PqxdhRegistrationJointServiceCosts.creation_queries (KemSK := KemSK) .decapsulate)
  unfold StepAt
  rw [PqxdhDeploymentIdealPostSteps.upperE_run setup codec checks t p created _ _
      (PqxdhDeploymentIdealPostSteps.encodeMid_clean setup m), upperLayer_create, Functor.map_map,
    simulateQ_map, OptionT.run_map, StateT.run_map]
  rw [show (encodeMid setup m).2 = (PqxdhRegistrationJointKemObserverFree.eraseJoint
      (m.joint.pool.1, PqxdhDeploymentIdealPoolSource.routerOf m.joint.pool.2),
      (m.joint.shared.1.cache, (m.backend.2.1, m.backend.1))) from rfl,
    lowerE_pool setup t p _ 1 bounded noReveal fresh m.joint.pool.1 m.joint.pool.2 prefixed room,
    PqxdhDeploymentIdealPoolSource.client_reserved, sourceMid_create]
  rw [show (m.joint.pool.1, m.joint.pool.2).2.keys.length = m.joint.owners.length from counted]
  simp only [PqxdhDeploymentIdealPoolSource.createSourcePool, StateT.run, Functor.map_map]
  refine congrArg (fun f => f <$> _) (funext fun value => ?_)
  simp [encodeMid, grown, PqxdhRegistrationJointGeneratedFinish.encodeState,
    PqxdhRegistrationJointGeneratedFinish.encodeEntry, PqxdhRegistrationJointSchedule.created,
    PqxdhRegistrationJointSchedule.birth, PqxdhRegistrationJointCreation.serviceView,
    PqxdhRegistrationJointServiceSchedule.birth, PqxdhRegistrationJointBundle.encode,
    PqxdhBeaconPhase1Publication.mapState, PqxdhBeaconPhase1Publication.mapPhase,
    PqxdhRegistrationJointBundle.identityMap, PqxdhRegistrationJointBundle.keyMap]
  rfl

end Create

/-! ### The bundle request -/

section Bundle
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- The bundle program of an encoded owner, as private-service requests. -/
noncomputable abbrev bundleProgram (owner : PqxdhRegistrationJointBundle.Owner) :
    OracleComp (PqxdhLiveKemBirth.Spec KemSK) (Option Pqxdh.Bytes × PqxdhRegistrationJointBundle.Owner) :=
  simulateQ (PqxdhRegistrationJointBundleCompiler.compiler (KemSK := KemSK) codec)
    (PqxdhLivePhase1Bundle.bundle (PqxdhRegistrationJointBundle.projection setup) owner)

/-- The upper layers on a bundle at an absent address: no request, nothing changes. -/
theorem upperLayer_bundle_none (address : ℕ)
    (state : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry × SkelState KemSK Output)
    (missing : state.1[address]? = none) :
    (upperLayer setup codec checks created.server.server.metadata.identityIndex created.publicIdentity t.kem.val
        p.challenge (factoredServices setup codec checks) (.inl (.inr (.bundle address)))).run state =
      pure (none, state) := by
  rcases state with ⟨owners, skel⟩
  simp only [upperLayer, QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run_mk,
    PqxdhRegistrationJointKemPostSkeleton.groupedClient, PqxdhRegistrationJointRevealSchedule.client,
    PqxdhRegistrationJointServiceSchedule.handler]
  change (fun x => (x.1.1, x.1.2, x.2)) <$> StateT.run (simulateQ _
    (simulateQ PqxdhRegistrationJointKemPostSkeleton.groupedLift
      (PqxdhRegistrationJointServiceSchedule.bundle (Response := Response) setup codec address owners))) skel = _
  simp only [PqxdhRegistrationJointServiceSchedule.bundle, missing]
  simp

/-- The upper layers on a bundle at a present address: the owner's bundle program sent to the exposed encapsulation interface, then the owner reinstalled. -/
theorem upperLayer_bundle (address : ℕ) (entry : PqxdhRegistrationJointGeneratedFinish.EncodedEntry)
    (state : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry × SkelState KemSK Output)
    (found : state.1[address]? = some entry) :
    (upperLayer setup codec checks created.server.server.metadata.identityIndex created.publicIdentity t.kem.val
        p.challenge (factoredServices setup codec checks) (.inl (.inr (.bundle address)))).run state =
      (fun result => (result.1, (state.1.set address (entry.1, entry.2.1, result.2), state.2))) <$>
        simulateQ poolUp (bundleProgram setup codec entry.2.2) := by
  rcases state with ⟨owners, skel⟩
  simp only [upperLayer, QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run_mk,
    PqxdhRegistrationJointKemPostSkeleton.groupedClient, PqxdhRegistrationJointRevealSchedule.client,
    PqxdhRegistrationJointServiceSchedule.handler]
  change (fun x => (x.1.1, x.1.2, x.2)) <$> StateT.run (simulateQ _
    (simulateQ PqxdhRegistrationJointKemPostSkeleton.groupedLift
      (PqxdhRegistrationJointServiceSchedule.bundle (Response := Response) setup codec address owners))) skel = _
  simp only [PqxdhRegistrationJointServiceSchedule.bundle, found, simulateQ_map, StateT.run_map, skel_pool,
    Functor.map_map]

/-- The middle source handler on a bundle is the annotated bundle. -/
theorem sourceMid_bundle (address : ℕ) (m : Mid KemSK) :
    (sourceMid setup codec route checks t p created (.inl (.inr (.bundle address)))).run m =
      (fun result => (result.1, { m with joint := result.2 })) <$>
        (PqxdhRegistrationJointSchedule.bundle setup codec address).run m.joint := rfl

/-- A prefix pool is no longer than the pairs. -/
theorem prefix_length (pairs : List (PqxdhLiveKemReservation.Pair KemSK)) (pool : PqxdhLiveKemBirth.Pool KemSK)
    (prefixed : PqxdhDeploymentIdealPoolSource.PoolPrefix pairs pool) : pool.keys.length ≤ pairs.length := by
  have lengths := congrArg List.length prefixed
  rw [List.length_take] at lengths
  omega

/-- A bundle: the owner's bundle program through the post-challenge router is its run under the actual services (it creates no KEM key and decapsulates nothing), which is the annotated source's bundle trace by item 2's `PqxdhRegistrationJointBundleCompiler.bundle_source`; it needs item 2's ownership of the annotated state and a prefix KEM pool. -/
theorem step_bundle (address : ℕ) (m : Mid KemSK) (owned : PqxdhRegistrationJointSchedule.Invariant m.joint)
    (prefixed : PqxdhDeploymentIdealPoolSource.PoolPrefix (p.pool t) m.joint.pool.2) :
    StepAt setup codec route checks t p created (.inl (.inr (.bundle address))) m := by
  unfold StepAt
  rw [PqxdhDeploymentIdealPostSteps.upperE_run setup codec checks t p created _ _
      (PqxdhDeploymentIdealPostSteps.encodeMid_clean setup m), sourceMid_bundle]
  rcases found : m.joint.owners[address]? with _ | entry
  · have missing : (encodeMid setup m).1.1[address]? = none := by
      simp [encodeMid, PqxdhRegistrationJointGeneratedFinish.encodeState, List.getElem?_map, found]
    rw [upperLayer_bundle_none setup codec checks t p created address _ missing, map_pure, simulateQ_pure]
    simp only [PqxdhRegistrationJointSchedule.bundle, found, StateT.run]
    simp only [OptionT.run_pure, map_pure]
    rfl
  · have present : (encodeMid setup m).1.1[address]? =
        some (PqxdhRegistrationJointGeneratedFinish.encodeEntry setup entry) := by
      simp [encodeMid, PqxdhRegistrationJointGeneratedFinish.encodeState, List.getElem?_map, found]
    have bounded := PqxdhRegistrationJointServiceCosts.bundle_queries (KemSK := KemSK) setup codec
      (PqxdhRegistrationJointGeneratedFinish.encodeEntry setup entry).2.2 .kemCreate
    have noCreate : (bundleProgram setup codec (PqxdhRegistrationJointGeneratedFinish.encodeEntry setup entry).2.2 :
        OracleComp (PqxdhLiveKemBirth.Spec KemSK) _).IsQueryBoundP (PqxdhLiveKemReservation.IsCreate (KemSK := KemSK)) 0 := by
      refine (isQueryBoundP_congr_pred (fun query => ?_)).mpr (by simpa [PqxdhRegistrationJointServiceCosts.bundleCap] using bounded)
      rw [PqxdhDeploymentIdealPoolSource.isCreate_class]
    have noReveal : (bundleProgram setup codec (PqxdhRegistrationJointGeneratedFinish.encodeEntry setup entry).2.2 :
        OracleComp (PqxdhLiveKemBirth.Spec KemSK) _).IsQueryBoundP
          (fun query => PqxdhRegistrationJointServiceCosts.poolClass (KemSK := KemSK) query = .other) 0 := by
      simpa [PqxdhRegistrationJointServiceCosts.bundleCap] using
        PqxdhRegistrationJointServiceCosts.bundle_queries (KemSK := KemSK) setup codec
          (PqxdhRegistrationJointGeneratedFinish.encodeEntry setup entry).2.2 .other
    have fresh := fresh_of_noDecaps t.kem.val p.challenge
      (bundleProgram setup codec (PqxdhRegistrationJointGeneratedFinish.encodeEntry setup entry).2.2 :
        OracleComp (PqxdhLiveKemBirth.Spec KemSK) _) (by
      simpa [PqxdhRegistrationJointServiceCosts.bundleCap] using
        PqxdhRegistrationJointServiceCosts.bundle_queries (KemSK := KemSK) setup codec
          (PqxdhRegistrationJointGeneratedFinish.encodeEntry setup entry).2.2 .decapsulate)
    rw [upperLayer_bundle setup codec checks t p created address _ _ present, Functor.map_map,
      simulateQ_map, OptionT.run_map, StateT.run_map]
    rw [show (encodeMid setup m).2 = (PqxdhRegistrationJointKemObserverFree.eraseJoint
        (m.joint.pool.1, PqxdhDeploymentIdealPoolSource.routerOf m.joint.pool.2),
        (m.joint.shared.1.cache, (m.backend.2.1, m.backend.1))) from rfl,
      lowerE_pool setup t p _ 0 noCreate noReveal fresh m.joint.pool.1 m.joint.pool.2 prefixed
        (by simpa using prefix_length _ _ prefixed),
      PqxdhDeploymentIdealPoolSource.reserved_noCreate setup (p.pool t) _ noCreate]
    have source := PqxdhRegistrationJointBundleCompiler.bundle_source setup codec entry.identityIndex entry.kemIndex
      entry.owner (m.joint.pool.1, m.joint.pool.2) (owned entry (List.mem_of_getElem? found)).1
    rw [show bundleProgram setup codec (PqxdhRegistrationJointGeneratedFinish.encodeEntry setup entry).2.2 =
      simulateQ (PqxdhRegistrationJointBundleCompiler.compiler (KemSK := KemSK) codec) (PqxdhLivePhase1Bundle.bundle
        (PqxdhRegistrationJointBundle.projection setup)
        (PqxdhRegistrationJointBundle.encode setup entry.identityIndex entry.kemIndex entry.owner)) from rfl, source]
    simp only [PqxdhRegistrationJointSchedule.bundle, found, StateT.run, Functor.map_map]
    refine congrArg (fun f => f <$> _) (funext fun result => ?_)
    simp [encodeMid, PqxdhRegistrationJointGeneratedFinish.encodeState, PqxdhRegistrationJointGeneratedFinish.encodeEntry,
      List.map_set]
    rfl

end Bundle

end BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.upperLayer_hmac' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.upperLayer_hmac

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.step_hmac' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.step_hmac

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.localValue_encode' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.localValue_encode

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.step_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.step_read

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.postDecapsulation_fresh' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.postDecapsulation_fresh

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.kemStep_fresh' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.kemStep_fresh

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.jointStep_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.jointStep_fresh

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.jointProgram_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.jointProgram_fresh

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.challengeDecaps_class' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.challengeDecaps_class

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.fresh_of_noDecaps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.fresh_of_noDecaps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.service_pool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.service_pool

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.service_poolProgram' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.service_poolProgram

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.lowerE_pool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.lowerE_pool

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.skel_pool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.skel_pool

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.upperLayer_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.upperLayer_create

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.sourceMid_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.sourceMid_create

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.step_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.step_create

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.upperLayer_bundle_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.upperLayer_bundle_none

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.upperLayer_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.upperLayer_bundle

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.sourceMid_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.sourceMid_bundle

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.prefix_length' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.prefix_length

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.step_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests.step_bundle
