-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueTail

/-! Join the literal saved post-encapsulation suffix to the source allocation/root/clear/consume/publication tail. Candidate bytes occur only in the private interpretation. `resume_lift` states the join for every outer monad that receives the native game through a monad morphism and for every prefix interpreter in that monad: the suffix's optional failures and consumed state, the prefix interpreter's own effects and the complete native continuation stay in source order. It is instantiated at the native game itself, at the exposed encapsulation-cut client, under the real encapsulator with open private services, at the stateful private services of the actual accept state, at the ordinary CCA challenge reply, and under the KEM reduction's post-challenge interpreter. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueResume
open PqxdhRegistrationJointKemOpaqueSuffix PqxdhRegistrationJointKemOpaqueClient
open PqxdhServerAuthExperiment PqxdhServerAuthNative PqxdhJointIdentity
open PqxdhServerRootPreparation
variable {Reader KemSK Response Result : Type} {ι : Type} {baseSpec : OracleSpec ι}

abbrev Spec (Reader KemSK : Type) := PqxdhRegistrationJointKemEncapsulation.Spec KemSK +
  PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK

def prefixLift : QueryImpl (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) (OracleComp (Spec Reader KemSK)) :=
  fun query => (Spec Reader KemSK).query (.inl query)
def tailLift : QueryImpl (PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK) (OracleComp (Spec Reader KemSK)) :=
  fun query => (Spec Reader KemSK).query (.inr query)

/-- Complete private interpretation for a prefix interpreter whose target is the native game. The selected value is absent from the executable request program. -/
noncomputable def impl (setup : Setup baseSpec KemSK) (index : Nat)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (preImpl : QueryImpl (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) (NativeGame KemSK)) :
    QueryImpl (Spec Reader KemSK) (NativeGame KemSK)
  | .inl query => preImpl query
  | .inr query => PqxdhRegistrationJointKemOpaqueTail.impl setup.hmac index candidate query

/-- The original remaining service program retains its whole adaptive effect under the combined interpreter. -/
theorem prefix_run (setup : Setup baseSpec KemSK) (index : Nat)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (preImpl : QueryImpl (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) (NativeGame KemSK))
    (work : OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) Result) :
    simulateQ (impl (Reader := Reader) setup index candidate preImpl) (simulateQ prefixLift work) =
      simulateQ preImpl work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih => simp only [simulateQ_bind, simulateQ_spec_query, prefixLift, impl, ih]

/-- The native tail interpreter is unchanged under the combined interface, including full private state. -/
theorem tail_run (setup : Setup baseSpec KemSK) (index : Nat)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (preImpl : QueryImpl (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) (NativeGame KemSK))
    (work : OracleComp (PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK) Result) :
    simulateQ (impl setup index candidate preImpl) (simulateQ tailLift work) =
      simulateQ (PqxdhRegistrationJointKemOpaqueTail.impl setup.hmac index candidate) work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih => simp only [simulateQ_bind, simulateQ_spec_query, tailLift, impl, ih]

/-- Actual suffix and actual tail execute consecutively without any selected-KEM argument or selected-KEM-dependent runtime test. The executable steps still branch on private DH-derived values, exactly as the source does. -/
noncomputable def resume (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (raw : Pqxdh.Bytes)
    (verified : Verified Reader) (ephemeral : Ephemeral PqxdhJointGapDh.ScalarBytes)
    (ciphertext : PqxdhBeaconPhase2Preparation.Ciphertext) (token : Token)
    (state : GameState KemSK) (consumed : List Pqxdh.Bytes) : OracleComp (Spec Reader KemSK) (Option Nat) := do
  let collected ← simulateQ prefixLift
    ((compiled setup codec checks identityIndex raw verified ephemeral ciphertext token).run consumed)
  simulateQ tailLift (PqxdhRegistrationJointKemOpaqueTail.tail setup.serverKeyId publicIdentity state collected)

section Lifted
variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Complete private interpretation in an arbitrary outer monad. Prefix requests use any supplied interpreter in that monad; tail requests use the private native tail interpreter transported by the supplied monad morphism. -/
noncomputable def liftImpl (native : NativeGame KemSK →ᵐ m) (setup : Setup baseSpec KemSK) (index : Nat)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (preImpl : QueryImpl (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) m) :
    QueryImpl (Spec Reader KemSK) m
  | .inl query => preImpl query
  | .inr query => native.toFun _ (PqxdhRegistrationJointKemOpaqueTail.impl setup.hmac index candidate query)

/-- The remaining service program keeps its whole adaptive effect under the supplied outer interpreter. -/
theorem lift_prefix (native : NativeGame KemSK →ᵐ m) (setup : Setup baseSpec KemSK) (index : Nat)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (preImpl : QueryImpl (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) m)
    (work : OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) Result) :
    simulateQ (liftImpl (Reader := Reader) native setup index candidate preImpl) (simulateQ prefixLift work) =
      simulateQ preImpl work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih => simp only [simulateQ_bind, simulateQ_spec_query, prefixLift, liftImpl, ih]

/-- The tail runs as the transported complete native tail computation, including its full private state. -/
theorem lift_tail (native : NativeGame KemSK →ᵐ m) (setup : Setup baseSpec KemSK) (index : Nat)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (preImpl : QueryImpl (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) m)
    (work : OracleComp (PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK) Result) :
    simulateQ (liftImpl native setup index candidate preImpl) (simulateQ tailLift work) =
      native.toFun _ (simulateQ (PqxdhRegistrationJointKemOpaqueTail.impl setup.hmac index candidate) work) := by
  induction work using OracleComp.inductionOn with
  | pure value =>
      simp only [simulateQ_pure]
      exact (native.toFun_pure' value).symm
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, tailLift, liftImpl, ih]
      exact (native.toFun_bind' _ _).symm

/-- The entire resumed source execution equals the original suffix, with the KEM candidate materialized, followed by the transported original native tail. The outer monad, its native embedding and the prefix interpreter are arbitrary. No marginal key equality, successful-suffix premise or fresh-input assumption is needed. -/
theorem resume_lift (native : NativeGame KemSK →ᵐ m) (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (raw : Pqxdh.Bytes)
    (verified : Verified Reader) (ephemeral : Ephemeral PqxdhJointGapDh.ScalarBytes)
    (ciphertext : PqxdhBeaconPhase2Preparation.Ciphertext) (token : Token)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (state : GameState KemSK) (consumed : List Pqxdh.Bytes)
    (preImpl : QueryImpl (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) m) :
    simulateQ (liftImpl native setup state.sessions candidate preImpl)
      (resume setup codec checks identityIndex publicIdentity raw verified ephemeral ciphertext token state consumed) =
      (do
        let collected ← simulateQ preImpl
          ((PqxdhRegistrationJointKemSourceSuffix.suffix setup codec checks identityIndex raw verified ephemeral
            (some (ciphertext, PqxdhRootTableInitialization.rootArray
              (PqxdhPhase2DecapsulationRouting.materialize candidate token)))).run consumed)
        native.toFun _ (PqxdhRegistrationJointServerAccept.tail setup publicIdentity state collected)) := by
  rw [← compiled_native setup codec checks identityIndex raw candidate verified ephemeral ciphertext token consumed]
  simp only [resume, simulateQ_bind, lift_prefix, lift_tail, simulateQ_map, bind_map_left]
  apply bind_congr
  intro collected
  rw [PqxdhRegistrationJointKemOpaqueTail.tail_native setup publicIdentity candidate state collected]

end Lifted

/-- For every prefix interpreter whose target is the native game itself, the entire resumed source execution has exactly its original full native-state distribution. It is the identity-morphism case of `resume_lift`; interpreters in other monads, including the actual private services and the KEM reduction, are covered by `resume_lift` and its instantiations below. No marginal key equality, successful-suffix premise or fresh-input assumption is needed. -/
theorem resume_native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (raw : Pqxdh.Bytes)
    (verified : Verified Reader) (ephemeral : Ephemeral PqxdhJointGapDh.ScalarBytes)
    (ciphertext : PqxdhBeaconPhase2Preparation.Ciphertext) (token : Token)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (state : GameState KemSK) (consumed : List Pqxdh.Bytes)
    (preImpl : QueryImpl (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) (NativeGame KemSK)) :
    simulateQ (impl setup state.sessions candidate preImpl)
      (resume setup codec checks identityIndex publicIdentity raw verified ephemeral ciphertext token state consumed) =
      (do
        let collected ← simulateQ preImpl
          ((PqxdhRegistrationJointKemSourceSuffix.suffix setup codec checks identityIndex raw verified ephemeral
            (some (ciphertext, PqxdhRootTableInitialization.rootArray
              (PqxdhPhase2DecapsulationRouting.materialize candidate token)))).run consumed)
        PqxdhRegistrationJointServerAccept.tail setup publicIdentity state collected) :=
  resume_lift (MonadHom.id _) setup codec checks identityIndex publicIdentity raw verified ephemeral ciphertext token
    candidate state consumed preImpl

/-- The exposed encapsulation-cut client monad of `KemEncapsulation.accept`. -/
abbrev Client (KemSK : Type) := StateT (NativeState KemSK) (OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK))

/-- The exact native embedding used by `KemEncapsulation.accept`: native coins become private-service uniform requests and every other request is forwarded unchanged. -/
noncomputable def clientNative : NativeGame KemSK →ᵐ Client KemSK where
  toFun _ work := PqxdhRegistrationJointKemEncapsulation.lift (PqxdhRegistrationJointOpenBackend.native work)
  toFun_pure' value := by
    funext state
    change simulateQ PqxdhRegistrationJointKemEncapsulation.forward
        (PqxdhLiveKemBirth.coins ((pure value : NativeGame KemSK _).run state)) =
      (pure value : Client KemSK _).run state
    rw [StateT.run_pure, StateT.run_pure]
    simp only [PqxdhLiveKemBirth.coins, simulateQ_pure]
  toFun_bind' work next := by
    funext state
    change simulateQ PqxdhRegistrationJointKemEncapsulation.forward
        (PqxdhLiveKemBirth.coins ((work >>= next).run state)) =
      (PqxdhRegistrationJointKemEncapsulation.lift (PqxdhRegistrationJointOpenBackend.native work) >>=
        fun value => PqxdhRegistrationJointKemEncapsulation.lift
          (PqxdhRegistrationJointOpenBackend.native (next value))).run state
    rw [StateT.run_bind, StateT.run_bind]
    simp only [PqxdhLiveKemBirth.coins, simulateQ_bind]
    rfl

/-- Prefix requests are forwarded to the exposed interface with the native state unchanged, as in `KemEncapsulation.prepare`. -/
def forwardClient : QueryImpl (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) (Client KemSK) :=
  fun query state => (fun answer => (answer, state)) <$> (PqxdhRegistrationJointKemEncapsulation.Spec KemSK).query query

/-- Forwarding retains the complete prefix program and leaves the native state untouched. -/
theorem forward_client (work : OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) Result)
    (state : NativeState KemSK) :
    (simulateQ forwardClient work).run state = (fun answer => (answer, state)) <$> work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      change ((fun answer => (answer, state)) <$>
          ((PqxdhRegistrationJointKemEncapsulation.Spec KemSK).query query :
            OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) _)) >>=
          (fun result => (simulateQ forwardClient (next result.1)).run result.2) = _
      simp only [bind_map_left, ih]

/-- Client instantiation: the opaque resumption is exactly the saved source suffix followed by the original tail through the same native embedding as `KemEncapsulation.accept`. -/
theorem resume_client (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (raw : Pqxdh.Bytes)
    (verified : Verified Reader) (ephemeral : Ephemeral PqxdhJointGapDh.ScalarBytes)
    (ciphertext : PqxdhBeaconPhase2Preparation.Ciphertext) (token : Token)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (state : GameState KemSK) (consumed : List Pqxdh.Bytes)
    (native : NativeState KemSK) :
    (simulateQ (liftImpl clientNative setup state.sessions candidate forwardClient)
      (resume setup codec checks identityIndex publicIdentity raw verified ephemeral ciphertext token state consumed)).run native =
      (do
        let collected ← (PqxdhRegistrationJointKemSourceSuffix.suffix setup codec checks identityIndex raw verified
          ephemeral (some (ciphertext, PqxdhRootTableInitialization.rootArray
            (PqxdhPhase2DecapsulationRouting.materialize candidate token)))).run consumed
        (PqxdhRegistrationJointKemEncapsulation.lift (PqxdhRegistrationJointOpenBackend.native
          (PqxdhRegistrationJointServerAccept.tail setup publicIdentity state collected))).run native) := by
  rw [resume_lift, StateT.run_bind, forward_client, bind_map_left]
  rfl

/-- Open-backend instantiation: interpreting the exposed interface by the real encapsulator `KemEncapsulation.actual`, which leaves the identity/KEM service requests open, turns the opaque resumption into the original open-backend raw-prefix suffix followed by the original native tail. -/
theorem resume_actual (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (raw : Pqxdh.Bytes)
    (verified : Verified Reader) (ephemeral : Ephemeral PqxdhJointGapDh.ScalarBytes)
    (ciphertext : PqxdhBeaconPhase2Preparation.Ciphertext) (token : Token)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (state : GameState KemSK) (consumed : List Pqxdh.Bytes)
    (native : NativeState KemSK) :
    simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
      ((simulateQ (liftImpl clientNative setup state.sessions candidate forwardClient)
        (resume setup codec checks identityIndex publicIdentity raw verified ephemeral ciphertext token state consumed)).run native) =
      (do
        let collected ← (simulateQ (PqxdhRegistrationJointOpenBackend.prefixImpl setup codec checks)
          (simulateQ (PqxdhRegistrationJointServerPrefix.compiler identityIndex)
            (PqxdhRegistrationJointKemCollected.afterEncapsulation verified ephemeral
              (some (ciphertext, PqxdhRootTableInitialization.rootArray
                (PqxdhPhase2DecapsulationRouting.materialize candidate token)))))).run consumed
        (PqxdhRegistrationJointOpenBackend.native
          (PqxdhRegistrationJointServerAccept.tail setup publicIdentity state collected)).run native) := by
  rw [resume_client, simulateQ_bind]
  simp only [PqxdhRegistrationJointKemSourceSuffix.suffix, PqxdhRegistrationJointKemSourceSuffix.handler,
    QueryImpl.simulateQ_compose, PqxdhRegistrationJointKemEncapsulation.prefix_program,
    PqxdhRegistrationJointKemEncapsulation.lift_actual]

open PqxdhRegistrationJointFinish (State onPool onNative) in
/-- The native embedding of the actual Server accept state, whose first component holds the private identity/KEM service state and whose second is the complete native state. -/
noncomputable def serviceNative : NativeGame KemSK →ᵐ StateT (State KemSK) ProbComp where
  toFun _ work := onNative work
  toFun_pure' value := by
    funext state
    simp only [onNative]
    rfl
  toFun_bind' work next := by
    funext state
    change (fun result => (result.1, (state.1, result.2))) <$> (work >>= next).run state.2 =
      ((onNative work) >>= fun value => onNative (next value)).run state
    rw [StateT.run_bind, StateT.run_bind]
    simp only [onNative, StateT.run, map_bind, bind_map_left]

open PqxdhRegistrationJointFinish (State onPool) in
/-- The actual private-service interpreter of the exposed interface: the real source encapsulator and the stateful identity/KEM service backend, run on the private service component only. -/
noncomputable def serviceImpl (setup : Setup baseSpec KemSK) :
    QueryImpl (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) (StateT (State KemSK) ProbComp) :=
  fun query => onPool ((PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem ∘ₛ
    PqxdhRegistrationJointKemEncapsulation.actual setup) query)

open PqxdhRegistrationJointFinish (onNative) in
/-- Actual stateful service instantiation: with the real encapsulator and the stateful identity/KEM services on the private component of the actual accept state, the opaque resumption is the saved suffix under those services followed by the original native tail on the native component. -/
theorem resume_service (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (raw : Pqxdh.Bytes)
    (verified : Verified Reader) (ephemeral : Ephemeral PqxdhJointGapDh.ScalarBytes)
    (ciphertext : PqxdhBeaconPhase2Preparation.Ciphertext) (token : Token)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (state : GameState KemSK) (consumed : List Pqxdh.Bytes) :
    simulateQ (liftImpl serviceNative setup state.sessions candidate (serviceImpl setup))
      (resume setup codec checks identityIndex publicIdentity raw verified ephemeral ciphertext token state consumed) =
      (do
        let collected ← simulateQ (serviceImpl setup)
          ((PqxdhRegistrationJointKemSourceSuffix.suffix setup codec checks identityIndex raw verified ephemeral
            (some (ciphertext, PqxdhRootTableInitialization.rootArray
              (PqxdhPhase2DecapsulationRouting.materialize candidate token)))).run consumed)
        onNative (PqxdhRegistrationJointServerAccept.tail setup publicIdentity state collected)) :=
  resume_lift serviceNative setup codec checks identityIndex publicIdentity raw verified ephemeral ciphertext token
    candidate state consumed (serviceImpl setup)

/-- CCA challenge-reply instantiation: the saved encapsulation continuation of `KemSourceSuffix.suffix_cut`, resumed with the ordinary challenge reply and followed by the original accept tail and any later source work, is the candidate-free executable resumption under the private client interpreter. The candidate occurs only in that interpreter. -/
theorem resume_reply (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (raw : Pqxdh.Bytes)
    (verified : Verified Reader) (ephemeral : Ephemeral PqxdhJointGapDh.ScalarBytes)
    (ciphertext : PqxdhKemIndCca.MlKem768Ciphertext) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (state : GameState KemSK) (consumed : List Pqxdh.Bytes) (native : NativeState KemSK)
    (rest : Option Nat × NativeState KemSK → OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) Result) :
    (do
      let input ← (PqxdhRegistrationJointKemSourceSuffix.suffix setup codec checks identityIndex raw verified ephemeral
        (PqxdhRegistrationJointKemResume.reply ciphertext candidate)).run consumed
      let out ← (PqxdhRegistrationJointKemEncapsulation.lift (PqxdhRegistrationJointOpenBackend.native
        (PqxdhRegistrationJointServerAccept.tail setup publicIdentity state input))).run native
      rest out) =
      (do
        let out ← (simulateQ (liftImpl clientNative setup state.sessions candidate forwardClient)
          (resume setup codec checks identityIndex publicIdentity raw verified ephemeral
            (PqxdhAcceptedRegistration.ciphertextArray ciphertext) .challenge state consumed)).run native
        rest out) := by
  rw [resume_client, bind_assoc]
  rfl

/-- KEM-reduction instantiation: the same equality holds after the exact post-challenge interpreter chain used by `KemResume.post`, namely the actual encapsulator followed by the dynamic joint router into the ordinary CCA oracle interface. This is source correspondence only; it charges no advantage. -/
theorem resume_post (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (raw : Pqxdh.Bytes)
    (verified : Verified Reader) (ephemeral : Ephemeral PqxdhJointGapDh.ScalarBytes)
    (ciphertext : PqxdhKemIndCca.MlKem768Ciphertext) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (state : GameState KemSK) (consumed : List Pqxdh.Bytes) (native : NativeState KemSK)
    (rest : Option Nat × NativeState KemSK → OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) Result)
    (selected : Nat) (reservation : PqxdhDynamicKemRouter.Reservation KemSK)
    (source : PqxdhDynamicKemJointSource.State KemSK) :
    ((simulateQ (PqxdhDynamicKemJointRouter.post (baseSpec := baseSpec) setup.joint setup.kem selected reservation
      ciphertext candidate)
      (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup) (do
        let input ← (PqxdhRegistrationJointKemSourceSuffix.suffix setup codec checks identityIndex raw verified ephemeral
          (PqxdhRegistrationJointKemResume.reply ciphertext candidate)).run consumed
        let out ← (PqxdhRegistrationJointKemEncapsulation.lift (PqxdhRegistrationJointOpenBackend.native
          (PqxdhRegistrationJointServerAccept.tail setup publicIdentity state input))).run native
        rest out))).run).run source =
      ((simulateQ (PqxdhDynamicKemJointRouter.post (baseSpec := baseSpec) setup.joint setup.kem selected reservation
        ciphertext candidate)
        (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup) (do
          let out ← (simulateQ (liftImpl clientNative setup state.sessions candidate forwardClient)
            (resume setup codec checks identityIndex publicIdentity raw verified ephemeral
              (PqxdhAcceptedRegistration.ciphertextArray ciphertext) .challenge state consumed)).run native
          rest out))).run).run source := by
  rw [resume_reply]

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueResume

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueResume.prefix_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueResume.prefix_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueResume.tail_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueResume.tail_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueResume.lift_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueResume.lift_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueResume.lift_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueResume.lift_tail

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueResume.resume_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueResume.resume_lift

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueResume.resume_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueResume.resume_native

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueResume.forward_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueResume.forward_client

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueResume.resume_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueResume.resume_client

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueResume.resume_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueResume.resume_actual

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueResume.resume_service' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueResume.resume_service

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueResume.resume_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueResume.resume_reply

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueResume.resume_post' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueResume.resume_post
