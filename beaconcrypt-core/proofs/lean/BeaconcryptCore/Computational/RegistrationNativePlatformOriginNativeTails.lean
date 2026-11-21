import BeaconcryptCore.Computational.RegistrationNativePlatformOriginSourceTails
-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendEnvelope
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBounds
import BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills
/-! The literal native free source has no hidden seal outside the two send branches. Actual send continuations retain the post-seal publication and stateful reserve with complete reached public controls. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeTails
open PqxdhRecordLiftInterface (Environment WorldSpec)
open PqxdhRecordLiftProtocol (ServiceSpec Control)
open PqxdhRecordLiftCtxProtocolBounds (BudgetKind categoryCost)
open PqxdhRecordLiftCtxProgramBounds (Weighted weighted_indicator weighted_run)
open PqxdhRecordLiftCtxBills (worldBill)
open PqxdhRecordLiftBudget (WorldRecord NativeRecord)
open PqxdhServerAuthExperiment (Codec)
variable {n : Nat} {Platform Failure Reader Response A : Type}

noncomputable def source (env : Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp PqxdhDeploymentInterface.Spec A) (before : Platform)
    (shell : CborRecordWorldClient.Shell) (control : Control n) :=
  (simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
    ((simulateQ CborRecordWorldClient.handler
      ((simulateQ (RegistrationNativePlatformGatedRecordInterface.native env reserve) work).run before)).run shell)).run control

private theorem source_bind {B : Type} (env : Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp PqxdhDeploymentInterface.Spec A) (next : A → OracleComp PqxdhDeploymentInterface.Spec B)
    (before : Platform) (shell : CborRecordWorldClient.Shell) (control : Control n) :
    source env reserve codec route (work >>= next) before shell control=
      (do
        let result ← source env reserve codec route work before shell control
        source env reserve codec route (next result.1.1.1) result.1.1.2 result.1.2 result.2) := by
  simp only [source,simulateQ_bind,StateT.run_bind]

private theorem source_pure (env : Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (value : A) (before : Platform) (shell : CborRecordWorldClient.Shell) (control : Control n) :
    source env reserve codec route (pure value) before shell control=pure (((value,before),shell),control) := by
  simp only [source,simulateQ_pure,StateT.run_pure]

private theorem weighted_zero {I : Type} {spec : OracleSpec I} (cost : I → Nat)
    (work : OracleComp spec A) (bounded : Weighted cost work 0) : work.AllQueriesSatisfy (fun query=>cost query=0) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    rw [Weighted,isQueryBound_query_bind_iff] at bounded
    rw [allQueriesSatisfy_query_bind_iff]
    refine ⟨by omega,?_⟩
    intro reply
    apply ih reply
    change (next reply).IsQueryBound 0 (fun query available=>cost query≤available) (fun query available=>available-cost query)
    simpa only [Nat.zero_sub] using bounded.2 reply

private theorem seal_bill : (worldBill .seal : (WorldSpec n).Domain → Nat)=
    fun query=>if WorldRecord .send query then 1 else 0 := by
  funext query
  rcases query with created|(effect|record)
  · rfl
  · cases effect <;> rfl
  · rcases record with (send|raw)|⟨owner,plaintext|raw⟩ <;> rfl

/-- Genuine non-send native syntax emits no hidden sealing request, including arbitrary environment programs and every CBOR outcome. -/
theorem non_send (env : Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (query : PqxdhDeploymentInterface.Spec.Domain) (quiet : ¬NativeRecord .send query)
    (before : Platform) (shell : CborRecordWorldClient.Shell) (control : Control n) :
    (((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
      ((simulateQ CborRecordWorldClient.handler
        ((RegistrationNativePlatformGatedRecordInterface.native env reserve query).run before)).run shell)).run control)).AllQueriesSatisfy
      (fun request=>∀pending,request≠.sealing pending) := by
  have original := RegistrationNativePlatformGatedRecordBounds.native_step env reserve .send query before
  simp only [quiet,ite_false] at original
  have cursor := CborRecordWorldClient.client_bound
    ((RegistrationNativePlatformGatedRecordInterface.native env reserve query).run before) (WorldRecord .send) 0 original shell
  simp only [CborRecordWorldClient.client,isQueryBoundP_map_iff] at cursor
  have weight := weighted_indicator (WorldRecord .send) 1 _ 0 cursor
  simp only [Nat.one_mul] at weight
  rw [←seal_bill] at weight
  have compiled := weighted_run (worldBill .seal) (categoryCost .seal)
    (PqxdhRecordLiftProtocol.handler codec.frameRead route) _ 0 control weight
    (fun request current=>PqxdhRecordLiftCtxBills.handler_categories .seal codec.frameRead route request current)
  apply (weighted_zero (categoryCost .seal) _ compiled).mono
  intro request zero pending equal
  subst request
  change (1 : Nat)=0 at zero
  omega
open RegistrationNativePlatformOriginSourceTails (HasTails)
open PqxdhRecordLiftWorldCompiler (Label LabeledKernel Server Peer)

private theorem lookup_seal {X : Type} (pending : PqxdhRecordLiftProtocol.Sealing n)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (after : Option RawCtxSourceSend.Encrypted → Platform → OracleComp (ServiceSpec n) X)
    (before : Platform) (tag : PqxdhDeploymentInterface.FrameTag)
    (later : ∀output state,HasTails Platform Failure (after output state)) :
    HasTails Platform Failure (do
      let _ ← ((ServiceSpec n).query (.lookup pending.material) : OracleComp (ServiceSpec n) _)
      let reply ← ((ServiceSpec n).query (.sealing pending) : OracleComp (ServiceSpec n) _)
      RegistrationNativePlatformOriginReserveContinuationBound.continued reserve after before tag reply) := by
  apply RegistrationNativePlatformOriginSourceTails.nonsealing _ _ ?_
  · intro _
    exact RegistrationNativePlatformOriginSourceTails.sealing_node pending reserve after before tag later
  · rintro ⟨sealed,impossible⟩
    cases impossible

/-- Every non-send branch derives the literal source tail property from its genuine zero-sealing syntax. -/
theorem non_send_tails (env : Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (query : PqxdhDeploymentInterface.Spec.Domain) (quiet : ¬NativeRecord .send query)
    (before : Platform) (shell : CborRecordWorldClient.Shell) (control : Control n) :
    HasTails Platform Failure (source env reserve codec route (PqxdhDeploymentInterface.Spec.query query) before shell control) := by
  apply RegistrationNativePlatformOriginSourceTails.zero
  simp only [source,simulateQ_spec_query]
  have noSeal := non_send env reserve codec route query quiet before shell control
  apply noSeal.mono
  rintro request absent ⟨pending,equal⟩
  exact absent pending equal

/-- The actual hidden Server source has its real reserve tail after every optional sealing reply. -/
theorem server_hidden (env : Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (before : Platform) (shell : CborRecordWorldClient.Shell) (control : Control n)
    (keyId : U64) (plaintext : Pqxdh.Bytes)
    (admitted : CborRecordWorldClient.refusal (n := n) (.inr (.inr (.inl (.inl (plaintext,keyId))))) shell=none)
    (server : Server n) (serverAt : control.server=some server) (peer : Peer n) (peerAt : server.peers keyId=some peer)
    (slot : PqxdhRecordLiftInterface.Slot n) (kernel : LabeledKernel n) (hidden : peer.kernel=.hidden slot kernel)
    (nonempty : plaintext.isEmpty=false)
    (pending : RawCtxChainSend.Kdf (Label n) (Label n) (Label n) RawCtxSourceSend.SealContext)
    (requested : RawCtxChainSend.normalBegin kernel
      ⟨plaintext,keyId,server.sender,(PqxdhRecordLiftWorldCompiler.serverOwner server keyId peer).associatedData⟩=.requested pending) :
    HasTails Platform Failure (source env reserve codec route (PqxdhDeploymentInterface.Spec.query (.inr (.serverSend keyId plaintext))) before shell control) := by
  simp only [source,simulateQ_spec_query]
  rw [RegistrationNativePlatformOriginSendEnvelope.server_hidden env reserve codec route before shell control keyId plaintext
    admitted server serverAt peer peerAt slot kernel hidden nonempty pending requested]
  let ready := RawCtxChainSend.ready pending (PqxdhRecordLiftChainState.advance pending.request 1,pending.request)
  let after : Option RawCtxSourceSend.Encrypted → Platform → OracleComp (ServiceSpec n) _ := fun output current=>pure
    (((output,current),CborRecordWorldClient.advanceServer shell keyId plaintext),
      {control with server:=some {server with peers:=Function.update server.peers keyId (some {peer with kernel:=.hidden slot ready.advanced})}})
  have guarded := lookup_seal ready reserve after before (PqxdhDeploymentNative.serverTag (.inl (plaintext,keyId))) (by intros;trivial)
  simpa only [RegistrationNativePlatformOriginReserveContinuationBound.continued,after,ready,RawCtxChainSend.ready] using guarded

/-- The actual hidden Beacon source retains its assigned owner, advanced kernel and real reserve on every reply continuation. -/
theorem beacon_hidden (env : Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (before : Platform) (shell : CborRecordWorldClient.Shell) (control : Control n)
    (ownerIndex : Nat) (plaintext : Pqxdh.Bytes)
    (admitted : CborRecordWorldClient.refusal (n := n) (.inr (.inr (.inr (ownerIndex,.inl plaintext)))) shell=none)
    (beacon : PqxdhRecordLiftInterface.BeaconShell) (slot : PqxdhRecordLiftInterface.Slot n) (kernel : LabeledKernel n)
    (ownerAt : control.owners[ownerIndex]?=some (.established beacon (.hidden slot kernel)))
    (nonempty : plaintext.isEmpty=false)
    (pending : RawCtxChainSend.Kdf (Label n) (Label n) (Label n) RawCtxSourceSend.SealContext)
    (requested : RawCtxChainSend.normalBegin kernel
      ⟨plaintext,beacon.control.server_binding.identity_key_id,beacon.identityKeyId,PqxdhRefinement.absBytes beacon.associatedData⟩=.requested pending) :
    HasTails Platform Failure (source env reserve codec route (PqxdhDeploymentInterface.Spec.query (.inr (.beaconSend ownerIndex plaintext))) before shell control) := by
  simp only [source,simulateQ_spec_query]
  rw [RegistrationNativePlatformOriginSendEnvelope.beacon_hidden env reserve codec route before shell control ownerIndex plaintext
    admitted beacon slot kernel ownerAt nonempty pending requested]
  let ready := RawCtxChainSend.ready pending (PqxdhRecordLiftChainState.advance pending.request 1,pending.request)
  let after : Option RawCtxSourceSend.Encrypted → Platform → OracleComp (ServiceSpec n) _ := fun output current=>pure
    (((output,current),CborRecordWorldClient.advanceOwner shell ownerIndex plaintext),
      {control with owners:=control.owners.set ownerIndex (.established beacon (.hidden slot ready.advanced))})
  have guarded := lookup_seal ready reserve after before (PqxdhDeploymentNative.beaconTag ownerIndex) (by intros;trivial)
  simpa only [RegistrationNativePlatformOriginReserveContinuationBound.continued,after,ready,RawCtxChainSend.ready] using guarded

private theorem coins_quiet {X : Type} (work : ProbComp X) :
    (simulateQ (RegistrationNativePlatformOriginGateSource.coins (n := n)) work).AllQueriesSatisfy
      (fun request=>¬RegistrationNativePlatformOriginSourceTails.Sealing request) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,RegistrationNativePlatformOriginGateSource.coins,bind_assoc,allQueriesSatisfy_query_bind_iff]
    refine ⟨?_,fun _=>⟨?_,fun reply=>ih reply⟩⟩
    all_goals rintro ⟨pending,impossible⟩;cases impossible

private theorem gate_tails {X : Type} (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (before : Platform) (work : OracleComp (ServiceSpec n) (Option RawCtxSourceSend.Encrypted × Control n))
    (quiet : work.AllQueriesSatisfy (fun request=>¬RegistrationNativePlatformOriginSourceTails.Sealing request))
    (after : (Option RawCtxSourceSend.Encrypted × Platform) → Control n → X) :
    HasTails Platform Failure (do
      let sent ← work
      let gated ← simulateQ RegistrationNativePlatformOriginGateSource.coins
        ((RegistrationNativePlatformOrdinaryGate.gate reserve (fun value=>value.ciphertext.length) sent.1).run before)
      pure (after gated sent.2)) := by
  apply RegistrationNativePlatformOriginSourceTails.zero
  apply allQueriesSatisfy_bind quiet
  intro sent
  exact allQueriesSatisfy_bind (coins_quiet _) (fun _=>by trivial)

private theorem owner_empty (tag : PqxdhDeploymentInterface.FrameTag) (sender : U64) (decode : RawCtxReceive.FrameDecoder)
    (plaintext : Pqxdh.Bytes) (owner : PqxdhRecordLiftWorldCompiler.Owner n) (empty : plaintext.isEmpty=true) :
    (PqxdhRecordLiftProtocol.ownerRun tag sender decode (.inl plaintext) owner).AllQueriesSatisfy
      (fun request=>¬RegistrationNativePlatformOriginSourceTails.Sealing request) := by
  simp only [PqxdhRecordLiftProtocol.ownerRun,PqxdhRecordLiftProtocol.ownerStep,PqxdhRecordLiftProtocol.ownerSend,
    empty,ite_true,pure_bind,allQueriesSatisfy_query_bind_iff]
  refine ⟨?_,fun _=>by trivial⟩
  rintro ⟨pending,impossible⟩
  cases impossible

private theorem owner_known (tag : PqxdhDeploymentInterface.FrameTag) (sender : U64) (decode : RawCtxReceive.FrameDecoder)
    (plaintext : Pqxdh.Bytes) (owner : PqxdhRecordLiftWorldCompiler.Owner n)
    (kernel : beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel) (known : owner.kernel=.known kernel) :
    (PqxdhRecordLiftProtocol.ownerRun tag sender decode (.inl plaintext) owner).AllQueriesSatisfy
      (fun request=>¬RegistrationNativePlatformOriginSourceTails.Sealing request) := by
  cases empty : plaintext.isEmpty with
  | true => exact owner_empty tag sender decode plaintext owner empty
  | false =>
    simp only [PqxdhRecordLiftProtocol.ownerRun,PqxdhRecordLiftProtocol.ownerStep,PqxdhRecordLiftProtocol.ownerSend,
      empty,Bool.false_eq_true,ite_false,known,PqxdhRecordLiftProtocol.kernelSend,bind_assoc,pure_bind,allQueriesSatisfy_query_bind_iff]
    refine ⟨?_,fun _=>⟨?_,fun _=>by trivial⟩⟩
    all_goals rintro ⟨pending,impossible⟩;cases impossible

private theorem owner_exhausted (tag : PqxdhDeploymentInterface.FrameTag) (sender : U64) (decode : RawCtxReceive.FrameDecoder)
    (plaintext : Pqxdh.Bytes) (owner : PqxdhRecordLiftWorldCompiler.Owner n) (slot : PqxdhRecordLiftInterface.Slot n)
    (kernel : LabeledKernel n) (hidden : owner.kernel=.hidden slot kernel) (nonempty : plaintext.isEmpty=false)
    (entry : LabeledKernel n) (context : RawCtxSourceSend.SealContext)
    (stopped : RawCtxChainSend.normalBegin kernel ⟨plaintext,owner.expectedSender,sender,owner.associatedData⟩=.exhausted entry context) :
    (PqxdhRecordLiftProtocol.ownerRun tag sender decode (.inl plaintext) owner).AllQueriesSatisfy
      (fun request=>¬RegistrationNativePlatformOriginSourceTails.Sealing request) := by
  simp only [PqxdhRecordLiftProtocol.ownerRun,PqxdhRecordLiftProtocol.ownerStep,PqxdhRecordLiftProtocol.ownerSend,
    nonempty,Bool.false_eq_true,ite_false,hidden,PqxdhRecordLiftProtocol.kernelSend,PqxdhRecordLiftOpaqueDrivers.admittedSend,
    stopped,PqxdhRecordLiftOpaqueDrivers.sendProgram,simulateQ_pure,pure_bind,allQueriesSatisfy_query_bind_iff]
  refine ⟨?_,fun _=>by trivial⟩
  rintro ⟨pending,impossible⟩
  cases impossible

private theorem server_quiet (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (control : Control n) (server : Server n) (serverAt : control.server=some server)
    (keyId : U64) (peer : Peer n) (peerAt : server.peers keyId=some peer) (plaintext : Pqxdh.Bytes)
    (quiet : (PqxdhRecordLiftProtocol.ownerRun (PqxdhDeploymentNative.serverTag (.inl (plaintext,keyId))) server.sender codec.frameRead
      (.inl plaintext) (PqxdhRecordLiftWorldCompiler.serverOwner server keyId peer)).AllQueriesSatisfy
      (fun request=>¬RegistrationNativePlatformOriginSourceTails.Sealing request)) :
    ((PqxdhRecordLiftProtocol.serverStep codec.frameRead route (.inl (plaintext,keyId))).run control).AllQueriesSatisfy
      (fun request=>¬RegistrationNativePlatformOriginSourceTails.Sealing request) := by
  simp only [PqxdhRecordLiftProtocol.serverStep,StateT.run,serverAt,peerAt]
  exact allQueriesSatisfy_bind quiet (fun _=>by trivial)

/-- Every admitted Server branch has the actual charged source tail, including absence, known kernels and exhausted chains. -/
theorem server_admitted (env : Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (before : Platform) (shell : CborRecordWorldClient.Shell) (control : Control n)
    (keyId : U64) (plaintext : Pqxdh.Bytes)
    (admitted : CborRecordWorldClient.refusal (n := n) (.inr (.inr (.inl (.inl (plaintext,keyId))))) shell=none) :
    HasTails Platform Failure (source env reserve codec route (PqxdhDeploymentInterface.Spec.query (.inr (.serverSend keyId plaintext))) before shell control) := by
  have quietCase (quiet : ((PqxdhRecordLiftProtocol.serverStep codec.frameRead route (.inl (plaintext,keyId))).run control).AllQueriesSatisfy
      (fun request=>¬RegistrationNativePlatformOriginSourceTails.Sealing request)) :
      HasTails Platform Failure (source env reserve codec route (PqxdhDeploymentInterface.Spec.query (.inr (.serverSend keyId plaintext))) before shell control) := by
    simp only [source,simulateQ_spec_query]
    rw [RegistrationNativePlatformOriginSendEnvelope.server_source env reserve codec route before shell control keyId plaintext admitted]
    exact gate_tails reserve before _ quiet (fun gated current=>((gated,CborRecordWorldClient.advanceServer shell keyId plaintext),current))
  cases serverAt : control.server with
  | none =>
    apply quietCase
    simp only [PqxdhRecordLiftProtocol.serverStep,StateT.run,serverAt]
    trivial
  | some server => cases peerAt : server.peers keyId with
    | none =>
      apply quietCase
      simp only [PqxdhRecordLiftProtocol.serverStep,StateT.run,serverAt,peerAt]
      trivial
    | some peer =>
      cases empty : plaintext.isEmpty with
      | true =>
        exact quietCase (server_quiet codec route control server serverAt keyId peer peerAt plaintext
          (owner_empty _ _ _ _ _ empty))
      | false => cases stored : peer.kernel with
        | known kernel =>
          exact quietCase (server_quiet codec route control server serverAt keyId peer peerAt plaintext
            (owner_known _ _ _ _ _ kernel stored))
        | hidden slot kernel =>
          cases requested : RawCtxChainSend.normalBegin kernel
              (⟨plaintext,keyId,server.sender,(PqxdhRecordLiftWorldCompiler.serverOwner server keyId peer).associatedData⟩ : RawCtxSourceSend.SealContext) with
          | exhausted entry context =>
            exact quietCase (server_quiet codec route control server serverAt keyId peer peerAt plaintext
              (owner_exhausted _ _ _ _ _ slot kernel stored empty entry context requested))
          | requested pending =>
            exact server_hidden env reserve codec route before shell control keyId plaintext admitted server serverAt peer peerAt slot kernel stored empty pending requested

private theorem beacon_quiet (codec : Codec Reader Response) (control : Control n)
    (index : Nat) (beacon : PqxdhRecordLiftInterface.BeaconShell) (stored : PqxdhRecordLiftWorldCompiler.StoredKernel n)
    (ownerAt : control.owners[index]?=some (.established beacon stored)) (plaintext : Pqxdh.Bytes)
    (quiet : (PqxdhRecordLiftProtocol.ownerRun (PqxdhDeploymentNative.beaconTag index) beacon.identityKeyId codec.frameRead
      (.inl plaintext) (PqxdhRecordLiftWorldCompiler.beaconOwner beacon stored (control.ownerRaw index))).AllQueriesSatisfy
      (fun request=>¬RegistrationNativePlatformOriginSourceTails.Sealing request)) :
    ((PqxdhRecordLiftProtocol.beaconStep codec.frameRead index (.inl plaintext)).run control).AllQueriesSatisfy
      (fun request=>¬RegistrationNativePlatformOriginSourceTails.Sealing request) := by
  simp only [PqxdhRecordLiftProtocol.beaconStep,StateT.run,ownerAt]
  exact allQueriesSatisfy_bind quiet (fun _=>by trivial)

/-- Every admitted Beacon branch retains its actual charged tail, including missing and inactive owners and all chain outcomes. -/
theorem beacon_admitted (env : Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (before : Platform) (shell : CborRecordWorldClient.Shell) (control : Control n)
    (index : Nat) (plaintext : Pqxdh.Bytes)
    (admitted : CborRecordWorldClient.refusal (n := n) (.inr (.inr (.inr (index,.inl plaintext)))) shell=none) :
    HasTails Platform Failure (source env reserve codec route (PqxdhDeploymentInterface.Spec.query (.inr (.beaconSend index plaintext))) before shell control) := by
  have quietCase (quiet : ((PqxdhRecordLiftProtocol.beaconStep codec.frameRead index (.inl plaintext)).run control).AllQueriesSatisfy
      (fun request=>¬RegistrationNativePlatformOriginSourceTails.Sealing request)) :
      HasTails Platform Failure (source env reserve codec route (PqxdhDeploymentInterface.Spec.query (.inr (.beaconSend index plaintext))) before shell control) := by
    simp only [source,simulateQ_spec_query]
    rw [RegistrationNativePlatformOriginSendEnvelope.beacon_source env reserve codec route before shell control index plaintext admitted]
    exact gate_tails reserve before _ quiet (fun gated current=>((gated,CborRecordWorldClient.advanceOwner shell index plaintext),current))
  cases ownerAt : control.owners[index]? with
  | none =>
    apply quietCase
    simp only [PqxdhRecordLiftProtocol.beaconStep,StateT.run,ownerAt,PqxdhDeploymentNative.absent]
    trivial
  | some phase => cases phase with
    | inactive phase =>
      apply quietCase
      simp only [PqxdhRecordLiftProtocol.beaconStep,StateT.run,ownerAt]
      trivial
    | established beacon stored =>
      cases empty : plaintext.isEmpty with
      | true =>
        exact quietCase (beacon_quiet codec control index beacon stored ownerAt plaintext (owner_empty _ _ _ _ _ empty))
      | false => cases stored with
        | known kernel =>
          exact quietCase (beacon_quiet codec control index beacon (.known kernel) ownerAt plaintext (owner_known _ _ _ _ _ kernel rfl))
        | hidden slot kernel =>
          cases requested : RawCtxChainSend.normalBegin kernel
              (⟨plaintext,beacon.control.server_binding.identity_key_id,beacon.identityKeyId,PqxdhRefinement.absBytes beacon.associatedData⟩ : RawCtxSourceSend.SealContext) with
          | exhausted entry context =>
            exact quietCase (beacon_quiet codec control index beacon (.hidden slot kernel) ownerAt plaintext
              (owner_exhausted _ _ _ _ _ slot kernel rfl empty entry context requested))
          | requested pending =>
            exact beacon_hidden env reserve codec route before shell control index plaintext admitted beacon slot kernel ownerAt empty pending requested

private theorem server_refused (env : Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (before : Platform) (shell : CborRecordWorldClient.Shell) (control : Control n)
    (keyId : U64) (plaintext : Pqxdh.Bytes) (denied : Option RawCtxSourceSend.Encrypted)
    (refused : CborRecordWorldClient.refusal (n := n) (.inr (.inr (.inl (.inl (plaintext,keyId))))) shell=some denied) :
    HasTails Platform Failure (source env reserve codec route (PqxdhDeploymentInterface.Spec.query (.inr (.serverSend keyId plaintext))) before shell control) := by
  have equation : source env reserve codec route (PqxdhDeploymentInterface.Spec.query (.inr (.serverSend keyId plaintext))) before shell control=
      (fun result=>((result,shell),control)) <$>
        simulateQ RegistrationNativePlatformOriginGateSource.coins
          ((RegistrationNativePlatformOrdinaryGate.gate reserve (fun value : RawCtxSourceSend.Encrypted=>value.ciphertext.length) denied).run before) := by
    simp only [source,simulateQ_spec_query]
    change ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
      ((simulateQ CborRecordWorldClient.handler
        (do let reply ← ((WorldSpec n).query (.inr (.inr (.inl (.inl (plaintext,keyId))))) : OracleComp (WorldSpec n) (Option RawCtxSourceSend.Encrypted))
            simulateQ PqxdhRecordLiftInterface.coinLift
              ((RegistrationNativePlatformOrdinaryGate.gate reserve (fun value=>value.ciphertext.length) reply).run before))).run shell)).run control)=_
    simp only [simulateQ_bind,StateT.run_bind,simulateQ_spec_query]
    rw [show (CborRecordWorldClient.handler (n := n) (.inr (.inr (.inl (.inl (plaintext,keyId)))))).run shell=pure (denied,shell) by
      simp only [CborRecordWorldClient.handler,StateT.run,refused]]
    simp only [simulateQ_pure,StateT.run_pure,pure_bind]
    exact RegistrationNativePlatformOriginGateSource.closed_program _ codec route shell control
  rw [equation]
  exact RegistrationNativePlatformOriginSourceTails.map _ _ (RegistrationNativePlatformOriginSourceTails.zero _ (coins_quiet _))

private theorem beacon_refused (env : Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (before : Platform) (shell : CborRecordWorldClient.Shell) (control : Control n)
    (index : Nat) (plaintext : Pqxdh.Bytes) (denied : Option RawCtxSourceSend.Encrypted)
    (refused : CborRecordWorldClient.refusal (n := n) (.inr (.inr (.inr (index,.inl plaintext)))) shell=some denied) :
    HasTails Platform Failure (source env reserve codec route (PqxdhDeploymentInterface.Spec.query (.inr (.beaconSend index plaintext))) before shell control) := by
  have equation : source env reserve codec route (PqxdhDeploymentInterface.Spec.query (.inr (.beaconSend index plaintext))) before shell control=
      (fun result=>((result,shell),control)) <$>
        simulateQ RegistrationNativePlatformOriginGateSource.coins
          ((RegistrationNativePlatformOrdinaryGate.gate reserve (fun value : RawCtxSourceSend.Encrypted=>value.ciphertext.length) denied).run before) := by
    simp only [source,simulateQ_spec_query]
    change ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
      ((simulateQ CborRecordWorldClient.handler
        (do let reply ← ((WorldSpec n).query (.inr (.inr (.inr (index,.inl plaintext)))) : OracleComp (WorldSpec n) (Option RawCtxSourceSend.Encrypted))
            simulateQ PqxdhRecordLiftInterface.coinLift
              ((RegistrationNativePlatformOrdinaryGate.gate reserve (fun value=>value.ciphertext.length) reply).run before))).run shell)).run control)=_
    simp only [simulateQ_bind,StateT.run_bind,simulateQ_spec_query]
    rw [show (CborRecordWorldClient.handler (n := n) (.inr (.inr (.inr (index,.inl plaintext))))).run shell=pure (denied,shell) by
      simp only [CborRecordWorldClient.handler,StateT.run,refused]]
    simp only [simulateQ_pure,StateT.run_pure,pure_bind]
    exact RegistrationNativePlatformOriginGateSource.closed_program _ codec route shell control
  rw [equation]
  exact RegistrationNativePlatformOriginSourceTails.map _ _ (RegistrationNativePlatformOriginSourceTails.zero _ (coins_quiet _))

/-- Every literal native callback has only its actual publication/reserve continuation after a hidden seal. -/
theorem query (env : Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (request : PqxdhDeploymentInterface.Spec.Domain)
    (before : Platform) (shell : CborRecordWorldClient.Shell) (control : Control n) :
    HasTails Platform Failure (source env reserve codec route (PqxdhDeploymentInterface.Spec.query request) before shell control) := by
  classical
  by_cases quiet : ¬NativeRecord .send request
  · exact non_send_tails env reserve codec route request quiet before shell control
  · cases request with
    | inl coin => exact (quiet (by simp [NativeRecord,PqxdhDeploymentCompileBudget.commandKind])).elim
    | inr command => cases command with
      | serverSend keyId plaintext =>
        cases refused : CborRecordWorldClient.refusal (n := n) (.inr (.inr (.inl (.inl (plaintext,keyId))))) shell with
        | none => exact server_admitted env reserve codec route before shell control keyId plaintext refused
        | some denied => exact server_refused env reserve codec route before shell control keyId plaintext denied refused
      | beaconSend index plaintext =>
        cases refused : CborRecordWorldClient.refusal (n := n) (.inr (.inr (.inr (index,.inl plaintext)))) shell with
        | none => exact beacon_admitted env reserve codec route before shell control index plaintext refused
        | some denied => exact beacon_refused env reserve codec route before shell control index plaintext denied refused
      | _ => exact (quiet (by simp [NativeRecord,PqxdhDeploymentCompileBudget.commandKind])).elim

/-- The entire actual adaptive native source retains its original stateful reserve tails and all reached platform, cursor and control coordinates. -/
theorem program (env : Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp PqxdhDeploymentInterface.Spec A)
    (before : Platform) (shell : CborRecordWorldClient.Shell) (control : Control n) :
    HasTails Platform Failure (source env reserve codec route work before shell control) := by
  induction work using OracleComp.inductionOn generalizing before shell control with
  | pure value => rw [source_pure];trivial
  | query_bind request next ih =>
    rw [source_bind]
    exact RegistrationNativePlatformOriginSourceTails.bind _ _
      (query env reserve codec route request before shell control)
      (fun result=>ih result.1.1.1 result.1.1.2 result.1.2 result.2)

/-- The literal hidden send has one material lookup and sealing request, followed by the actual public publication and reserve and a pure returned full state. -/
noncomputable def Envelope {X : Type}
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (before : Platform) (work : OracleComp (ServiceSpec n) X) : Prop :=
  ∃ (pending : PqxdhRecordLiftProtocol.Sealing n) (tag : PqxdhDeploymentInterface.FrameTag)
    (after : Option RawCtxSourceSend.Encrypted → Platform → X),work=(do
      let _ ← ((ServiceSpec n).query (.lookup pending.material) : OracleComp (ServiceSpec n) _)
      let reply ← ((ServiceSpec n).query (.sealing pending) : OracleComp (ServiceSpec n) _)
      RegistrationNativePlatformOriginReserveContinuationBound.continued reserve (fun output state=>pure (after output state)) before tag reply)

/-- The actual optional native reply and platform result are returned unchanged after the genuine reserve, with cursor/control fixed before the sealing reply. -/
noncomputable def ReplyEnvelope
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (before : Platform)
    (work : OracleComp (ServiceSpec n)
      (((Option RawCtxSourceSend.Encrypted × Platform) × CborRecordWorldClient.Shell) × Control n)) : Prop :=
  ∃ (pending : PqxdhRecordLiftProtocol.Sealing n) (tag : PqxdhDeploymentInterface.FrameTag)
    (shell : CborRecordWorldClient.Shell) (control : Control n),work=(do
      let _ ← ((ServiceSpec n).query (.lookup pending.material) : OracleComp (ServiceSpec n) _)
      let reply ← ((ServiceSpec n).query (.sealing pending) : OracleComp (ServiceSpec n) _)
      RegistrationNativePlatformOriginReserveContinuationBound.continued reserve
        (fun output state=>pure (((output,state),shell),control)) before tag reply)
private theorem reply_forget
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure)) (before : Platform)
    (work : OracleComp (ServiceSpec n)
      (((Option RawCtxSourceSend.Encrypted × Platform) × CborRecordWorldClient.Shell) × Control n))
    (form : ReplyEnvelope reserve before work) : Envelope reserve before work := by
  obtain ⟨pending,tag,shell,control,form⟩ := form
  exact ⟨pending,tag,(fun output state=>(((output,state),shell),control)),form⟩

private theorem server_form_hidden (env : Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (before : Platform) (shell : CborRecordWorldClient.Shell) (control : Control n)
    (keyId : U64) (plaintext : Pqxdh.Bytes)
    (admitted : CborRecordWorldClient.refusal (n := n) (.inr (.inr (.inl (.inl (plaintext,keyId))))) shell=none)
    (server : Server n) (serverAt : control.server=some server) (peer : Peer n) (peerAt : server.peers keyId=some peer)
    (slot : PqxdhRecordLiftInterface.Slot n) (kernel : LabeledKernel n) (hidden : peer.kernel=.hidden slot kernel)
    (nonempty : plaintext.isEmpty=false)
    (pending : RawCtxChainSend.Kdf (Label n) (Label n) (Label n) RawCtxSourceSend.SealContext)
    (requested : RawCtxChainSend.normalBegin kernel
      ⟨plaintext,keyId,server.sender,(PqxdhRecordLiftWorldCompiler.serverOwner server keyId peer).associatedData⟩=.requested pending) :
    ReplyEnvelope reserve before (source env reserve codec route (PqxdhDeploymentInterface.Spec.query (.inr (.serverSend keyId plaintext))) before shell control) := by
  let ready := RawCtxChainSend.ready pending (PqxdhRecordLiftChainState.advance pending.request 1,pending.request)
  let after : Option RawCtxSourceSend.Encrypted → Platform → _ := fun output current=>
    (((output,current),CborRecordWorldClient.advanceServer shell keyId plaintext),
      {control with server:=some {server with peers:=Function.update server.peers keyId (some {peer with kernel:=.hidden slot ready.advanced})}})
  refine ⟨ready,(PqxdhDeploymentNative.serverTag (.inl (plaintext,keyId))),(after none before).1.2,(after none before).2,?_⟩
  simp only [source,simulateQ_spec_query]
  rw [RegistrationNativePlatformOriginSendEnvelope.server_hidden env reserve codec route before shell control keyId plaintext
    admitted server serverAt peer peerAt slot kernel hidden nonempty pending requested]
  rfl

private theorem beacon_form_hidden (env : Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (before : Platform) (shell : CborRecordWorldClient.Shell) (control : Control n)
    (ownerIndex : Nat) (plaintext : Pqxdh.Bytes)
    (admitted : CborRecordWorldClient.refusal (n := n) (.inr (.inr (.inr (ownerIndex,.inl plaintext)))) shell=none)
    (beacon : PqxdhRecordLiftInterface.BeaconShell) (slot : PqxdhRecordLiftInterface.Slot n) (kernel : LabeledKernel n)
    (ownerAt : control.owners[ownerIndex]?=some (.established beacon (.hidden slot kernel)))
    (nonempty : plaintext.isEmpty=false)
    (pending : RawCtxChainSend.Kdf (Label n) (Label n) (Label n) RawCtxSourceSend.SealContext)
    (requested : RawCtxChainSend.normalBegin kernel
      ⟨plaintext,beacon.control.server_binding.identity_key_id,beacon.identityKeyId,PqxdhRefinement.absBytes beacon.associatedData⟩=.requested pending) :
    ReplyEnvelope reserve before (source env reserve codec route (PqxdhDeploymentInterface.Spec.query (.inr (.beaconSend ownerIndex plaintext))) before shell control) := by
  let ready := RawCtxChainSend.ready pending (PqxdhRecordLiftChainState.advance pending.request 1,pending.request)
  let after : Option RawCtxSourceSend.Encrypted → Platform → _ := fun output current=>
    (((output,current),CborRecordWorldClient.advanceOwner shell ownerIndex plaintext),
      {control with owners:=control.owners.set ownerIndex (.established beacon (.hidden slot ready.advanced))})
  refine ⟨ready,(PqxdhDeploymentNative.beaconTag ownerIndex),(after none before).1.2,(after none before).2,?_⟩
  simp only [source,simulateQ_spec_query]
  rw [RegistrationNativePlatformOriginSendEnvelope.beacon_hidden env reserve codec route before shell control ownerIndex plaintext
    admitted beacon slot kernel ownerAt nonempty pending requested]
  rfl

private theorem server_form_admitted (env : Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (before : Platform) (shell : CborRecordWorldClient.Shell) (control : Control n)
    (keyId : U64) (plaintext : Pqxdh.Bytes)
    (admitted : CborRecordWorldClient.refusal (n := n) (.inr (.inr (.inl (.inl (plaintext,keyId))))) shell=none) :
    (source env reserve codec route (PqxdhDeploymentInterface.Spec.query (.inr (.serverSend keyId plaintext))) before shell control).AllQueriesSatisfy (fun request=>¬RegistrationNativePlatformOriginSourceTails.Sealing request) ∨ ReplyEnvelope reserve before (source env reserve codec route (PqxdhDeploymentInterface.Spec.query (.inr (.serverSend keyId plaintext))) before shell control) := by
  have quietCase (quiet : ((PqxdhRecordLiftProtocol.serverStep codec.frameRead route (.inl (plaintext,keyId))).run control).AllQueriesSatisfy
      (fun request=>¬RegistrationNativePlatformOriginSourceTails.Sealing request)) :
      (source env reserve codec route (PqxdhDeploymentInterface.Spec.query (.inr (.serverSend keyId plaintext))) before shell control).AllQueriesSatisfy (fun request=>¬RegistrationNativePlatformOriginSourceTails.Sealing request) ∨ ReplyEnvelope reserve before (source env reserve codec route (PqxdhDeploymentInterface.Spec.query (.inr (.serverSend keyId plaintext))) before shell control) := by
    apply Or.inl
    simp only [source,simulateQ_spec_query]
    rw [RegistrationNativePlatformOriginSendEnvelope.server_source env reserve codec route before shell control keyId plaintext admitted]
    exact allQueriesSatisfy_bind quiet (fun sent=>
      allQueriesSatisfy_bind (coins_quiet _) (fun gated=>by trivial))
  cases serverAt : control.server with
  | none =>
    apply quietCase
    simp only [PqxdhRecordLiftProtocol.serverStep,StateT.run,serverAt]
    trivial
  | some server => cases peerAt : server.peers keyId with
    | none =>
      apply quietCase
      simp only [PqxdhRecordLiftProtocol.serverStep,StateT.run,serverAt,peerAt]
      trivial
    | some peer =>
      cases empty : plaintext.isEmpty with
      | true =>
        exact quietCase (server_quiet codec route control server serverAt keyId peer peerAt plaintext
          (owner_empty _ _ _ _ _ empty))
      | false => cases stored : peer.kernel with
        | known kernel =>
          exact quietCase (server_quiet codec route control server serverAt keyId peer peerAt plaintext
            (owner_known _ _ _ _ _ kernel stored))
        | hidden slot kernel =>
          cases requested : RawCtxChainSend.normalBegin kernel
              (⟨plaintext,keyId,server.sender,(PqxdhRecordLiftWorldCompiler.serverOwner server keyId peer).associatedData⟩ : RawCtxSourceSend.SealContext) with
          | exhausted entry context =>
            exact quietCase (server_quiet codec route control server serverAt keyId peer peerAt plaintext
              (owner_exhausted _ _ _ _ _ slot kernel stored empty entry context requested))
          | requested pending =>
            exact Or.inr (server_form_hidden env reserve codec route before shell control keyId plaintext admitted server serverAt peer peerAt slot kernel stored empty pending requested)

private theorem beacon_form_admitted (env : Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (before : Platform) (shell : CborRecordWorldClient.Shell) (control : Control n)
    (index : Nat) (plaintext : Pqxdh.Bytes)
    (admitted : CborRecordWorldClient.refusal (n := n) (.inr (.inr (.inr (index,.inl plaintext)))) shell=none) :
    (source env reserve codec route (PqxdhDeploymentInterface.Spec.query (.inr (.beaconSend index plaintext))) before shell control).AllQueriesSatisfy (fun request=>¬RegistrationNativePlatformOriginSourceTails.Sealing request) ∨ ReplyEnvelope reserve before (source env reserve codec route (PqxdhDeploymentInterface.Spec.query (.inr (.beaconSend index plaintext))) before shell control) := by
  have quietCase (quiet : ((PqxdhRecordLiftProtocol.beaconStep codec.frameRead index (.inl plaintext)).run control).AllQueriesSatisfy
      (fun request=>¬RegistrationNativePlatformOriginSourceTails.Sealing request)) :
      (source env reserve codec route (PqxdhDeploymentInterface.Spec.query (.inr (.beaconSend index plaintext))) before shell control).AllQueriesSatisfy (fun request=>¬RegistrationNativePlatformOriginSourceTails.Sealing request) ∨ ReplyEnvelope reserve before (source env reserve codec route (PqxdhDeploymentInterface.Spec.query (.inr (.beaconSend index plaintext))) before shell control) := by
    apply Or.inl
    simp only [source,simulateQ_spec_query]
    rw [RegistrationNativePlatformOriginSendEnvelope.beacon_source env reserve codec route before shell control index plaintext admitted]
    exact allQueriesSatisfy_bind quiet (fun sent=>
      allQueriesSatisfy_bind (coins_quiet _) (fun gated=>by trivial))
  cases ownerAt : control.owners[index]? with
  | none =>
    apply quietCase
    simp only [PqxdhRecordLiftProtocol.beaconStep,StateT.run,ownerAt,PqxdhDeploymentNative.absent]
    trivial
  | some phase => cases phase with
    | inactive phase =>
      apply quietCase
      simp only [PqxdhRecordLiftProtocol.beaconStep,StateT.run,ownerAt]
      trivial
    | established beacon stored =>
      cases empty : plaintext.isEmpty with
      | true =>
        exact quietCase (beacon_quiet codec control index beacon stored ownerAt plaintext (owner_empty _ _ _ _ _ empty))
      | false => cases stored with
        | known kernel =>
          exact quietCase (beacon_quiet codec control index beacon (.known kernel) ownerAt plaintext (owner_known _ _ _ _ _ kernel rfl))
        | hidden slot kernel =>
          cases requested : RawCtxChainSend.normalBegin kernel
              (⟨plaintext,beacon.control.server_binding.identity_key_id,beacon.identityKeyId,PqxdhRefinement.absBytes beacon.associatedData⟩ : RawCtxSourceSend.SealContext) with
          | exhausted entry context =>
            exact quietCase (beacon_quiet codec control index beacon (.hidden slot kernel) ownerAt plaintext
              (owner_exhausted _ _ _ _ _ slot kernel rfl empty entry context requested))
          | requested pending =>
            exact Or.inr (beacon_form_hidden env reserve codec route before shell control index plaintext admitted beacon slot kernel ownerAt empty pending requested)

private theorem server_form_refused (env : Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (before : Platform) (shell : CborRecordWorldClient.Shell) (control : Control n)
    (keyId : U64) (plaintext : Pqxdh.Bytes) (denied : Option RawCtxSourceSend.Encrypted)
    (refused : CborRecordWorldClient.refusal (n := n) (.inr (.inr (.inl (.inl (plaintext,keyId))))) shell=some denied) :
    (source env reserve codec route (PqxdhDeploymentInterface.Spec.query (.inr (.serverSend keyId plaintext))) before shell control).AllQueriesSatisfy (fun request=>¬RegistrationNativePlatformOriginSourceTails.Sealing request) := by
  have equation : source env reserve codec route (PqxdhDeploymentInterface.Spec.query (.inr (.serverSend keyId plaintext))) before shell control=
      (fun result=>((result,shell),control)) <$>
        simulateQ RegistrationNativePlatformOriginGateSource.coins
          ((RegistrationNativePlatformOrdinaryGate.gate reserve (fun value : RawCtxSourceSend.Encrypted=>value.ciphertext.length) denied).run before) := by
    simp only [source,simulateQ_spec_query]
    change ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
      ((simulateQ CborRecordWorldClient.handler
        (do let reply ← ((WorldSpec n).query (.inr (.inr (.inl (.inl (plaintext,keyId))))) : OracleComp (WorldSpec n) (Option RawCtxSourceSend.Encrypted))
            simulateQ PqxdhRecordLiftInterface.coinLift
              ((RegistrationNativePlatformOrdinaryGate.gate reserve (fun value=>value.ciphertext.length) reply).run before))).run shell)).run control)=_
    simp only [simulateQ_bind,StateT.run_bind,simulateQ_spec_query]
    rw [show (CborRecordWorldClient.handler (n := n) (.inr (.inr (.inl (.inl (plaintext,keyId)))))).run shell=pure (denied,shell) by
      simp only [CborRecordWorldClient.handler,StateT.run,refused]]
    simp only [simulateQ_pure,StateT.run_pure,pure_bind]
    exact RegistrationNativePlatformOriginGateSource.closed_program _ codec route shell control
  rw [equation]
  simpa only [bind_pure_comp] using
    allQueriesSatisfy_bind (coins_quiet _) (fun result=>allQueriesSatisfy_pure _ _)

private theorem beacon_form_refused (env : Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (before : Platform) (shell : CborRecordWorldClient.Shell) (control : Control n)
    (index : Nat) (plaintext : Pqxdh.Bytes) (denied : Option RawCtxSourceSend.Encrypted)
    (refused : CborRecordWorldClient.refusal (n := n) (.inr (.inr (.inr (index,.inl plaintext)))) shell=some denied) :
    (source env reserve codec route (PqxdhDeploymentInterface.Spec.query (.inr (.beaconSend index plaintext))) before shell control).AllQueriesSatisfy (fun request=>¬RegistrationNativePlatformOriginSourceTails.Sealing request) := by
  have equation : source env reserve codec route (PqxdhDeploymentInterface.Spec.query (.inr (.beaconSend index plaintext))) before shell control=
      (fun result=>((result,shell),control)) <$>
        simulateQ RegistrationNativePlatformOriginGateSource.coins
          ((RegistrationNativePlatformOrdinaryGate.gate reserve (fun value : RawCtxSourceSend.Encrypted=>value.ciphertext.length) denied).run before) := by
    simp only [source,simulateQ_spec_query]
    change ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
      ((simulateQ CborRecordWorldClient.handler
        (do let reply ← ((WorldSpec n).query (.inr (.inr (.inr (index,.inl plaintext)))) : OracleComp (WorldSpec n) (Option RawCtxSourceSend.Encrypted))
            simulateQ PqxdhRecordLiftInterface.coinLift
              ((RegistrationNativePlatformOrdinaryGate.gate reserve (fun value=>value.ciphertext.length) reply).run before))).run shell)).run control)=_
    simp only [simulateQ_bind,StateT.run_bind,simulateQ_spec_query]
    rw [show (CborRecordWorldClient.handler (n := n) (.inr (.inr (.inr (index,.inl plaintext))))).run shell=pure (denied,shell) by
      simp only [CborRecordWorldClient.handler,StateT.run,refused]]
    simp only [simulateQ_pure,StateT.run_pure,pure_bind]
    exact RegistrationNativePlatformOriginGateSource.closed_program _ codec route shell control
  rw [equation]
  simpa only [bind_pure_comp] using
    allQueriesSatisfy_bind (coins_quiet _) (fun result=>allQueriesSatisfy_pure _ _)


/-- Every actual Server send is either structurally nonsealing or its literal hidden requested-send reserve envelope, including all refusal and failure branches. -/
theorem server_form (env : Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (before : Platform) (shell : CborRecordWorldClient.Shell) (control : Control n)
    (keyId : U64) (plaintext : Pqxdh.Bytes) :
    (source env reserve codec route (PqxdhDeploymentInterface.Spec.query (.inr (.serverSend keyId plaintext))) before shell control).AllQueriesSatisfy
      (fun request=>¬RegistrationNativePlatformOriginSourceTails.Sealing request) ∨
    Envelope reserve before (source env reserve codec route (PqxdhDeploymentInterface.Spec.query (.inr (.serverSend keyId plaintext))) before shell control) := by
  cases refused : CborRecordWorldClient.refusal (n := n) (.inr (.inr (.inl (.inl (plaintext,keyId))))) shell with
  | none=>
    rcases server_form_admitted env reserve codec route before shell control keyId plaintext refused with quiet|form
    · exact Or.inl quiet
    · exact Or.inr (reply_forget reserve before _ form)
  | some denied=>exact Or.inl (server_form_refused env reserve codec route before shell control keyId plaintext denied refused)


/-- Every actual Beacon send is either structurally nonsealing or its literal hidden requested-send reserve envelope, including all refusal and failure branches. -/
theorem beacon_form (env : Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (before : Platform) (shell : CborRecordWorldClient.Shell) (control : Control n)
    (index : Nat) (plaintext : Pqxdh.Bytes) :
    (source env reserve codec route (PqxdhDeploymentInterface.Spec.query (.inr (.beaconSend index plaintext))) before shell control).AllQueriesSatisfy
      (fun request=>¬RegistrationNativePlatformOriginSourceTails.Sealing request) ∨
    Envelope reserve before (source env reserve codec route (PqxdhDeploymentInterface.Spec.query (.inr (.beaconSend index plaintext))) before shell control) := by
  cases refused : CborRecordWorldClient.refusal (n := n) (.inr (.inr (.inr (index,.inl plaintext)))) shell with
  | none=>
    rcases beacon_form_admitted env reserve codec route before shell control index plaintext refused with quiet|form
    · exact Or.inl quiet
    · exact Or.inr (reply_forget reserve before _ form)
  | some denied=>exact Or.inl (beacon_form_refused env reserve codec route before shell control index plaintext denied refused)


/-- The entire literal native callback is nonsealing or has exactly one hidden seal followed by its actual reserve and complete returned states. -/
theorem normalform (env : Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (query : PqxdhDeploymentInterface.Spec.Domain)
    (before : Platform) (shell : CborRecordWorldClient.Shell) (control : Control n) :
    (source env reserve codec route (PqxdhDeploymentInterface.Spec.query query) before shell control).AllQueriesSatisfy
      (fun request=>¬RegistrationNativePlatformOriginSourceTails.Sealing request) ∨
    Envelope reserve before (source env reserve codec route (PqxdhDeploymentInterface.Spec.query query) before shell control) := by
  classical
  by_cases quiet : ¬NativeRecord .send query
  · apply Or.inl
    simp only [source,simulateQ_spec_query]
    apply (non_send env reserve codec route query quiet before shell control).mono
    rintro request absent ⟨pending,equal⟩
    exact absent pending equal
  · cases query with
    | inl coin=>exact (quiet (by simp [NativeRecord,PqxdhDeploymentCompileBudget.commandKind])).elim
    | inr command=>cases command with
      | serverSend keyId plaintext=>exact server_form env reserve codec route before shell control keyId plaintext
      | beaconSend index plaintext=>exact beacon_form env reserve codec route before shell control index plaintext
      | _=>exact (quiet (by simp [NativeRecord,PqxdhDeploymentCompileBudget.commandKind])).elim

theorem server_reply_form (env : Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (before : Platform) (shell : CborRecordWorldClient.Shell) (control : Control n)
    (keyId : U64) (plaintext : Pqxdh.Bytes) :
    (source env reserve codec route (PqxdhDeploymentInterface.Spec.query (.inr (.serverSend keyId plaintext))) before shell control).AllQueriesSatisfy
      (fun request=>¬RegistrationNativePlatformOriginSourceTails.Sealing request) ∨
    ReplyEnvelope reserve before (source env reserve codec route (PqxdhDeploymentInterface.Spec.query (.inr (.serverSend keyId plaintext))) before shell control) := by
  cases refused : CborRecordWorldClient.refusal (n := n) (.inr (.inr (.inl (.inl (plaintext,keyId))))) shell with
  | none=>exact server_form_admitted env reserve codec route before shell control keyId plaintext refused
  | some denied=>exact Or.inl (server_form_refused env reserve codec route before shell control keyId plaintext denied refused)


theorem beacon_reply_form (env : Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (before : Platform) (shell : CborRecordWorldClient.Shell) (control : Control n)
    (index : Nat) (plaintext : Pqxdh.Bytes) :
    (source env reserve codec route (PqxdhDeploymentInterface.Spec.query (.inr (.beaconSend index plaintext))) before shell control).AllQueriesSatisfy
      (fun request=>¬RegistrationNativePlatformOriginSourceTails.Sealing request) ∨
    ReplyEnvelope reserve before (source env reserve codec route (PqxdhDeploymentInterface.Spec.query (.inr (.beaconSend index plaintext))) before shell control) := by
  cases refused : CborRecordWorldClient.refusal (n := n) (.inr (.inr (.inr (index,.inl plaintext)))) shell with
  | none=>exact beacon_form_admitted env reserve codec route before shell control index plaintext refused
  | some denied=>exact Or.inl (beacon_form_refused env reserve codec route before shell control index plaintext denied refused)


end BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeTails

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeTails.non_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeTails.non_send

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeTails.non_send_tails' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeTails.non_send_tails

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeTails.server_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeTails.server_hidden

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeTails.beacon_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeTails.beacon_hidden

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeTails.server_admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeTails.server_admitted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeTails.beacon_admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeTails.beacon_admitted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeTails.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeTails.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeTails.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeTails.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeTails.server_form' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeTails.server_form

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeTails.beacon_form' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeTails.beacon_form

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeTails.normalform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeTails.normalform

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeTails.server_reply_form' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeTails.server_reply_form

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeTails.beacon_reply_form' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginNativeTails.beacon_reply_form
