-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendSource
/-! Exact actual native send, public CBOR admission and source Protocol envelopes retain advanced Control, Shell and platform state through the genuine post-seal reserve. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendEnvelope
open PqxdhRecordLiftInterface (Environment WorldSpec)
open PqxdhRecordLiftProtocol (ServiceSpec Control)
open PqxdhRecordLiftWorldCompiler (Label LabeledKernel Owner Server Peer)
open PqxdhRecordLiftChainState (advance)
open PqxdhServerAuthExperiment (Codec)
variable {n : Nat} {Platform Failure Reader Response X : Type}

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before=Prod.map change id <$> work before := StateT.run_map change work before

/-- The actual public CBOR envelope and terminal reserve retain the original send's advanced source control and public cursor, including absent ciphertext and Err. -/
theorem server_source (env : Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (before : Platform) (shell : CborRecordWorldClient.Shell) (control : Control n)
    (keyId : Std.U64) (plaintext : Pqxdh.Bytes)
    (admitted : CborRecordWorldClient.refusal (n := n) (.inr (.inr (.inl (.inl (plaintext,keyId))))) shell=none) :
    ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
      ((simulateQ CborRecordWorldClient.handler
        ((RegistrationNativePlatformGatedRecordInterface.native env reserve (.inr (.serverSend keyId plaintext))).run before)).run shell)).run control)=
      (do
        let sent ← (PqxdhRecordLiftProtocol.serverStep codec.frameRead route (.inl (plaintext,keyId))).run control
        let gated ← simulateQ RegistrationNativePlatformOriginGateSource.coins
          ((RegistrationNativePlatformOrdinaryGate.gate reserve (fun value : RawCtxSourceSend.Encrypted=>value.ciphertext.length) sent.1).run before)
        pure ((gated,CborRecordWorldClient.advanceServer shell keyId plaintext),sent.2)) := by
  change ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
    ((simulateQ CborRecordWorldClient.handler
      (do let reply ← ((WorldSpec n).query (.inr (.inr (.inl (.inl (plaintext,keyId))))) : OracleComp (WorldSpec n) (Option RawCtxSourceSend.Encrypted))
          simulateQ PqxdhRecordLiftInterface.coinLift
            ((RegistrationNativePlatformOrdinaryGate.gate reserve (fun value : RawCtxSourceSend.Encrypted=>value.ciphertext.length) reply).run before))).run shell)).run control)=_
  simp only [simulateQ_bind,StateT.run_bind,simulateQ_spec_query]
  rw [show (CborRecordWorldClient.handler (n := n) (.inr (.inr (.inl (.inl (plaintext,keyId)))))).run shell=
    CborRecordWorldClient.forward (n := n) (.inr (.inr (.inl (.inl (plaintext,keyId))))) shell by
      simp only [CborRecordWorldClient.handler,StateT.run,admitted]]
  simp only [CborRecordWorldClient.forward,simulateQ_map,StateT.run_map,simulateQ_spec_query,bind_map_left]
  change (do
    let sent ← (PqxdhRecordLiftProtocol.serverStep codec.frameRead route (.inl (plaintext,keyId))).run control
    ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
      ((simulateQ CborRecordWorldClient.handler (simulateQ PqxdhRecordLiftInterface.coinLift
        ((RegistrationNativePlatformOrdinaryGate.gate reserve (fun value : RawCtxSourceSend.Encrypted=>value.ciphertext.length) sent.1).run before))).run
          (CborRecordWorldClient.advanceServer shell keyId plaintext))).run sent.2))=_
  apply bind_congr
  intro sent
  simpa only [bind_pure_comp] using RegistrationNativePlatformOriginGateSource.closed_program
    ((RegistrationNativePlatformOrdinaryGate.gate reserve (fun value : RawCtxSourceSend.Encrypted=>value.ciphertext.length) sent.1).run before)
      codec route (CborRecordWorldClient.advanceServer shell keyId plaintext) sent.2
/-- The actual public CBOR envelope and terminal reserve retain the original send's advanced source control and public cursor, including absent ciphertext and Err. -/
theorem beacon_source (env : Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (before : Platform) (shell : CborRecordWorldClient.Shell) (control : Control n)
    (ownerIndex : Nat) (plaintext : Pqxdh.Bytes)
    (admitted : CborRecordWorldClient.refusal (n := n) (.inr (.inr (.inr (ownerIndex,.inl plaintext)))) shell=none) :
    ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
      ((simulateQ CborRecordWorldClient.handler
        ((RegistrationNativePlatformGatedRecordInterface.native env reserve (.inr (.beaconSend ownerIndex plaintext))).run before)).run shell)).run control)=
      (do
        let sent ← (PqxdhRecordLiftProtocol.beaconStep codec.frameRead ownerIndex (.inl plaintext)).run control
        let gated ← simulateQ RegistrationNativePlatformOriginGateSource.coins
          ((RegistrationNativePlatformOrdinaryGate.gate reserve (fun value : RawCtxSourceSend.Encrypted=>value.ciphertext.length) sent.1).run before)
        pure ((gated,CborRecordWorldClient.advanceOwner shell ownerIndex plaintext),sent.2)) := by
  change ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
    ((simulateQ CborRecordWorldClient.handler
      (do let reply ← ((WorldSpec n).query (.inr (.inr (.inr (ownerIndex,.inl plaintext)))) : OracleComp (WorldSpec n) (Option RawCtxSourceSend.Encrypted))
          simulateQ PqxdhRecordLiftInterface.coinLift
            ((RegistrationNativePlatformOrdinaryGate.gate reserve (fun value : RawCtxSourceSend.Encrypted=>value.ciphertext.length) reply).run before))).run shell)).run control)=_
  simp only [simulateQ_bind,StateT.run_bind,simulateQ_spec_query]
  rw [show (CborRecordWorldClient.handler (n := n) (.inr (.inr (.inr (ownerIndex,.inl plaintext))))).run shell=
    CborRecordWorldClient.forward (n := n) (.inr (.inr (.inr (ownerIndex,.inl plaintext)))) shell by
      simp only [CborRecordWorldClient.handler,StateT.run,admitted]]
  simp only [CborRecordWorldClient.forward,simulateQ_map,StateT.run_map,simulateQ_spec_query,bind_map_left]
  change (do
    let sent ← (PqxdhRecordLiftProtocol.beaconStep codec.frameRead ownerIndex (.inl plaintext)).run control
    ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
      ((simulateQ CborRecordWorldClient.handler (simulateQ PqxdhRecordLiftInterface.coinLift
        ((RegistrationNativePlatformOrdinaryGate.gate reserve (fun value : RawCtxSourceSend.Encrypted=>value.ciphertext.length) sent.1).run before))).run
          (CborRecordWorldClient.advanceOwner shell ownerIndex plaintext))).run sent.2))=_
  apply bind_congr
  intro sent
  simpa only [bind_pure_comp] using RegistrationNativePlatformOriginGateSource.closed_program
    ((RegistrationNativePlatformOrdinaryGate.gate reserve (fun value : RawCtxSourceSend.Encrypted=>value.ciphertext.length) sent.1).run before)
      codec route (CborRecordWorldClient.advanceOwner shell ownerIndex plaintext) sent.2

/-- A genuine admitted hidden Server send has one lookup and seal, followed by its actual publication and reserve, with complete advanced public controls fixed before the optional sealing reply. -/
theorem server_hidden (env : Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (before : Platform) (shell : CborRecordWorldClient.Shell) (control : Control n)
    (keyId : Std.U64) (plaintext : Pqxdh.Bytes)
    (admitted : CborRecordWorldClient.refusal (n := n) (.inr (.inr (.inl (.inl (plaintext,keyId))))) shell=none)
    (server : Server n) (serverAt : control.server=some server) (peer : Peer n) (peerAt : server.peers keyId=some peer)
    (slot : PqxdhRecordLiftInterface.Slot n) (kernel : LabeledKernel n) (hidden : peer.kernel=.hidden slot kernel)
    (nonempty : plaintext.isEmpty=false)
    (pending : RawCtxChainSend.Kdf (Label n) (Label n) (Label n) RawCtxSourceSend.SealContext)
    (requested : RawCtxChainSend.normalBegin kernel
      ⟨plaintext,keyId,server.sender,(PqxdhRecordLiftWorldCompiler.serverOwner server keyId peer).associatedData⟩=.requested pending) :
    ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
      ((simulateQ CborRecordWorldClient.handler
        ((RegistrationNativePlatformGatedRecordInterface.native env reserve (.inr (.serverSend keyId plaintext))).run before)).run shell)).run control)=
      (do
        let _ ← ((ServiceSpec n).query (.lookup pending.request) : OracleComp (ServiceSpec n) _)
        let ready := RawCtxChainSend.ready pending (advance pending.request 1,pending.request)
        let reply ← ((ServiceSpec n).query (.sealing ready) : OracleComp (ServiceSpec n) _)
        let _ ← ((ServiceSpec n).query (.publish (PqxdhDeploymentNative.serverTag (.inl (plaintext,keyId)))) : OracleComp (ServiceSpec n) _)
        let gated ← simulateQ RegistrationNativePlatformOriginGateSource.coins
          ((RegistrationNativePlatformOrdinaryGate.gate reserve (fun value : RawCtxSourceSend.Encrypted=>value.ciphertext.length) reply).run before)
        pure ((gated,CborRecordWorldClient.advanceServer shell keyId plaintext),
          {control with server:=some {server with peers:=Function.update server.peers keyId (some {peer with kernel:=.hidden slot ready.advanced})}})) := by
  rw [server_source env reserve codec route before shell control keyId plaintext admitted]
  simp only [PqxdhRecordLiftProtocol.serverStep,StateT.run,serverAt,peerAt,bind_assoc,pure_bind]
  rw [RegistrationNativePlatformOriginSendSource.owner (PqxdhDeploymentNative.serverTag (.inl (plaintext,keyId))) server.sender codec.frameRead
    plaintext (PqxdhRecordLiftWorldCompiler.serverOwner server keyId peer) slot kernel hidden nonempty pending requested]
  simp only [bind_assoc,pure_bind]
  rfl

/-- An admitted hidden Beacon send retains the same actual shell, advanced kernel, raw counter and public platform state across every optional seal and reserve result. -/
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
    ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
      ((simulateQ CborRecordWorldClient.handler
        ((RegistrationNativePlatformGatedRecordInterface.native env reserve (.inr (.beaconSend ownerIndex plaintext))).run before)).run shell)).run control)=
      (do
        let _ ← ((ServiceSpec n).query (.lookup pending.request) : OracleComp (ServiceSpec n) _)
        let ready := RawCtxChainSend.ready pending (advance pending.request 1,pending.request)
        let reply ← ((ServiceSpec n).query (.sealing ready) : OracleComp (ServiceSpec n) _)
        let _ ← ((ServiceSpec n).query (.publish (PqxdhDeploymentNative.beaconTag ownerIndex)) : OracleComp (ServiceSpec n) _)
        let gated ← simulateQ RegistrationNativePlatformOriginGateSource.coins
          ((RegistrationNativePlatformOrdinaryGate.gate reserve (fun value : RawCtxSourceSend.Encrypted=>value.ciphertext.length) reply).run before)
        pure ((gated,CborRecordWorldClient.advanceOwner shell ownerIndex plaintext),
          {control with owners:=control.owners.set ownerIndex (.established beacon (.hidden slot ready.advanced))})) := by
  rw [beacon_source env reserve codec route before shell control ownerIndex plaintext admitted]
  simp only [PqxdhRecordLiftProtocol.beaconStep,StateT.run,ownerAt,bind_assoc,pure_bind]
  rw [RegistrationNativePlatformOriginSendSource.owner (PqxdhDeploymentNative.beaconTag ownerIndex) beacon.identityKeyId codec.frameRead
    plaintext (PqxdhRecordLiftWorldCompiler.beaconOwner beacon (.hidden slot kernel) (control.ownerRaw ownerIndex)) slot kernel rfl nonempty pending requested]
  simp only [bind_assoc,pure_bind,PqxdhRecordLiftWorldCompiler.beaconOwner,Function.update_eq_self]

/-- The actual refused-publication prefix has exactly the charged reserve-tail form, preserving arbitrary later source work and all advanced public states. -/
theorem server_stopped (env : Environment n Platform)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit Failure))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (before : Platform) (shell : CborRecordWorldClient.Shell) (control : Control n)
    (keyId : Std.U64) (plaintext : Pqxdh.Bytes)
    (admitted : CborRecordWorldClient.refusal (n := n) (.inr (.inr (.inl (.inl (plaintext,keyId))))) shell=none)
    (server : Server n) (serverAt : control.server=some server) (peer : Peer n) (peerAt : server.peers keyId=some peer)
    (slot : PqxdhRecordLiftInterface.Slot n) (kernel : LabeledKernel n) (hidden : peer.kernel=.hidden slot kernel)
    (nonempty : plaintext.isEmpty=false)
    (pending : RawCtxChainSend.Kdf (Label n) (Label n) (Label n) RawCtxSourceSend.SealContext)
    (requested : RawCtxChainSend.normalBegin kernel
      ⟨plaintext,keyId,server.sender,(PqxdhRecordLiftWorldCompiler.serverOwner server keyId peer).associatedData⟩=.requested pending)
    (future : CborRecordWorldClient.Shell → Control n → Platform → OracleComp (ServiceSpec n) X) :
    (do
      let sent ← ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
      ((simulateQ CborRecordWorldClient.handler
        ((RegistrationNativePlatformGatedRecordInterface.native env reserve (.inr (.serverSend keyId plaintext))).run before)).run shell)).run control)
      if sent.1.1.1.isNone then (fun value=>some (value,sent.1.1.2)) <$> future sent.1.2 sent.2 sent.1.1.2 else pure none)=
      (do
        let _ ← ((ServiceSpec n).query (.lookup pending.request) : OracleComp (ServiceSpec n) _)
        let ready := RawCtxChainSend.ready pending (advance pending.request 1,pending.request)
        let reply ← ((ServiceSpec n).query (.sealing ready) : OracleComp (ServiceSpec n) _)
        RegistrationNativePlatformOriginReserveSourceGuess.tail reserve
          (fun platform=>future (CborRecordWorldClient.advanceServer shell keyId plaintext) {control with server:=some {server with peers:=Function.update server.peers keyId (some {peer with kernel:=.hidden slot ready.advanced})}} platform) before (PqxdhDeploymentNative.serverTag (.inl (plaintext,keyId))) reply) := by
  rw [server_hidden env reserve codec route before shell control keyId plaintext admitted server serverAt peer peerAt slot kernel hidden nonempty pending requested]
  simp only [bind_assoc,pure_bind,RegistrationNativePlatformOriginReserveSourceGuess.tail]

/-- The actual refused-publication prefix has exactly the charged reserve-tail form, preserving arbitrary later source work and all advanced public states. -/
theorem beacon_stopped (env : Environment n Platform)
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
      ⟨plaintext,beacon.control.server_binding.identity_key_id,beacon.identityKeyId,PqxdhRefinement.absBytes beacon.associatedData⟩=.requested pending)
    (future : CborRecordWorldClient.Shell → Control n → Platform → OracleComp (ServiceSpec n) X) :
    (do
      let sent ← ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
      ((simulateQ CborRecordWorldClient.handler
        ((RegistrationNativePlatformGatedRecordInterface.native env reserve (.inr (.beaconSend ownerIndex plaintext))).run before)).run shell)).run control)
      if sent.1.1.1.isNone then (fun value=>some (value,sent.1.1.2)) <$> future sent.1.2 sent.2 sent.1.1.2 else pure none)=
      (do
        let _ ← ((ServiceSpec n).query (.lookup pending.request) : OracleComp (ServiceSpec n) _)
        let ready := RawCtxChainSend.ready pending (advance pending.request 1,pending.request)
        let reply ← ((ServiceSpec n).query (.sealing ready) : OracleComp (ServiceSpec n) _)
        RegistrationNativePlatformOriginReserveSourceGuess.tail reserve
          (fun platform=>future (CborRecordWorldClient.advanceOwner shell ownerIndex plaintext) {control with owners:=control.owners.set ownerIndex (.established beacon (.hidden slot ready.advanced))} platform) before (PqxdhDeploymentNative.beaconTag ownerIndex) reply) := by
  rw [beacon_hidden env reserve codec route before shell control ownerIndex plaintext admitted beacon slot kernel ownerAt nonempty pending requested]
  simp only [bind_assoc,pure_bind,RegistrationNativePlatformOriginReserveSourceGuess.tail]

end BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendEnvelope

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendEnvelope.server_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendEnvelope.server_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendEnvelope.beacon_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendEnvelope.beacon_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendEnvelope.server_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendEnvelope.server_hidden

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendEnvelope.beacon_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendEnvelope.beacon_hidden

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendEnvelope.server_stopped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendEnvelope.server_stopped

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendEnvelope.beacon_stopped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendEnvelope.beacon_stopped
