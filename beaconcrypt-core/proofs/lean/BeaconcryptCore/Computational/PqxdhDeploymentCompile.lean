-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentRecordCache

/-! The compiled program of the CE-3 trial. A deployment adversary is turned into an ordinary source14 program: registration, HMAC and BLAKE2b commands are forwarded unchanged (a `create` pin is parsed locally first), and every record command is executed locally on a copy of the addressed Server peer or Beacon owner, behind the same frame log as the native record commands. A copy is built once, from public data and one source14 kernel read: the Server kernel reveal for a peer, the established-kernel field read for an owner. The public data are the program's own log of successful replies: created pins and key IDs, bundle bytes, finish inputs, accept bytes by returned session handle and build responses by assigned key ID. The reads are proof devices of the analysis and are never answered to the deployment adversary; no identity, KEM, prekey or one-time field is read. `merge` reassembles a deployment state from the compiled program's local copies and the source14 state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentCompile
open PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhDeploymentRecordCache (SourceSpec localPrimitives)
open PqxdhDeploymentInterface (Spec Command parsePin)
open PqxdhBeaconPhase2Preparation (Word32)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response X : Type}

abbrev Kernel := beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel
abbrev Identity := RawCtxServerRouting.Identity

/-- Public log of successful replies: pin and key ID of every created owner in creation order, the bundle bytes and finish input of each owner, the raw accept bytes of each returned session handle, and the session and response of each assigned key ID. -/
structure Log where
  owners : List (Word32 × Std.U64)
  bundles : Nat → Option Pqxdh.Bytes
  finishes : Nat → Option Pqxdh.Bytes
  accepts : Nat → Option Pqxdh.Bytes
  builds : Std.U64 → Option (Nat × PqxdhServerRegistrationPublication.Response)

/-- The empty log. -/
def Log.empty : Log := ⟨[], fun _ => none, fun _ => none, fun _ => none, fun _ => none⟩

/-- The compiled program's local state: its public log, the live kernels of the peers and owners copied so far, the raw-attempt counters and the produced record frames. -/
structure Local where
  log : Log
  peers : Std.U64 → Option Kernel
  owners : Nat → Option Kernel
  serverRaw : Nat
  ownerRaw : Nat → Nat
  produced : List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame)

/-- The initial local state: empty log, no copies, zero counters, no produced frame. -/
def Local.empty : Local := ⟨Log.empty, fun _ => none, fun _ => none, 0, fun _ => 0, []⟩

/-- Append the frames produced by one local record command under its tag. -/
def Local.produce (copies : Local) (tag : PqxdhDeploymentInterface.FrameTag) (frames : List PqxdhDeploymentNative.Frame) :
    Local :=
  { copies with produced := copies.produced ++ frames.map fun frame => (tag, frame) }

/-- The 32-byte identity key read from Phase 1 bytes with the codec reader and the Server's identity parser. -/
def identityOf (codec : Codec Reader Response) (bytes : Pqxdh.Bytes) : Option Identity := do
  let reader ← codec.read1 bytes
  let encoded ← codec.identity reader
  let identity ← PqxdhEd25519EufCma.parseIdentity encoded
  pure (PqxdhRootTableInitialization.rootArray identity)

/-- The Server identity read from a build response with the codec Phase 2 reader. -/
def serverIdentityOf (codec : Codec Reader Response) (response : PqxdhServerRegistrationPublication.Response) :
    Option Identity :=
  codec.read2 response.serialized >>= codec.serverIdentity

/-- Public reconstruction of an installed Server peer: the Server identity from its build response and the Beacon identity from the accept bytes of the same session. -/
def peerView (codec : Codec Reader Response) (log : Log) (kid : Std.U64) : Option (Identity × Identity) := do
  let built ← log.builds kid
  let raw ← log.accepts built.1
  let server ← serverIdentityOf codec built.2
  let peer ← identityOf codec raw
  pure (server, peer)

/-- Public reconstruction of an established owner: its outer key ID (the assigned key ID of its finish input), its established control (the pinned binding from `create` and the assigned key ID) and its 153-byte associated data (pin and the identity key read from its bundle bytes). -/
noncomputable def ownerView (codec : Codec Reader Response) (log : Log) (index : Nat) :
    Option (Std.U64 × beaconcrypt_core.pqxdh.BeaconEstablished × Std.Array Std.U8 153#usize) := do
  let created ← log.owners[index]?
  let bundle ← log.bundles index
  let beacon ← identityOf codec bundle
  let raw ← log.finishes index
  let response ← codec.read2 raw
  let assigned := codec.assignedId response
  pure (assigned, ⟨⟨created.1, created.2⟩, assigned⟩,
    PqxdhBeaconPhase2Shared.associatedData ⟨⟨created.1, created.2⟩, beacon⟩)

/-- The peer addressed by a Server record command: the key ID of a send, the header route of a raw receive. -/
def serverTarget (route : RawCtxServerRouting.SenderDecoder) : RawCtxServerMixed.SourceSpec.Domain → Option Std.U64
  | .inl (_, kid) => some kid
  | .inr raw => route raw

/-- The local Server: the reconstructed Server identity and at most the addressed peer, with its local or revealed kernel. -/
def localServer (codec : Codec Reader Response) (log : Log) (kid : Std.U64) (kernel : Option Kernel) (raw : Nat) :
    RawCtxServerRouting.State Unit Unit :=
  ⟨⟨((peerView codec log kid).map Prod.fst).getD default,
    fun other => if other = kid then (do
      let current ← kernel
      let view ← peerView codec log kid
      pure ⟨view.2, current, ()⟩) else none, ()⟩, raw⟩

/-- The local owner: the reconstructed established owner with its local or read kernel, or an inactive owner. Identity and secret fields are placeholders that no record command reads. -/
noncomputable def localOwner (codec : Codec Reader Response) (log : Log) (index : Nat) (kernel : Option Kernel) (raw : Nat) :
    RawCtxBeaconLifecycle.State Unit Unit Unit :=
  match kernel, ownerView codec log index with
  | some current, some view => ⟨⟨(), view.1, view.2.1.server_binding.identity_public_key,
      .established view.2.1 view.2.2 current⟩, raw⟩
  | _, _ => ⟨⟨(), 0#u64, default, .aborted ⟨0#u64⟩⟩, raw⟩

/-- The established kernel of a local owner phase. -/
def phaseKernel {DhPair KemPair : Type} :
    RawCtxBeaconLifecycle.Phase DhPair KemPair Kernel → Option Kernel
  | .established _ _ current => some current
  | _ => none

/-- The source14 Server kernel reveal. -/
def revealQuery (kid : Std.U64) : OracleComp (SourceSpec KemSK) (Option Kernel) :=
  ((SourceSpec KemSK).query (.inl (.inr (.reveal kid))) : OracleComp (SourceSpec KemSK) _)

/-- The source14 established-kernel field read. -/
def kernelQuery (index : Nat) : OracleComp (SourceSpec KemSK) (Option Kernel) :=
  (fun value => match value with
    | some (.kernel current) => some current
    | _ => none) <$>
    ((SourceSpec KemSK).query (.inr (index, .kernel)) : OracleComp (SourceSpec KemSK) _)

/-- The kernel of a peer: the local copy if one exists, otherwise one source14 reveal. -/
def peerKernel (copies : Local) (kid : Std.U64) : OracleComp (SourceSpec KemSK) (Option Kernel) :=
  match copies.peers kid with
  | some current => pure (some current)
  | none => revealQuery kid

/-- The kernel of an owner: the local copy if one exists, otherwise one source14 kernel read. -/
def ownerKernel (copies : Local) (index : Nat) : OracleComp (SourceSpec KemSK) (Option Kernel) :=
  match copies.owners index with
  | some current => pure (some current)
  | none => kernelQuery index

/-- A forwarded source14 command. -/
def forward (request : PqxdhRegistrationSchedule.Request) :
    OracleComp (SourceSpec KemSK) (PqxdhRegistrationSchedule.QuerySpec request) :=
  ((SourceSpec KemSK).query (.inl (.inr request)) : OracleComp (SourceSpec KemSK) _)

/-- Local Server record command: copy the addressed peer if needed, run `serverImpl` on the local Server under the Server key ID behind the frame log with locally answered primitives, keep the returned kernel, counter and produced frames. -/
noncomputable def serverLocal (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : RawCtxServerMixed.SourceSpec.Domain) :
    StateT Local (OracleComp (SourceSpec KemSK)) (RawCtxServerMixed.SourceSpec.Range query) := fun copies =>
  match serverTarget route query with
  | none => do
      let result ← simulateQ (localPrimitives setup codec) (PqxdhDeploymentNative.logged
        ((RawCtxServerMixed.serverImpl (fun _ => setup.serverKeyId) route codec.frameRead query).run
          (localServer codec copies.log 0#u64 none copies.serverRaw)))
      pure (result.1.1, ({ copies with serverRaw := result.1.2.rawAttempts } : Local).produce
        (PqxdhDeploymentNative.serverTag query) result.2)
  | some kid => do
      let kernel ← peerKernel copies kid
      let result ← simulateQ (localPrimitives setup codec) (PqxdhDeploymentNative.logged
        ((RawCtxServerMixed.serverImpl (fun _ => setup.serverKeyId) route codec.frameRead query).run
          (localServer codec copies.log kid kernel copies.serverRaw)))
      pure (result.1.1, ({ copies with
        peers := Function.update copies.peers kid ((result.1.2.server.peers kid).map RawCtxServerRouting.Peer.kernel)
        serverRaw := result.1.2.rawAttempts } : Local).produce (PqxdhDeploymentNative.serverTag query) result.2)

/-- Local Beacon record command: an uncreated handle is rejected; otherwise copy the owner if needed, run `beaconImpl` on the local owner behind the frame log with locally answered primitives, keep the returned kernel, counter and produced frames. -/
noncomputable def beaconLocal (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (query : RawCtxMixedOwner.SourceSpec.Domain) :
    StateT Local (OracleComp (SourceSpec KemSK)) (RawCtxMixedOwner.SourceSpec.Range query) := fun copies =>
  if index < copies.log.owners.length then do
    let kernel ← ownerKernel copies index
    let result ← simulateQ (localPrimitives setup codec) (PqxdhDeploymentNative.logged
      ((RawCtxBeaconLifecycle.beaconImpl codec.frameRead query).run
        (localOwner codec copies.log index kernel (copies.ownerRaw index))))
    pure (result.1.1, ({ copies with
      owners := Function.update copies.owners index (phaseKernel result.1.2.beacon.phase)
      ownerRaw := Function.update copies.ownerRaw index result.1.2.rawAttempts } : Local).produce
        (PqxdhDeploymentNative.beaconTag index) result.2)
  else pure (PqxdhDeploymentNative.absent query, copies)

/-- Record a successful reply in the public log. -/
def logReply (log : Log) : (command : Command) → PqxdhDeploymentInterface.CommandSpec command → Log
  | .bundle owner, some bytes => { log with bundles := Function.update log.bundles owner (some bytes) }
  | .accept raw, some session => { log with accepts := Function.update log.accepts session (some raw) }
  | .build session _, some response =>
      { log with builds := Function.update log.builds response.keyId (some (session, response)) }
  | .finish owner raw, some _ => { log with finishes := Function.update log.finishes owner (some raw) }
  | _, _ => log

/-- A forwarded registration command whose successful reply is logged. -/
def forwardLogged (request : PqxdhRegistrationSchedule.Request) (command : Command)
    (reply : PqxdhRegistrationSchedule.QuerySpec request → PqxdhDeploymentInterface.CommandSpec command) :
    StateT Local (OracleComp (SourceSpec KemSK)) (PqxdhDeploymentInterface.CommandSpec command) := fun copies => do
  let answer ← forward request
  pure (reply answer, { copies with log := logReply copies.log command (reply answer) })

/-- The compiler: every deployment command as source14 queries plus local work. -/
noncomputable def compileImpl (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) :
    QueryImpl Spec (StateT Local (OracleComp (SourceSpec KemSK)))
  | .inl coin => StateT.lift ((SourceSpec KemSK).query (.inl (.inl coin)) : OracleComp (SourceSpec KemSK) _)
  | .inr (.create pin keyId) => fun copies =>
      match parsePin pin with
      | none => pure (none, copies)
      | some word => do
          let index ← forward (KemSK := KemSK) (.create word keyId)
          pure (some index, { copies with log := { copies.log with owners := copies.log.owners ++ [(word, keyId)] } })
  | .inr (.bundle owner) => forwardLogged (.bundle owner) (.bundle owner) id
  | .inr (.accept raw) => forwardLogged (.accept raw) (.accept raw) id
  | .inr (.build session payload) => forwardLogged (.build session payload) (.build session payload) id
  | .inr (.finish owner raw) => forwardLogged (.finish owner raw) (.finish owner raw) id
  | .inr (.hmac key message) => StateT.lift (forward (.hmac key message))
  | .inr (.hash bytes) => StateT.lift (forward (.hash bytes))
  | .inr (.serverSend kid plaintext) => serverLocal setup codec route (.inl (plaintext, kid))
  | .inr (.serverRaw raw) => serverLocal setup codec route (.inr raw)
  | .inr (.beaconSend owner plaintext) => beaconLocal setup codec owner (.inl plaintext)
  | .inr (.beaconRaw owner raw) => beaconLocal setup codec owner (.inr raw)

/-- The compiled source14 program of a deployment adversary, returning the adversary's output with the final local state. -/
noncomputable def compile (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (adversary : OracleComp Spec X) :
    OracleComp (SourceSpec KemSK) (X × Local) :=
  (simulateQ (compileImpl setup codec route) adversary).run Local.empty

/-- A Server peer with its local live kernel, if one exists. -/
def mergePeer (kernel : Option Kernel) (peer : RawCtxServerRouting.Peer Unit) : RawCtxServerRouting.Peer Unit :=
  match kernel with
  | some current => { peer with kernel := current }
  | none => peer

/-- An established owner with its local live kernel, if one exists; every other owner is unchanged. -/
def mergeOwner (kernel : Option Kernel) (owner : PqxdhRegistrationSchedule.Owner KemSK) :
    PqxdhRegistrationSchedule.Owner KemSK :=
  match kernel, owner.beacon.phase with
  | some current, .established control associatedData _ =>
      { owner with beacon := { owner.beacon with phase := .established control associatedData current } }
  | _, _ => owner

/-- Reassemble a deployment state: the source14 state with every copied peer and owner kernel replaced by its live local copy, the local counters and the local produced frames. -/
def merge (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK) : PqxdhDeploymentNative.State KemSK :=
  ⟨{ native with
      shared := (native.shared.1, { native.shared.2 with
        server := { native.shared.2.server with
          server := { native.shared.2.server.server with
            peers := fun kid => (native.shared.2.server.server.peers kid).map (mergePeer (copies.peers kid)) } } })
      owners := native.owners.mapIdx fun index owner => mergeOwner (copies.owners index) owner },
    copies.serverRaw, copies.ownerRaw, copies.produced⟩

/-- With no local copies, merging changes nothing, the counters start at zero and no frame is produced. -/
theorem merge_empty (native : PqxdhRegistrationSchedule.State KemSK) :
    merge Local.empty native = ⟨native, 0, fun _ => 0, []⟩ := by
  have peers : (fun kid => (native.shared.2.server.server.peers kid).map (mergePeer (Local.empty.peers kid))) =
      native.shared.2.server.server.peers := by
    funext kid
    cases native.shared.2.server.server.peers kid <;> rfl
  have owners : native.owners.mapIdx (fun index owner => mergeOwner (Local.empty.owners index) owner) = native.owners := by
    apply List.ext_getElem?
    intro index
    rw [List.getElem?_mapIdx]
    cases native.owners[index]? <;> rfl
  simp only [merge, peers, owners]
  rfl

end BeaconcryptCore.Computational.PqxdhDeploymentCompile

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompile.merge_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompile.merge_empty
