import BeaconcryptCore.Computational.RawCtxKdfRequestTable

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false

namespace BeaconcryptCore.Computational.RawCtxKdfRequestViews
open PqxdhRefinement PqxdhJointKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf

/-!
Typed views retain the original private initialization or ongoing request and the actual public projection request. Every view forwards exactly one full-stream address. The initialization view fixes the source ratchet label; ongoing requests retain their entire original info. No owner or position creates a separate table entry. These are fixed-source functional laws, not a random-public-HKDF security replacement. The request values remain private interpreter provenance when used by private callers; this module adds no reveal interface.

Forwarding initial64 through a full76 response can evaluate an otherwise unused tail and repeat local HMAC work. The equations preserve the actual reply and complete oracle state, not local runtime or work. A later sampled-table initial-only miss must charge the full76 reservation; no such random-table security game is introduced here.
-/

inductive Request where
  | initial (input : Std.Array Std.U8 32#usize)
  | ongoing (request : SymmetricRatchetKdfRequest)
  | publicView (request : JointKdfViewQuery)

def Spec : OracleSpec Request
  | .initial _ => pqxdh.concrete.InitialRatchetKdfResponse
  | .ongoing _ => RatchetKdfResponse
  | .publicView request => JointKdfViewSpec.Range request

def address : Request → JointKdfAddress
  | .initial input => RawCtxKdfRequestTable.address ⟨input, ratchet.SYM_RATCHET_INFO⟩
  | .ongoing request => RawCtxKdfRequestTable.address request
  | .publicView request => request.address

def project (request : Request) (output : FullOutput) : Spec.Range request :=
  match request with
  | .initial _ => RawCtxKdfRequestTable.initialResponse output
  | .ongoing _ => RawCtxKdfRequestTable.fullResponse output
  | .publicView query => query.project output

def forward : QueryImpl Spec (OracleComp JointKdfRO) :=
  fun request => project request <$> (JointKdfRO.query (address request) : OracleComp JointKdfRO FullOutput)

def sourceReply (source : FixedHkdfSha512NoSaltSource) (request : Request) : Spec.Range request :=
  match request with
  | .initial input => RawCtxSourceHkdf.initialResponse source.crypto ⟨input, ratchet.SYM_RATCHET_INFO⟩
  | .ongoing query => RawCtxSourceHkdf.response source.crypto query
  | .publicView query => query.project (productionStream source.crypto query.address)

/-- Every typed projection is exactly the original source response at its complete request. -/
theorem source_projection (source : FixedHkdfSha512NoSaltSource) (request : Request) :
    project request (productionStream source.crypto (address request)) = sourceReply source request :=
  match request with
  | .initial input => RawCtxKdfRequestTable.initialResponse_source source input
  | .ongoing query => RawCtxKdfRequestTable.fullResponse_source source query
  | .publicView _ => rfl

/-- One shared table step retains its whole previous state and exact typed reply, including hits. -/
theorem memo_forward (source : FixedHkdfSha512NoSaltSource)
    (table : RawCtxKdfRequestTable.Table) (consistent : RawCtxKdfRequestTable.Consistent source table)
    (request : Request) :
    (simulateQ (RawCtxKdfRequestTable.memoImpl source) (forward request)).run table =
      pure (sourceReply source request,
        table.cacheQuery (address request) (productionStream source.crypto (address request))) := by
  simp only [forward, simulateQ_map, simulateQ_spec_query, StateT.run_map,
    RawCtxKdfRequestTable.memo_step source table consistent, map_pure, source_projection]

def width : Request → Nat
  | .initial _ => 64
  | .ongoing _ => 76
  | .publicView query => query.projection.width

def replyBytes (request : Request) : Spec.Range request → Pqxdh.Bytes :=
  match request with
  | .initial _ => fun reply => absBytes reply.bytes
  | .ongoing _ => fun reply => absBytes reply.bytes
  | .publicView _ => fun reply => reply.toList

def projectedBytes (request : Request) (output : FullOutput) : Pqxdh.Bytes :=
  match request with
  | .initial _ => output.toList.take 64
  | .ongoing _ => output.toList
  | .publicView query => (query.project output).toList

/-- Typed conversion retains every requested byte and the exact public coordinate. -/
theorem project_bytes (request : Request) (output : FullOutput) :
    replyBytes request (project request output) = projectedBytes request output :=
  match request with
  | .initial _ => RawCtxKdfRequestTable.initialResponse_bytes output
  | .ongoing _ => RawCtxKdfRequestTable.fullResponse_bytes output
  | .publicView _ => rfl

/-- Every possible typed reply has its requested fixed width. -/
theorem reply_width (request : Request) (reply : Spec.Range request) :
    (replyBytes request reply).length = width request := by
  cases request with
  | initial input =>
    have length : reply.bytes.val.length = 64 := by simpa using reply.bytes.property
    simpa only [replyBytes, width, absBytes, List.length_map] using length
  | ongoing request =>
    have length : reply.bytes.val.length = 76 := by simpa using reply.bytes.property
    simpa only [replyBytes, width, absBytes, List.length_map] using length
  | publicView request =>
    simpa only [replyBytes, width, List.Vector.toList] using reply.property

/-- An initial view and an ongoing view at its exact input/info are one table address. -/
theorem initial_ongoing_address (input : Std.Array Std.U8 32#usize) :
    address (.initial input) = address (.ongoing ⟨input, ratchet.SYM_RATCHET_INFO⟩) := rfl

/-- Every existing public ratchet projection at the same input uses that very same private address. -/
theorem initial_public_address (input : Std.Array Std.U8 32#usize) (projection : JointKdfProjection) :
    address (.initial input) = address (.publicView ⟨absBytes input, .ratchet, projection⟩) :=
  congrArg (fun info => (⟨info, absBytes input⟩ : JointKdfAddress))
    (by simpa only [pqxdh.SYM_RATCHET_INFO, FixedHkdfDomain.info_ratchet] using absBytes_SYM_RATCHET_INFO)

/-- Both typed private views of one response share the entire initial 64-byte prefix. -/
theorem initial_ongoing_prefix (input : Std.Array Std.U8 32#usize) (output : FullOutput) :
    replyBytes (.initial input) (project (.initial input) output) =
      (replyBytes (.ongoing ⟨input, ratchet.SYM_RATCHET_INFO⟩)
        (project (.ongoing ⟨input, ratchet.SYM_RATCHET_INFO⟩) output)).take 64 := by
  simp only [project_bytes, projectedBytes]

end BeaconcryptCore.Computational.RawCtxKdfRequestViews

/-- info: 'BeaconcryptCore.Computational.RawCtxKdfRequestViews.source_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxKdfRequestViews.source_projection

/-- info: 'BeaconcryptCore.Computational.RawCtxKdfRequestViews.memo_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxKdfRequestViews.memo_forward

/-- info: 'BeaconcryptCore.Computational.RawCtxKdfRequestViews.project_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxKdfRequestViews.project_bytes

/-- info: 'BeaconcryptCore.Computational.RawCtxKdfRequestViews.reply_width' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxKdfRequestViews.reply_width

/-- info: 'BeaconcryptCore.Computational.RawCtxKdfRequestViews.initial_ongoing_address' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxKdfRequestViews.initial_ongoing_address

/-- info: 'BeaconcryptCore.Computational.RawCtxKdfRequestViews.initial_public_address' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxKdfRequestViews.initial_public_address

/-- info: 'BeaconcryptCore.Computational.RawCtxKdfRequestViews.initial_ongoing_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxKdfRequestViews.initial_ongoing_prefix
