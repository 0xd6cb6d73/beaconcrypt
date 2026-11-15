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
  | .initial input => RawCtxKdfRequestTable.initialAddress ⟨input, ratchet.INITIAL_RATCHET_INFO⟩
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
  | .initial input => RawCtxSourceHkdf.initialResponse source.crypto ⟨input, ratchet.INITIAL_RATCHET_INFO⟩
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

/-- Actual initial and message views select different addresses even at the same input. -/
theorem initial_ongoing_address_ne (input : Std.Array Std.U8 32#usize) :
    address (.initial input) ≠ address (.ongoing ⟨input, ratchet.SYM_RATCHET_INFO⟩) := by
  intro same
  have infos := congrArg JointKdfAddress.info same
  exact Pqxdh.INFO_INIT_ne_INFO_R (by simpa only [address,
    RawCtxKdfRequestTable.initialAddress, RawCtxKdfRequestTable.address,
    absBytes_INITIAL_RATCHET_INFO, absBytes_SYM_RATCHET_INFO] using infos)

/-- Public evaluation at the actual initial label shares exactly that initial request address. -/
theorem initial_public_address (input : Std.Array Std.U8 32#usize) (projection : JointKdfProjection) :
    address (.initial input) = address (.publicView ⟨absBytes input, .initial, projection⟩) :=
  congrArg (fun info => (⟨info, absBytes input⟩ : JointKdfAddress)) absBytes_INITIAL_RATCHET_INFO

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

/-- info: 'BeaconcryptCore.Computational.RawCtxKdfRequestViews.initial_ongoing_address_ne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxKdfRequestViews.initial_ongoing_address_ne

/-- info: 'BeaconcryptCore.Computational.RawCtxKdfRequestViews.initial_public_address' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxKdfRequestViews.initial_public_address
