-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeTokenCacheSource
import BeaconcryptCore.Computational.RegistrationNativeTokenTrace

/-! The earlier accept that created a later consumed token retains its exact selected authentication cache through the accept's actual returned state. This strengthens provenance only at the actual source cut. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeTokenCacheTrace
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeTokenSource (Present Born)
open RegistrationNativeStageTrace (Call Path Executed)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "implementation" => RegistrationNativeExperiment.handler setup checks wire route representation created source credential
attribute [local irreducible] RegistrationNativeExperiment.handler RegistrationServerSdkSource.accept
  RegistrationServerNativeSource.authenticate RegistrationServerNativeSource.agree RegistrationWorldAuthentication.begin

def SourceAt (call : Call RegistrationNativeRawAdapter.TypedSpec Native) (token : peer.ConsumedRegistration) : Prop :=
  ∃ packet events authenticated afterAuthentication,
    call.query = .inr (.accept packet) ∧
    (.ok (events, .Accepted authenticated), afterAuthentication) ∈ support
      ((RegistrationServerNativeSource.authenticate setup (RegistrationNativeWire.ledgerCodec wire) route source.verify created packet).run call.before.server) ∧
    Born setup checks representation created packet authenticated afterAuthentication token ∧
    RegistrationNativeInitFinal.summary afterAuthentication = RegistrationNativeInitFinal.summary call.after.server

set_option maxRecDepth 16384 in
private theorem accept_origin (packet : registration.InitPacket) (before after : Native)
    (reply : RustM (Option Nat))
    (called : (reply, after) ∈ support ((implementation (.inr (.accept packet))).run before))
    (token : peer.ConsumedRegistration) (present : Present token after.server) :
    Present token before.server ∨ SourceAt setup checks wire route representation created
      (⟨.inr (.accept packet), before, reply, after⟩ : Call RegistrationNativeRawAdapter.TypedSpec Native) token := by
  simp only [RegistrationNativeExperiment.handler] at called
  change (reply, after) ∈ support ((RegistrationNativeExperiment.server
    (RegistrationServerSdkSource.accept setup (RegistrationNativeWire.ledgerCodec wire) checks route source.verify representation created packet)).run
    { before with parsedAccepts := before.parsedAccepts + 1 }) at called
  simp only [RegistrationNativeExperiment.server, StateT.run, support_map] at called
  obtain ⟨inner, supported, same⟩ := called
  cases same
  rcases RegistrationNativeTokenCacheSource.accept setup (RegistrationNativeWire.ledgerCodec wire) checks route source.verify
    representation created packet before.server inner supported token present with old | ⟨events, authenticated, middle, checked, born, summaryEq⟩
  · exact Or.inl old
  · exact Or.inr (show SourceAt setup checks wire route representation created
      (⟨.inr (.accept packet), before, inner.1, {before with parsedAccepts := before.parsedAccepts + 1, server := inner.2}⟩ : Call RegistrationNativeRawAdapter.TypedSpec Native) token from
      ⟨packet, events, authenticated, middle, rfl, checked, born, summaryEq⟩)

def NonAccept : RegistrationNativeRawAdapter.TypedSpec.Domain → Prop
  | .inr (.accept _) => False
  | _ => True

/-- A final live token is old or has a genuine earlier accept with its actual returned-cache equality. -/
theorem call_origin (call : Call RegistrationNativeRawAdapter.TypedSpec Native)
    (called : Executed implementation call) (token : peer.ConsumedRegistration) (present : Present token call.after.server) :
    Present token call.before.server ∨ SourceAt setup checks wire route representation created call token := by
  by_cases allowed : NonAccept call.query
  · rcases RegistrationNativeTokenTrace.call_origin setup checks wire route representation created credential call called token present with old | origin
    · exact Or.inl old
    · obtain ⟨packet, _events, _authenticated, _afterAuthentication, queryEq, _checked, _born⟩ := origin
      rw [queryEq] at allowed
      exact False.elim allowed
  · rcases call with ⟨query, before, reply, after⟩
    cases query with
    | inl coin => exact False.elim (allowed trivial)
    | inr query => cases query with
      | accept packet => exact accept_origin setup checks wire route representation created credential packet before after reply called token present
      | _ => exact False.elim (allowed trivial)

/-- Actual path induction retains the selected cache of the same earlier token-creating accept. -/
theorem path_origin {first last : Native} {calls : List (Call RegistrationNativeRawAdapter.TypedSpec Native)}
    (actual : Path implementation first calls last) (token : peer.ConsumedRegistration) (present : Present token last.server) :
    Present token first.server ∨ ∃ call ∈ calls, SourceAt setup checks wire route representation created call token := by
  induction actual with
  | nil => exact Or.inl present
  | cons call called rest last following ih =>
      rcases ih present with old | ⟨earlier, member, origin⟩
      · rcases call_origin setup checks wire route representation created credential call called token old with initial | born
        · exact Or.inl initial
        · exact Or.inr ⟨call, List.mem_cons_self, born⟩
      · exact Or.inr ⟨earlier, List.mem_cons_of_mem _ member, origin⟩

/-- Every consumed token has its actual earlier authentication cache in the same chronological leading. -/
theorem taken_origin {first beforeBuild : Native} {calls : List (Call RegistrationNativeRawAdapter.TypedSpec Native)}
    (actual : Path implementation first calls beforeBuild) (empty : first.server.sessions = [])
    (index : Nat) (token : peer.ConsumedRegistration) (current : RegistrationServerFrontendCompiler.State n)
    (taken : RegistrationServerSdkSource.take index beforeBuild.server = (some token, current)) :
    ∃ call leading trailing,
      calls = leading ++ call :: trailing ∧ Path implementation first leading call.before ∧
      Executed implementation call ∧ Path implementation call.after trailing beforeBuild ∧
      SourceAt setup checks wire route representation created call token := by
  have found := (RegistrationNativeTokenSource.take_origin index beforeBuild.server current token taken).1
  have present : Present token beforeBuild.server := List.mem_of_getElem? found
  rcases path_origin setup checks wire route representation created credential actual token present with initial | ⟨call, member, origin⟩
  · simp only [Present, empty, List.not_mem_nil] at initial
  · obtain ⟨leading, trailing, split, earlier, called, later⟩ := actual.member call member
    exact ⟨call, leading, trailing, split, earlier, called, later, origin⟩

end BeaconcryptCore.Computational.RegistrationNativeTokenCacheTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTokenCacheTrace.call_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTokenCacheTrace.call_origin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTokenCacheTrace.path_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTokenCacheTrace.path_origin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTokenCacheTrace.taken_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTokenCacheTrace.taken_origin
