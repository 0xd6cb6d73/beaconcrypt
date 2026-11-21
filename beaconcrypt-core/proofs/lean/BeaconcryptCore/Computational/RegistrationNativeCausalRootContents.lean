-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeTokenRootReceipt
import BeaconcryptCore.Computational.RegistrationNativeServerHistoryOrigin

/-! Every source Server-role issuance has an actual earlier accept, its retained root derivation inputs, and the actual intervening one-use token/build stage in one initialized execution. The signed stage may precede publication or installation failure. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeCausalRootContents
open RegistrationNativeStageTrace (Call Path Executed)
open RegistrationSigningShared (Receipt)
open RegistrationNativeMldsaRoleFrame (serverReceipts)
open RegistrationNativeServerIssuance (history)
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
attribute [local irreducible] RegistrationNativeExperiment.handler RegistrationServerNativeSource.authenticate RegistrationServerNativeSource.agree

/-- The complete native initialized history derives a causal accept-to-token-to-build chain for every Server signing receipt, with the actual pre-erasure root collection. -/
theorem path_contents (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKid : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (startup : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKid))
    (calls : List (Call RegistrationNativeRawAdapter.TypedSpec Native)) (final : Native)
    (actual : Path (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential)
      initial.state calls final)
    (receipt : Receipt) (member : receipt ∈ serverReceipts (history final.server)) :
    ∃ buildCall buildLeading buildTrailing index application token current acceptCall acceptLeading between
        packet events authenticated afterAuthentication afterAgreement consumedHistory,
      calls = buildLeading ++ buildCall :: buildTrailing ∧
      buildLeading = acceptLeading ++ acceptCall :: between ∧
      Path (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential)
        initial.state acceptLeading acceptCall.before ∧
      Executed (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential) acceptCall ∧
      Path (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential)
        acceptCall.after between buildCall.before ∧
      Executed (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential) buildCall ∧
      Path (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential)
        buildCall.after buildTrailing final ∧
      buildCall.query = .inr (.build index application) ∧
      RegistrationServerSdkSource.take index buildCall.before.server = (some token, current) ∧
      RegistrationNativeServerHistoryOrigin.SourceAt buildCall receipt ∧ acceptCall.query = .inr (.accept packet) ∧
      (.ok (events, .Accepted authenticated), afterAuthentication) ∈ support
        ((RegistrationServerNativeSource.authenticate setup (RegistrationNativeWire.ledgerCodec wire) route source.verify initial.created packet).run acceptCall.before.server) ∧
      (.ok (.ServerComplete token.agreement), afterAgreement) ∈ support
        ((RegistrationServerNativeSource.agree setup checks representation initial.created packet authenticated).run afterAuthentication) ∧
      RegistrationReplaySchedule.consume token.agreement afterAgreement.consumed = .ok (.Some token, consumedHistory) ∧
      Nonempty (RegistrationNativeTokenRootReceipt.Input setup checks representation initial.created
        packet authenticated afterAuthentication afterAgreement token.agreement) := by
  rcases RegistrationNativeServerHistoryOrigin.path_origin setup checks wire route representation initial.created initial.credential actual receipt member
    with original | ⟨buildCall, recorded, stage⟩
  · have empty := RegistrationNativeServerHistoryOrigin.start_empty setup ensureInit identityIndex serverKid initial startup
    rw [empty] at original
    cases original
  · have stageCopy := stage
    obtain ⟨index, application, token, current, _plaintext, _availability, _firstRecord, _hashed, queryEq, taken, _input,
      _admitted, _path, _key, _payload⟩ := stage
    obtain ⟨buildLeading, buildTrailing, split, beforeBuild, built, afterBuild⟩ := actual.member buildCall recorded
    have empty := RegistrationNativeTokenTrace.start_empty setup ensureInit identityIndex serverKid initial startup
    obtain ⟨acceptCall, acceptLeading, between, packet, events, authenticated, afterAuthentication, afterAgreement, consumedHistory,
      acceptSplit, beforeAccept, accepted, betweenPath, acceptQuery, checked, agreed, consumed, inputs⟩ :=
      RegistrationNativeTokenRootReceipt.taken setup checks representation initial.created wire route initial.credential
        beforeBuild empty index token current taken
    exact ⟨buildCall, buildLeading, buildTrailing, index, application, token, current, acceptCall, acceptLeading, between,
      packet, events, authenticated, afterAuthentication, afterAgreement, consumedHistory,
      split, acceptSplit, beforeAccept, accepted, betweenPath, built, afterBuild, queryEq, taken, stageCopy, acceptQuery,
      checked, agreed, consumed, inputs⟩

end BeaconcryptCore.Computational.RegistrationNativeCausalRootContents
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCausalRootContents.path_contents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCausalRootContents.path_contents
