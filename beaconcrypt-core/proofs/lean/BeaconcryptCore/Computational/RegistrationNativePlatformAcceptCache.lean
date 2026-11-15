-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBuildCache
import BeaconcryptCore.Computational.RegistrationNativePlatformReceiptPreservation

/-! Actual incoming source acceptance extends its shared cache through repeated pin recomputation and mandatory authentication. Every later replay/reservation/agreement/retention outcome preserves exactly the reached authentication history/cache summary, retaining the real external platform poststate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformAcceptCache
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationNativePlatformSdkCache (Keeps serverCache)
variable {n : Nat} {Platform Value Next ι KemSK Reader Response : Type} {base : OracleSpec ι}

private def Quiet {S W : Type} (field : S → W) (work : StateT S (StateT Platform ProbComp) Value) : Prop :=
  ∀ before previous result, result ∈ support ((work.run before).run previous) → field result.1.2 = field before

private theorem quiet_pure {S W : Type} (field : S → W) (value : Value) :
    Quiet (Platform := Platform) field (pure value) := by
  intro before previous result supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl

private theorem quiet_bind {S W : Type} (field : S → W)
    (work : StateT S (StateT Platform ProbComp) Value) (next : Value → StateT S (StateT Platform ProbComp) Next)
    (first : Quiet field work) (rest : ∀ value, Quiet field (next value)) : Quiet field (work >>= next) := by
  intro before previous result supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, called, continued⟩ := supported
  exact (rest middle.1.1 middle.1.2 middle.2 result continued).trans (first before previous middle called)

private theorem quiet_get {S W : Type} (field : S → W) :
    Quiet (Platform := Platform) field (get : StateT S (StateT Platform ProbComp) S) := by
  intro before previous result supported
  simp only [StateT.run_get, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl

private theorem quiet_external {S W : Type} (field : S → W) (work : StateT Platform ProbComp Value) :
    Quiet field (StateT.lift work : StateT S (StateT Platform ProbComp) Value) := by
  intro before previous result supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
  obtain ⟨inner, _possible, same⟩ := supported
  cases same
  rfl

private theorem quiet_native {S W : Type} (field : S → W)
    (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (work : StateT S ProbComp Value)
    (keeps : ∀ before result, result ∈ support (work.run before) → field result.2 = field before) :
    Quiet field (fun before => simulateQ coins (work.run before)) := by
  intro before previous result supported
  exact keeps before result.1 (RegistrationNativePlatformHashReceipt.native_support coins _ _ _ _ supported)

theorem afterAuthentication (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (reserve : StateT Platform ProbComp Bool)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    Quiet (RegistrationNativeInitFinal.summary (n := n)) (RegistrationNativePlatformServerSdk.afterAuthentication coins setup checks (StateT.lift reserve)
      representation created packet authenticated) := by
  unfold RegistrationNativePlatformServerSdk.afterAuthentication
  apply quiet_bind RegistrationNativeInitFinal.summary _ _ (quiet_get _)
  intro before
  split
  · exact quiet_pure _ _
  · apply quiet_bind _ _ _ (quiet_external _ reserve)
    intro admitted
    cases admitted with
    | false => exact quiet_pure _ _
    | true =>
      apply quiet_bind _ _ _ (quiet_native RegistrationNativeInitFinal.summary coins _ (fun before result supported =>
        (RegistrationNativeInitFinal.agree setup checks representation created packet authenticated before result supported)))
      intro completed
      cases completed with
      | fail error | div => exact quiet_pure _ _
      | ok effect =>
        cases effect
        all_goals first
          | exact quiet_pure _ _
          | exact quiet_native RegistrationNativeInitFinal.summary coins _ (fun before result supported =>
              (RegistrationNativeInitFinal.retain created _ before result supported))

private theorem pure_keeps (value : Value) :
    Keeps (Platform := Platform) (serverCache (n := n)) (pure value) := by
  intro before previous result supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact le_refl _

private theorem bind_keeps
    (work : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Value)
    (next : Value → StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Next)
    (first : Keeps serverCache work) (rest : ∀ value, Keeps serverCache (next value)) : Keeps serverCache (work >>= next) := by
  intro before previous result supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, called, continued⟩ := supported
  exact (first before previous middle called).trans (rest middle.1.1 middle.1.2 middle.2 result continued)

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

attribute [local irreducible] RegistrationWorldAuthentication.begin RegistrationWorldAuthentication.program
  RegistrationAuthenticationShared.begin

private theorem authenticate (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (verify : MldsaTranscriptAuth.Verify) (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    Keeps (serverCache (n := n)) (RegistrationNativePlatformSourceAccept.authenticate coins setup codec route verify pin packet) := by
  intro before previous result supported
  simp only [RegistrationNativePlatformSourceAccept.authenticate, StateT.run, map_apply, support_map] at supported
  obtain ⟨inner, called, same⟩ := supported
  cases same
  have native : inner.1 ∈ support ((RegistrationWorldAuthentication.begin setup codec route verify pin packet).run before.world.world.1) :=
    RegistrationNativePlatformHashReceipt.native_support coins
    ((RegistrationWorldAuthentication.begin setup codec route verify pin packet).run before.world.world.1) inner.1 previous inner.2 called
  unfold RegistrationWorldAuthentication.begin at native
  exact RegistrationWorldCache.program_cache setup codec route
    (RegistrationWorldAuthentication.program setup.source.crypto verify pin packet) before.world.world.1 inner.1 native

attribute [local irreducible] RegistrationNativePlatformSourceAccept.authenticate

private theorem afterPin (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks) (reserve : StateT Platform ProbComp Bool)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) (pin : RustM (core.option.Option session.ServerAuthenticationPin)) :
    Keeps (serverCache (n := n)) (RegistrationNativePlatformSourceAccept.afterPin coins setup codec checks (StateT.lift reserve)
      route verify representation created packet pin) := by
  unfold RegistrationNativePlatformSourceAccept.afterPin
  cases pin with
  | fail error | div => exact pure_keeps _
  | ok optional => cases optional with
    | none => exact pure_keeps _
    | some pin =>
      apply bind_keeps _ _ (authenticate coins setup codec route verify pin packet)
      intro checked
      cases checked with
      | fail error | div => exact pure_keeps _
      | ok pair =>
        rcases pair with ⟨events, status⟩
        cases status with
        | Accepted authenticated =>
          intro before previous result supported
          have same := afterAuthentication coins setup checks reserve representation created packet authenticated before previous result supported
          exact le_of_eq (congrArg Prod.snd same).symm
        | _ => exact pure_keeps _

/-- Every actual complete source acceptance outcome retains every earlier shared-cache entry, including all post-authentication failure branches. -/
theorem accept (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks) (reserve : StateT Platform ProbComp Bool)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) :
    Keeps (serverCache (n := n)) (RegistrationNativePlatformSourceAccept.accept coins setup codec checks reserve
      route verify representation created packet) := by
  unfold RegistrationNativePlatformSourceAccept.accept RegistrationNativePlatformSourceAccept.acceptWith
  exact bind_keeps _ _ (RegistrationNativePlatformBuildCache.pin coins)
    (afterPin coins setup codec checks reserve route verify representation created packet)

end BeaconcryptCore.Computational.RegistrationNativePlatformAcceptCache

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAcceptCache.afterAuthentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAcceptCache.afterAuthentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAcceptCache.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAcceptCache.accept
