-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSourceSeal
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedAuthentication
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySourceExecution
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkServer
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBundle
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkFinish
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionaryAuthentication
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionaryAgreement
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionaryCausal
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionarySecurity
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionaryRecords
import Lean.Elab.Command
/-! Regression checks for source-controller composition walk compiled declaration VALUES only. Merely importing an extracted refinement or mentioning it in a declaration type cannot satisfy a check. Final endpoint lists are installed only after those source corollaries are import-safe. -/
open Lean Elab Command
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards
private def declarationValue? : ConstantInfo →Option Expr
  | .defnInfo declaration=>some declaration.value
  | .thmInfo declaration=>some declaration.value
  | .opaqueInfo declaration=>some declaration.value
  | _=>none

private partial def valueClosure (environment : Environment) (pending : List Name)
    (visited : Std.HashSet Name) : Std.HashSet Name :=
  match pending with
  | []=>visited
  | currentName :: remaining =>
    if visited.contains currentName then valueClosure environment remaining visited else
    let visited:=visited.insert currentName
    match environment.find? currentName with
    | none=>valueClosure environment remaining visited
    | some declaration=>match declarationValue? declaration with
      | none=>valueClosure environment remaining visited
      | some value=>valueClosure environment (value.getUsedConstants.toList++remaining) visited

elab "#guard_source_value_dependencies " root:ident " includes " "[" required:ident,* "]" : command =>do
  let rootName←liftCoreM (realizeGlobalConstNoOverloadWithInfo root)
  let environment←getEnv
  let some rootDeclaration:=environment.find? rootName | throwErrorAt root "source endpoint declaration is unavailable"
  let some _:=declarationValue? rootDeclaration | throwErrorAt root "source endpoint has no declaration value"
  let closure:=valueClosure environment [rootName] {}
  for requiredSyntax in required.getElems do
    let requiredName←liftCoreM (realizeGlobalConstNoOverloadWithInfo requiredSyntax)
    let some (.thmInfo _):=environment.find? requiredName | throwErrorAt requiredSyntax "required source dependency must be a proved theorem"
    unless closure.contains requiredName do
      throwErrorAt root "source endpoint {rootName} does not reach source proof {requiredName} through declaration values"

#guard_source_value_dependencies RegistrationNativePlatformExtractedSourceSeal.build_source includes [
  RegistrationNativePlatformSourceSeal.build_source,
  BeaconcryptCore.Refinement.AdapterSealNative.source_native]
#guard_source_value_dependencies RegistrationNativePlatformExtractedAuthentication.accept_source includes [
  RegistrationNativePlatformAuthentication.init_source,
  BeaconcryptCore.Refinement.AdapterInitAuthenticationSourceLoop.program_authenticate]

/-- error: source endpoint BeaconcryptCore.Computational.RegistrationNativePlatformSourceSeal.build does not reach source proof BeaconcryptCore.Refinement.AdapterSealNative.source_native through declaration values -/
#guard_msgs in
#guard_source_value_dependencies RegistrationNativePlatformSourceSeal.build includes [BeaconcryptCore.Refinement.AdapterSealNative.source_native]

#guard_source_value_dependencies RegistrationNativePlatformOrdinarySourceExecution.guarded_source includes [
  BeaconcryptCore.Refinement.AdapterRecordStatefulSend.interpreted,
  BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.drive_source,
  BeaconcryptCore.Refinement.AdapterRecordFrameBytes.frame_bytes]
#guard_source_value_dependencies RegistrationNativePlatformExtractedSdkServer.Accept.sdk includes [
  BeaconcryptCore.Refinement.AdapterPublicServerEntry.source,
  BeaconcryptCore.Refinement.AdapterPublicServerEntryReceipt.sdk]
#guard_source_value_dependencies RegistrationNativePlatformExtractedSdkServer.Build.actual includes [
  RegistrationNativePlatformExtractedSourceSeal.sealing_source,
  BeaconcryptCore.Refinement.AdapterPublicServerBuildTrace.source]
#guard_source_value_dependencies RegistrationNativePlatformExtractedSdkBundle.fresh_complete includes [
  BeaconcryptCore.Refinement.AdapterPublicBundleLifetime.fresh_complete]
#guard_source_value_dependencies RegistrationNativePlatformExtractedSdkFinish.same_execution includes [
  BeaconcryptCore.Refinement.AdapterPublicFinishLifetime.same_execution]

#guard_source_value_dependencies RegistrationNativePlatformExtractedDictionaryAuthentication.protected_origin includes [
  BeaconcryptCore.Refinement.AdapterRecordStatefulSend.interpreted,
  BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.drive_source,
  BeaconcryptCore.Refinement.AdapterSealNative.source_native,
  BeaconcryptCore.Refinement.AdapterInitAuthenticationSourceLoop.program_authenticate,
  BeaconcryptCore.Refinement.AdapterAuthenticationStatefulResponse.source,
  BeaconcryptCore.Refinement.AdapterRecordFrameBytes.frame_bytes]
#guard_source_value_dependencies RegistrationNativePlatformExtractedDictionaryAgreement.bound includes [
  BeaconcryptCore.Refinement.AdapterRecordStatefulSend.interpreted,
  BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.drive_source,
  BeaconcryptCore.Refinement.AdapterSealNative.source_native,
  BeaconcryptCore.Refinement.AdapterInitAuthenticationSourceLoop.program_authenticate,
  BeaconcryptCore.Refinement.AdapterAuthenticationStatefulResponse.source,
  BeaconcryptCore.Refinement.AdapterRecordFrameBytes.frame_bytes,
  RegistrationNativePlatformOrdinaryAllOwnerAgreement.path,
  RegistrationNativePlatformOrdinaryCausalAgreement.path,
  RegistrationNativePlatformOrdinaryCausalRecordStage.path]
#guard_source_value_dependencies RegistrationNativePlatformExtractedDictionaryCausal.causal_bound includes [
  BeaconcryptCore.Refinement.AdapterRecordStatefulSend.interpreted,
  BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.drive_source,
  BeaconcryptCore.Refinement.AdapterSealNative.source_native,
  BeaconcryptCore.Refinement.AdapterInitAuthenticationSourceLoop.program_authenticate,
  BeaconcryptCore.Refinement.AdapterAuthenticationStatefulResponse.source,
  BeaconcryptCore.Refinement.AdapterRecordFrameBytes.frame_bytes]
#guard_source_value_dependencies RegistrationNativePlatformExtractedDictionarySecurity.lor includes [
  BeaconcryptCore.Refinement.AdapterRecordStatefulSend.interpreted,
  BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.drive_source,
  BeaconcryptCore.Refinement.AdapterSealNative.source_native,
  BeaconcryptCore.Refinement.AdapterInitAuthenticationSourceLoop.program_authenticate,
  BeaconcryptCore.Refinement.AdapterAuthenticationStatefulResponse.source,
  BeaconcryptCore.Refinement.AdapterRecordFrameBytes.frame_bytes]
#guard_source_value_dependencies RegistrationNativePlatformExtractedDictionarySecurity.app_weighted includes [
  BeaconcryptCore.Refinement.AdapterRecordStatefulSend.interpreted,
  BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.drive_source,
  BeaconcryptCore.Refinement.AdapterSealNative.source_native,
  BeaconcryptCore.Refinement.AdapterInitAuthenticationSourceLoop.program_authenticate,
  BeaconcryptCore.Refinement.AdapterAuthenticationStatefulResponse.source,
  BeaconcryptCore.Refinement.AdapterRecordFrameBytes.frame_bytes]

#guard_source_value_dependencies RegistrationNativePlatformExtractedDictionaryRecords.bound includes [
  BeaconcryptCore.Refinement.AdapterRecordStatefulSend.interpreted,
  BeaconcryptCore.Refinement.AdapterRecordStatefulReceive.drive_source,
  BeaconcryptCore.Refinement.AdapterSealNative.source_native,
  BeaconcryptCore.Refinement.AdapterInitAuthenticationSourceLoop.program_authenticate,
  BeaconcryptCore.Refinement.AdapterAuthenticationStatefulResponse.source,
  BeaconcryptCore.Refinement.AdapterRecordFrameBytes.frame_bytes]

end BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards
