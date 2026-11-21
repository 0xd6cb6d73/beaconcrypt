-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformAcceptCut
set_option warningAsError true

/-! The former platform Init ML protected-origin/forgery statements are retired because Init no longer carries an ML credential. Actual SourceAccept/AcceptCut retain the four required hash/Ed callbacks and the exact selected Server pin. Mandatory Server response ML origin is preserved in RegistrationNativePlatformResponseOrigin. -/
