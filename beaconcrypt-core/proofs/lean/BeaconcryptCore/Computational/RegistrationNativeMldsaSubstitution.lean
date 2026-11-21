-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationAuthenticationMetadata
set_option warningAsError true

/-! The former Init ML credential-substitution receipts are retired. The current Init has four retained classical/PQ fields and no ML public key or ML signature field. Current accepted metadata and exact request provenance are established in RegistrationAuthenticationMetadata; no six-field credential-origin subject remains. -/
