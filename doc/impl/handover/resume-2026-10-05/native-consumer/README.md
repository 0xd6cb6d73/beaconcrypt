# Initialized acceptance and inside-event validation

Fourteen unchanged modules from Server25, Accept14 and InsideExclusion17 are integrated onto `3ead9cb5ed44f9c54f038ac647fd063a2c2172cc`. All 988 retained transitive dependency blobs match their reviewed source lanes. All fourteen direct Lean 4.34 checks and the combined root check passed, with 56 exact standard-only axiom guards and no forbidden placeholder/custom-axiom declarations. The reviewed inventory gate passed. These are focused integration checks, not an aggregate rebuild.

`closure.json` records exact source and retained dependency blobs. `review-manifest.json` binds the integration files. The direct, root and inventory receipts record commands and exit statuses. Direct logs are empty and enumerated in `direct-logs.txt`; complete root and inventory logs are compressed with their raw hashes in the receipts. Original independent semantic reviews are included. The separate integration review is recorded before publication.

`doc/impl/native-consumer-event-integration.md` explains each result and its full cost/scope. The native root retains its existing restricted-ROM interpretation. Source support and event exclusion supply no probability cancellation, global source/compiler coupling, freshness result or final cryptographic bound. No new Rust or ProVerif result or mutation campaign is claimed.
