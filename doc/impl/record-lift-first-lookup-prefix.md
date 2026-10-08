# Actual first-lookup prefixes

`PqxdhRecordLiftFirstLookupPrefix` links the existing first-selected-lookup suspension to the exact supported-prefix relation in `PqxdhRecordLiftAvailability`. The prefix retains the original adaptive continuation and entire private source state. It uses no conditioning, rejection sampling or replacement of an adversary continuation.

`scan_reaches` covers both outcomes: a completed scan reaches the original pure result, while a pending scan reaches the original selected query and its continuation. This law holds for any interpreter of the existing private services, and its support premise refers to executing the actual scanner. It assumes no cryptographic security or source reachability assertion.

`scan_safe` transports a checked original-program safety certificate through that derived prefix. `pending_query` exposes the certificate at the precise pre-query state, before the selected lookup consumes a reply. The predicate is an explicit operational parameter of these transport lemmas; source-specific availability must still be proved from initialization, not assumed as a new security contract.

`sampled_support` and `sampled_reaches` apply this relation to the existing initialized mixed-source sampler. Forgetting its missing-entry proof yields exactly the original sampled state and remainder. Both the missing-entry certificate and the original-prefix certificate therefore concern the same evaluated distribution, including paths that complete without using the selected coordinate. No additional random draw, filtering or conditioning is introduced.

The module contains five statements with exact standard-axiom guards. These are operational source lemmas, with no statistical loss or added query cost. They do not themselves establish the concrete global availability certificate, adjacent-policy equality or a secrecy bound. The source query-safety endpoint and its use in the chain hybrid remain separate joins.
