# Averaging over the original supported prefix

`PqxdhRecordFactsOriginAverage.bind_le` applies a uniform continuation probability bound only to values in the support of the original prefix computation. The prefix distribution remains unchanged, with its full returned value available to the continuation. The theorem follows the existing VCVio supported-bind bound and translates it to the measure notation used by the record facts.

A consumer may put a complete prefix state, selected callback and saved continuation in that value. It must still prove the callback bound at every supported value; this lemma neither fixes a marginal key distribution nor conditions the prefix on later writer success. It introduces no source interface, primitive assumption, query count or selection factor. The attempted-seal scanner, exact source resumption and union over the source send budget remain consuming obligations.
