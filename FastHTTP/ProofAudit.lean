import FastHTTP.Proofs

#print axioms FastHTTP.Protocol.scanFeed_append
#print axioms FastHTTP.Protocol.scanFeed_fragments
#print axioms FastHTTP.Protocol.scanByte_stopped
#print axioms FastHTTP.Protocol.scanFeed_stopped
#print axioms FastHTTP.Protocol.conflicting_framing_rejected
#print axioms FastHTTP.Protocol.fixed_framing_exact
#print axioms FastHTTP.Protocol.takeCount_bounds
#print axioms FastHTTP.Protocol.takeCount_conservation
#print axioms FastHTTP.Protocol.takeCount_fragmentation
#print axioms FastHTTP.Protocol.takeBody_bounds
#print axioms FastHTTP.Protocol.takeBody_size
#print axioms FastHTTP.Protocol.takeBody_partition
#print axioms FastHTTP.Protocol.takeBody_complete
#print axioms FastHTTP.Protocol.takeBody_bytes_fragmentation
#print axioms FastHTTP.Protocol.head_has_no_body
#print axioms FastHTTP.Protocol.no_content_has_no_body
#print axioms FastHTTP.Protocol.not_modified_has_no_body
#print axioms FastHTTP.Protocol.no_content_omits_length
#print axioms FastHTTP.Protocol.response_length_exact
