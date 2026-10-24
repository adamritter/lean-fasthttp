import FastHTTP.QuotedProofs
import FastHTTP.LimitsProofs
import FastHTTP.StreamMachineProofs
import FastHTTP.WireProofs
import FastHTTP.HeaderProofs
import FastHTTP.FeedProofs
import FastHTTP.NumericProofs
import FastHTTP.SyntaxProofs
import FastHTTP.ScannerProofs
import FastHTTP.BodyFastProofs

#print axioms FastHTTP.Protocol.payload_push_fold
#print axioms FastHTTP.Protocol.bodyList_fixed_partial
#print axioms FastHTTP.Protocol.bodyList_data_payload
#print axioms FastHTTP.Protocol.payload_toByteArray
#print axioms FastHTTP.Protocol.bodyBulk_fixed
#print axioms FastHTTP.Protocol.bodyBulk_data
#print axioms FastHTTP.Protocol.bodyLoop_split
#print axioms FastHTTP.Protocol.bodyBulk_refines
#print axioms FastHTTP.Protocol.bodyFastLoop_eq_bodyLoop
#print axioms FastHTTP.Protocol.decodeBody_eq_reference
#print axioms FastHTTP.Protocol.decodeBody_fragmentation
#print axioms FastHTTP.Protocol.decodeBody_done_bounds
#print axioms FastHTTP.Protocol.decodeBody_partition
#print axioms FastHTTP.Protocol.decodeBody_fixed_exact
#print axioms FastHTTP.Protocol.decodeBody_pipeline_suffix
#print axioms FastHTTP.Protocol.bodyAdvance_terminal
#print axioms FastHTTP.Protocol.bodyList_terminal
#print axioms FastHTTP.Protocol.bodyLoop_eq_fold
#print axioms FastHTTP.Protocol.bodyFeed_eq_fold
#print axioms FastHTTP.Protocol.bodyFeed_append
#print axioms FastHTTP.Protocol.bodyFeed_fragments
#print axioms FastHTTP.Protocol.bodyFeed_terminal
#print axioms FastHTTP.Protocol.bodyFeed_pipeline_suffix
#print axioms FastHTTP.Protocol.bodyAdvance_count_bounds
#print axioms FastHTTP.Protocol.bodyList_count_bounds
#print axioms FastHTTP.Protocol.bodyLoop_count_bounds
#print axioms FastHTTP.Protocol.decodeBodyReference_done_bounds
#print axioms FastHTTP.Protocol.decodeBodyReference_partition
#print axioms FastHTTP.Protocol.bodyByte_live
#print axioms FastHTTP.Protocol.bodyInitial_live
#print axioms FastHTTP.Protocol.bodyAdvance_shift
#print axioms FastHTTP.Protocol.bodyList_shift
#print axioms FastHTTP.Protocol.bodyFeed_shift
#print axioms FastHTTP.Protocol.bodyList_more
#print axioms FastHTTP.Protocol.bodyInitial_more_live
#print axioms FastHTTP.Protocol.bodyFeed_more_count
#print axioms FastHTTP.Protocol.bodyScan_result_shift
#print axioms FastHTTP.Protocol.decodeBodyReference_fragmentation
#print axioms FastHTTP.Protocol.bodyList_fixed_exact
#print axioms FastHTTP.Protocol.bodyFeed_fixed_exact
#print axioms FastHTTP.Protocol.scanFeed_append
#print axioms FastHTTP.Protocol.scanFeed_fragments
#print axioms FastHTTP.Protocol.scanByte_stopped
#print axioms FastHTTP.Protocol.scanFeed_stopped
#print axioms FastHTTP.Protocol.scanByte_absorbed
#print axioms FastHTTP.Protocol.scanList_absorbed
#print axioms FastHTTP.Protocol.scanLoop_eq_fold
#print axioms FastHTTP.Protocol.scanFeedFast_eq_scanFeed
#print axioms FastHTTP.Protocol.scanFeedFast_append
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
#print axioms FastHTTP.Protocol.scanByte_history
#print axioms FastHTTP.Protocol.scanList_reference
#print axioms FastHTTP.Protocol.scanFeedFast_reference
#print axioms FastHTTP.Protocol.classify_cr_iff
#print axioms FastHTTP.Protocol.classify_lf_iff

#print axioms FastHTTP.Protocol.decimalValue_mono
#print axioms FastHTTP.Protocol.decimalStep_iff
#print axioms FastHTTP.Protocol.decimalFold_none
#print axioms FastHTTP.Protocol.decimalFold_iff
#print axioms FastHTTP.Protocol.decimalLoop_eq_fold
#print axioms FastHTTP.Protocol.decimal_iff
#print axioms FastHTTP.Protocol.hexDigit_iff
#print axioms FastHTTP.Protocol.pathOctet_iff
#print axioms FastHTTP.Protocol.uriLoop_iff
#print axioms FastHTTP.Protocol.uriComponent_iff
#print axioms FastHTTP.Protocol.validPathQuery_iff

#print axioms FastHTTP.Protocol.append_unless_empty
#print axioms FastHTTP.Protocol.extract_prefix_append
#print axioms FastHTTP.Protocol.extract_suffix_append
#print axioms FastHTTP.Protocol.decodeBody_extract
#print axioms FastHTTP.Protocol.bodyStep_extract
#print axioms FastHTTP.Protocol.bodyStep_append
#print axioms FastHTTP.Protocol.bodyStep_append_start
#print axioms FastHTTP.Protocol.scanByte_bounds
#print axioms FastHTTP.Protocol.scanList_bounds
#print axioms FastHTTP.Protocol.scanFeedFast_bounds
#print axioms FastHTTP.Protocol.headStep_append
#print axioms FastHTTP.Protocol.feed_head_fragmentation
#print axioms FastHTTP.Protocol.feed_body_fragmentation
#print axioms FastHTTP.Protocol.feed_fragmentation
#print axioms FastHTTP.Protocol.initial_state_bound
#print axioms FastHTTP.Protocol.feed_initial_fragmentation
#print axioms FastHTTP.Protocol.feed_fragments
#print axioms FastHTTP.Protocol.bodyStep_bound
#print axioms FastHTTP.Protocol.headStep_bound
#print axioms FastHTTP.Protocol.feed_bound
#print axioms FastHTTP.Protocol.feed_body_no_continue

#print axioms FastHTTP.Protocol.token_iff
#print axioms FastHTTP.Protocol.fieldOctet_iff
#print axioms FastHTTP.Protocol.spanEnd_spec
#print axioms FastHTTP.Protocol.spanEnd_complete
#print axioms FastHTTP.Protocol.parseFieldLine_sound
#print axioms FastHTTP.Protocol.parseFieldLine_complete
#print axioms FastHTTP.Protocol.parseFieldLine_iff
#print axioms FastHTTP.Protocol.targetOctet_iff
#print axioms FastHTTP.Protocol.parseRequestLine_sound
#print axioms FastHTTP.Protocol.parseRequestLine_complete
#print axioms FastHTTP.Protocol.parseRequestLine_iff
#print axioms FastHTTP.Protocol.parseHeaders_loop_sound
#print axioms FastHTTP.Protocol.parseHeaders_sound
#print axioms FastHTTP.Protocol.parseHead_envelope

#print axioms FastHTTP.Protocol.hexValue_iff
#print axioms FastHTTP.Protocol.digitChar_hex
#print axioms FastHTTP.Protocol.digitChar_decimal
#print axioms FastHTTP.Protocol.numeral_single_byte
#print axioms FastHTTP.Protocol.numeral_alphabet
#print axioms FastHTTP.Protocol.numeral_roundtrip
#print axioms FastHTTP.Protocol.decimal_wire_encoding
#print axioms FastHTTP.Protocol.decimal_wire_roundtrip
#print axioms FastHTTP.Protocol.encodeChunk_wire

#print axioms FastHTTP.Protocol.streamStep_resource
#print axioms FastHTTP.Protocol.streamStep_done
#print axioms FastHTTP.Protocol.streamStep_pull_after_write
#print axioms FastHTTP.Protocol.streamStep_write_from_producer
#print axioms FastHTTP.Protocol.streamStep_head
#print axioms FastHTTP.Protocol.streamStep_legacy_chunk
#print axioms FastHTTP.Protocol.streamStep_legacy_eof
#print axioms FastHTTP.Protocol.streamStep_modern_eof
#print axioms FastHTTP.Protocol.streamTrace_resource
#print axioms FastHTTP.Protocol.streamTrace_release_once
#print axioms FastHTTP.Protocol.streamTrace_cleanup_complete
#print axioms FastHTTP.Protocol.streamCommands_head

#print axioms FastHTTP.Protocol.hexadecimalValue_mono
#print axioms FastHTTP.Protocol.hexadecimalStep_iff
#print axioms FastHTTP.Protocol.hexadecimalFold_none
#print axioms FastHTTP.Protocol.hexadecimalFold_iff
#print axioms FastHTTP.Protocol.hexadecimalLoop_eq_fold
#print axioms FastHTTP.Protocol.hexadecimal_iff
#print axioms FastHTTP.Protocol.chunkSize_numeral
#print axioms FastHTTP.Protocol.chunkSize_bound
#print axioms FastHTTP.Protocol.bodyByte_budget
#print axioms FastHTTP.Protocol.bodyInitial_budget
#print axioms FastHTTP.Protocol.bodyAdvance_budget
#print axioms FastHTTP.Protocol.bodyList_budget
#print axioms FastHTTP.Protocol.decodeBody_budget
#print axioms FastHTTP.Protocol.parseField_budget
#print axioms FastHTTP.Protocol.parseHeaders_loop_budget
#print axioms FastHTTP.Protocol.parseHeaders_budget
#print axioms FastHTTP.Protocol.chooseFraming_budget
#print axioms FastHTTP.Protocol.parseHead_budget
#print axioms FastHTTP.Protocol.bodyStep_protocolBudget
#print axioms FastHTTP.Protocol.headStep_protocolBudget
#print axioms FastHTTP.Protocol.feed_protocolBudget
#print axioms FastHTTP.Protocol.feed_request_body_bound

#print axioms FastHTTP.Protocol.quoteText_iff
#print axioms FastHTTP.Protocol.quotedTail_sound
#print axioms FastHTTP.Protocol.quotedTail_complete
#print axioms FastHTTP.Protocol.quotedTail_bounds
#print axioms FastHTTP.Protocol.quotedEnd_iff
