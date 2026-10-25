import FastHTTP.ReadySignalProofs
import FastHTTP.SSEProofs
import FastHTTP.BatchProofs
import FastHTTP.ActionProofs
import FastHTTP.AuthorityProofs
import FastHTTP.PendingProofs
import FastHTTP.StreamingProofs
import FastHTTP.BodyFastProofs
import FastHTTP.BodyGrammarProofs
import FastHTTP.BodyLimitProofs
import FastHTTP.BodyProofs
import FastHTTP.ChunkGrammarProofs
import FastHTTP.DateSyntaxProofs
import FastHTTP.DriverInputProofs
import FastHTTP.DriverNativeProofs
import FastHTTP.DriverOutputProofs
import FastHTTP.DriverProgressProofs
import FastHTTP.DriverProofs
import FastHTTP.DriverRequestProofs
import FastHTTP.EndToEndProofs
import FastHTTP.FeedProofs
import FastHTTP.FieldsProofs
import FastHTTP.HeadGrammarProofs
import FastHTTP.HeaderLimitProofs
import FastHTTP.HeaderProofs
import FastHTTP.HeaderSemanticsProofs
import FastHTTP.HexProofs
import FastHTTP.IPv6Proofs
import FastHTTP.LexicalProofs
import FastHTTP.LimitsProofs
import FastHTTP.MessageGrammarProofs
import FastHTTP.NumericProofs
import FastHTTP.Proofs
import FastHTTP.QuotedProofs
import FastHTTP.ResponseProofs
import FastHTTP.ResponseSyntaxProofs
import FastHTTP.ScannerProofs
import FastHTTP.StreamMachineProofs
import FastHTTP.SyntaxProofs
import FastHTTP.TargetProofs
import FastHTTP.TrailerProofs
import FastHTTP.WireProofs

#print axioms FastHTTP.pending_stop_cancels
#print axioms FastHTTP.pending_stream_adopted
#print axioms FastHTTP.pending_close_idempotent
#print axioms FastHTTP.pending_take_once
#print axioms FastHTTP.pending_late_result
#print axioms FastHTTP.pending_cancel_before_resolve
#print axioms FastHTTP.pending_resolve_before_cancel
#print axioms FastHTTP.pending_taken_not_cancelled
#print axioms FastHTTP.sse_bad_event_rejected

#print axioms FastHTTP.checkedResponseFields
#print axioms FastHTTP.Response.create
#print axioms FastHTTP.StreamResponse.create
#print axioms FastHTTP.DateHeader.create
#print axioms FastHTTP.Protocol.regNameOctet_iff
#print axioms FastHTTP.Protocol.futureOctet_iff
#print axioms FastHTTP.Protocol.decimalOctet_iff
#print axioms FastHTTP.Protocol.spanEnd_eq_stop_iff
#print axioms FastHTTP.Protocol.validIPvFuture_iff
#print axioms FastHTTP.Protocol.validIPLiteral_iff
#print axioms FastHTTP.Protocol.validPort_iff
#print axioms FastHTTP.Protocol.regName_iff
#print axioms FastHTTP.Protocol.uriGrammar_octets
#print axioms FastHTTP.Protocol.regName_no_delimiters
#print axioms FastHTTP.Protocol.validAuthority_sound
#print axioms FastHTTP.Protocol.validAuthority_complete
#print axioms FastHTTP.Protocol.validAuthority_iff
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
#print axioms FastHTTP.Protocol.hex_is_token
#print axioms FastHTTP.Protocol.chunkSize_complete
#print axioms FastHTTP.Protocol.chunkSize_iff
#print axioms FastHTTP.Protocol.pair_witness
#print axioms FastHTTP.Protocol.bodyByte_grammar
#print axioms FastHTTP.Protocol.bodyWire_fold
#print axioms FastHTTP.Protocol.bodyList_live_wire
#print axioms FastHTTP.Protocol.bodyList_wire
#print axioms FastHTTP.Protocol.bodyScan_done_iff
#print axioms FastHTTP.Protocol.decodeBody_grammar_iff
#print axioms FastHTTP.Protocol.decodeChunked_grammar_iff
#print axioms FastHTTP.Protocol.bodyByte_budget
#print axioms FastHTTP.Protocol.bodyInitial_budget
#print axioms FastHTTP.Protocol.bodyAdvance_budget
#print axioms FastHTTP.Protocol.bodyList_budget
#print axioms FastHTTP.Protocol.decodeBody_budget
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
#print axioms FastHTTP.Protocol.space_iff
#print axioms FastHTTP.Protocol.spanEnd_whitespace
#print axioms FastHTTP.Protocol.spanEnd_token
#print axioms FastHTTP.Protocol.chunkExtension_sound
#print axioms FastHTTP.Protocol.chunkExtensions_sound
#print axioms FastHTTP.Protocol.token_not_space
#print axioms FastHTTP.Protocol.space_not_token
#print axioms FastHTTP.Protocol.chunkExtensions_lead
#print axioms FastHTTP.Protocol.chunkExtension_complete
#print axioms FastHTTP.Protocol.chunkExtensions_complete
#print axioms FastHTTP.Protocol.chunkExtensions_iff
#print axioms FastHTTP.Protocol.chunkSize_grammar
#print axioms FastHTTP.Protocol.dateNumber_iff
#print axioms FastHTTP.Protocol.validDateHeader_iff
#print axioms FastHTTP.Protocol.request_wire_suffix
#print axioms FastHTTP.Protocol.input_initial
#print axioms FastHTTP.Protocol.input_reject
#print axioms FastHTTP.Protocol.input_accept
#print axioms FastHTTP.Protocol.input_resume
#print axioms FastHTTP.Protocol.input_stream_command
#print axioms FastHTTP.Protocol.input_stream_event
#print axioms FastHTTP.Protocol.input_stop
#print axioms FastHTTP.Protocol.driver_step_input
#print axioms FastHTTP.Protocol.driver_replay_input
#print axioms FastHTTP.Protocol.input_shift_partition
#print axioms FastHTTP.Protocol.input_event_window
#print axioms FastHTTP.Protocol.input_shift_window
#print axioms FastHTTP.Protocol.read_octets_cons
#print axioms FastHTTP.Protocol.input_trace_origin
#print axioms FastHTTP.Protocol.driver_native_input_trace
#print axioms FastHTTP.Protocol.driver_native_input_origin
#print axioms FastHTTP.Protocol.driver_finalizer_weight
#print axioms FastHTTP.Protocol.driver_actual_cleanup
#print axioms FastHTTP.Protocol.driver_actual_cleanup_complete
#print axioms FastHTTP.Protocol.driver_actual_output_prefix
#print axioms FastHTTP.Protocol.driver_actual_graceful_output
#print axioms FastHTTP.Protocol.output_reject
#print axioms FastHTTP.Protocol.output_accept
#print axioms FastHTTP.Protocol.output_resume
#print axioms FastHTTP.Protocol.output_stop
#print axioms FastHTTP.Protocol.output_stream_command
#print axioms FastHTTP.Protocol.output_stream_head_safe
#print axioms FastHTTP.Protocol.output_stream_written_enabled
#print axioms FastHTTP.Protocol.output_stream_result_enabled
#print axioms FastHTTP.Protocol.output_stream_step
#print axioms FastHTTP.Protocol.output_stream_event
#print axioms FastHTTP.Protocol.driver_step_output
#print axioms FastHTTP.Protocol.driver_replay_output
#print axioms FastHTTP.Protocol.driver_output_prefixes
#print axioms FastHTTP.Protocol.driver_native_output_order
#print axioms FastHTTP.Protocol.stream_resume_gate
#print axioms FastHTTP.Protocol.reject_ne_handler
#print axioms FastHTTP.Protocol.stop_ne_handler
#print axioms FastHTTP.Protocol.stream_command_handler
#print axioms FastHTTP.Protocol.stream_event_handler
#print axioms FastHTTP.Protocol.driver_handler_gate
#print axioms FastHTTP.Protocol.active_reply_busy
#print axioms FastHTTP.Protocol.reject_reply_rank
#print axioms FastHTTP.Protocol.driver_reply_descent
#print axioms FastHTTP.Protocol.driver_eventual_reply
#print axioms FastHTTP.Protocol.driver_reject_empty
#print axioms FastHTTP.Protocol.driver_accept_empty
#print axioms FastHTTP.Protocol.driver_resume_empty
#print axioms FastHTTP.Protocol.driver_stream_resource
#print axioms FastHTTP.Protocol.driver_stop_resource
#print axioms FastHTTP.Protocol.driver_step_resource
#print axioms FastHTTP.Protocol.driver_replay_resource
#print axioms FastHTTP.Protocol.driver_native_resource
#print axioms FastHTTP.Protocol.driver_native_cleanup_at_most_acquired
#print axioms FastHTTP.Protocol.driver_native_cleanup_complete
#print axioms FastHTTP.Protocol.driver_initial_request_invariant
#print axioms FastHTTP.Protocol.driver_reject_valid
#print axioms FastHTTP.Protocol.driver_accept_valid
#print axioms FastHTTP.Protocol.driver_resume_valid
#print axioms FastHTTP.Protocol.driver_streamCommand_valid
#print axioms FastHTTP.Protocol.driver_streamEvent_valid
#print axioms FastHTTP.Protocol.driver_stop_valid
#print axioms FastHTTP.Protocol.driver_step_request_valid
#print axioms FastHTTP.Protocol.driver_replay_requests_valid
#print axioms FastHTTP.Protocol.driver_native_requests_valid
#print axioms FastHTTP.Protocol.request_wire_deterministic
#print axioms FastHTTP.Protocol.request_wire_body_bound
#print axioms FastHTTP.Protocol.complete_request_dispatch
#print axioms FastHTTP.Protocol.received_request_dispatch
#print axioms FastHTTP.Protocol.http11_end_to_end
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
#print axioms FastHTTP.Protocol.listSpace_iff
#print axioms FastHTTP.Protocol.connectionToken_sound
#print axioms FastHTTP.Protocol.connectionToken_complete
#print axioms FastHTTP.Protocol.connectionToken_iff
#print axioms FastHTTP.Protocol.connectionList_sound
#print axioms FastHTTP.Protocol.connectionList_complete
#print axioms FastHTTP.Protocol.connectionOptions_iff
#print axioms FastHTTP.Protocol.transferParameter_sound
#print axioms FastHTTP.Protocol.transferParameter_complete
#print axioms FastHTTP.Protocol.transferParameter_iff
#print axioms FastHTTP.Protocol.transferParameter_bounds
#print axioms FastHTTP.Protocol.transferParameters_sound
#print axioms FastHTTP.Protocol.transferParameters_bounds
#print axioms FastHTTP.Protocol.transferParameters_complete
#print axioms FastHTTP.Protocol.transferParameters_iff
#print axioms FastHTTP.Protocol.transferCoding_sound
#print axioms FastHTTP.Protocol.transferCoding_complete
#print axioms FastHTTP.Protocol.transferCoding_iff
#print axioms FastHTTP.Protocol.transferCoding_bounds
#print axioms FastHTTP.Protocol.transferList_sound
#print axioms FastHTTP.Protocol.transferList_complete
#print axioms FastHTTP.Protocol.transferCodings_iff
#print axioms FastHTTP.Protocol.parseHeaders_meaning_sound
#print axioms FastHTTP.Protocol.parseHeaders_meaning_complete
#print axioms FastHTTP.Protocol.parseHeaders_grammar_iff
#print axioms FastHTTP.Protocol.chooseFraming_grammar_iff
#print axioms FastHTTP.Protocol.parseHead_grammar_iff
#print axioms FastHTTP.Protocol.parseField_budget
#print axioms FastHTTP.Protocol.parseHeaders_loop_budget
#print axioms FastHTTP.Protocol.parseHeaders_budget
#print axioms FastHTTP.Protocol.chooseFraming_budget
#print axioms FastHTTP.Protocol.parseHead_budget
#print axioms FastHTTP.Protocol.parseHeaders_loop_sound
#print axioms FastHTTP.Protocol.parseHeaders_sound
#print axioms FastHTTP.Protocol.parseHead_envelope
#print axioms FastHTTP.Protocol.canonicalTrimmed_sound
#print axioms FastHTTP.Protocol.canonicalTrimmed_complete
#print axioms FastHTTP.Protocol.extract_octets
#print axioms FastHTTP.Protocol.decimal_success_span
#print axioms FastHTTP.Protocol.headerField_trim
#print axioms FastHTTP.Protocol.parseField_grammar_iff
#print axioms FastHTTP.Protocol.hexadecimalValue_mono
#print axioms FastHTTP.Protocol.hexadecimalStep_iff
#print axioms FastHTTP.Protocol.hexadecimalFold_none
#print axioms FastHTTP.Protocol.hexadecimalFold_iff
#print axioms FastHTTP.Protocol.hexadecimalLoop_eq_fold
#print axioms FastHTTP.Protocol.hexadecimal_iff
#print axioms FastHTTP.Protocol.chunkSize_numeral
#print axioms FastHTTP.Protocol.chunkSize_bound
#print axioms FastHTTP.Protocol.validDecOctet_sound
#print axioms FastHTTP.Protocol.validDecOctet_complete
#print axioms FastHTTP.Protocol.validDecOctet_iff
#print axioms FastHTTP.Protocol.validIPv4_iff
#print axioms FastHTTP.Protocol.validH16_iff
#print axioms FastHTTP.Protocol.ipv6Parts_sound
#print axioms FastHTTP.Protocol.ipv6Parts_complete
#print axioms FastHTTP.Protocol.ipv6Parts_iff
#print axioms FastHTTP.Protocol.ipv6Groups_iff
#print axioms FastHTTP.Protocol.validIPv6_iff
#print axioms FastHTTP.Protocol.decOctet_value_bound
#print axioms FastHTTP.Protocol.utf8IPv6_iff
#print axioms FastHTTP.Protocol.invalid_utf8_ipv6_rejected
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
#print axioms FastHTTP.Protocol.bodyStep_protocolBudget
#print axioms FastHTTP.Protocol.headStep_protocolBudget
#print axioms FastHTTP.Protocol.feed_protocolBudget
#print axioms FastHTTP.Protocol.feed_request_body_bound
#print axioms FastHTTP.Protocol.bodyStep_grammar_iff
#print axioms FastHTTP.Protocol.acknowledge_bodyStep
#print axioms FastHTTP.Protocol.acknowledge_continue_body
#print axioms FastHTTP.Protocol.headStep_grammar_iff
#print axioms FastHTTP.Protocol.feed_request_grammar_iff
#print axioms FastHTTP.Protocol.feed_fragmented_grammar_iff
#print axioms FastHTTP.Protocol.headStep_no_head_continue
#print axioms FastHTTP.Protocol.feed_continuation_bound
#print axioms FastHTTP.Protocol.acknowledge_append
#print axioms FastHTTP.Protocol.feed_acknowledged_fragmentation
#print axioms FastHTTP.Protocol.feed_acknowledged_fragments
#print axioms FastHTTP.Protocol.feed_live_fragments_grammar_iff
#print axioms FastHTTP.Protocol.acknowledge_bound
#print axioms FastHTTP.Protocol.acknowledge_idempotent
#print axioms FastHTTP.Protocol.acknowledge_initial_idempotent
#print axioms FastHTTP.Protocol.feed_empty_need
#print axioms FastHTTP.Protocol.decimalValue_mono
#print axioms FastHTTP.Protocol.decimalStep_iff
#print axioms FastHTTP.Protocol.decimalFold_none
#print axioms FastHTTP.Protocol.decimalFold_iff
#print axioms FastHTTP.Protocol.decimalLoop_eq_fold
#print axioms FastHTTP.Protocol.decimal_iff
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
#print axioms FastHTTP.Protocol.quoteText_iff
#print axioms FastHTTP.Protocol.quotedTail_sound
#print axioms FastHTTP.Protocol.quotedTail_complete
#print axioms FastHTTP.Protocol.quotedTail_bounds
#print axioms FastHTTP.Protocol.quotedEnd_iff
#print axioms FastHTTP.Protocol.status_wire_encoding
#print axioms FastHTTP.Protocol.prepared_buffers_grammar
#print axioms FastHTTP.Protocol.streaming_buffers_grammar
#print axioms FastHTTP.Protocol.encoded_chunk_grammar
#print axioms FastHTTP.Protocol.driver_prepared_buffers_grammar
#print axioms FastHTTP.Protocol.validOutputName_iff
#print axioms FastHTTP.Protocol.outputValueOctet_iff
#print axioms FastHTTP.Protocol.validFieldValue_iff
#print axioms FastHTTP.Protocol.validOutputReason_iff
#print axioms FastHTTP.Protocol.outputNameIs_iff
#print axioms FastHTTP.Protocol.outputFieldAllowed_iff
#print axioms FastHTTP.Protocol.scanByte_history
#print axioms FastHTTP.Protocol.scanList_reference
#print axioms FastHTTP.Protocol.scanFeedFast_reference
#print axioms FastHTTP.Protocol.classify_cr_iff
#print axioms FastHTTP.Protocol.classify_lf_iff
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
#print axioms FastHTTP.Protocol.hexDigit_iff
#print axioms FastHTTP.Protocol.pathOctet_iff
#print axioms FastHTTP.Protocol.uriLoop_iff
#print axioms FastHTTP.Protocol.uriComponent_iff
#print axioms FastHTTP.Protocol.validPathQuery_iff
#print axioms FastHTTP.Protocol.equals_loop_iff
#print axioms FastHTTP.Protocol.equals_iff
#print axioms FastHTTP.Protocol.delimited_iff
#print axioms FastHTTP.Protocol.alphaOctet_iff
#print axioms FastHTTP.Protocol.schemeOctet_iff
#print axioms FastHTTP.Protocol.pathGrammar_iff
#print axioms FastHTTP.Protocol.uriFuture_iff
#print axioms FastHTTP.Protocol.parseHierarchicalTarget_iff
#print axioms FastHTTP.Protocol.parseAbsoluteTarget_iff
#print axioms FastHTTP.Protocol.parseTarget_iff
#print axioms FastHTTP.Protocol.trimEnd_spec
#print axioms FastHTTP.Protocol.trimSpan_spec
#print axioms FastHTTP.Protocol.trimEnd_complete
#print axioms FastHTTP.Protocol.trimSpan_exact
#print axioms FastHTTP.Protocol.trailer_sound
#print axioms FastHTTP.Protocol.trailer_complete
#print axioms FastHTTP.Protocol.trailer_iff
#print axioms FastHTTP.Protocol.hexValue_iff
#print axioms FastHTTP.Protocol.digitChar_hex
#print axioms FastHTTP.Protocol.digitChar_decimal
#print axioms FastHTTP.Protocol.numeral_single_byte
#print axioms FastHTTP.Protocol.numeral_alphabet
#print axioms FastHTTP.Protocol.numeral_roundtrip
#print axioms FastHTTP.Protocol.decimal_wire_encoding
#print axioms FastHTTP.Protocol.decimal_wire_roundtrip
#print axioms FastHTTP.Protocol.encodeChunk_wire

#print axioms FastHTTP.Protocol.outputStringAll_iff
#print axioms FastHTTP.Protocol.outputStringAll_eq_all

#print axioms FastHTTP.Action.pure_ready

#print axioms FastHTTP.Action.io_ready

#print axioms FastHTTP.Action.context_scoped

#print axioms FastHTTP.Action.scoped_bind

#print axioms FastHTTP.Action.ready_bind

#print axioms FastHTTP.AsyncStream.ReadyBatch.append_data

#print axioms FastHTTP.AsyncStream.ReadyBatch.append_size

#print axioms FastHTTP.AsyncStream.ReadyBatch.payload_prefix

#print axioms FastHTTP.AsyncStream.ReadyBatch.payload_partition

#print axioms FastHTTP.AsyncStream.ReadyBatch.coalesce_pair

#print axioms FastHTTP.SSE.single_line_data_wire

#print axioms FastHTTP.ReadySignal.finish_before_register
#print axioms FastHTTP.ReadySignal.register_before_finish
#print axioms FastHTTP.ReadySignal.registration_delivery
#print axioms FastHTTP.ReadySignal.finish_is_ready
#print axioms FastHTTP.ReadySignal.finish_releases_waiter
#print axioms FastHTTP.ReadySignal.repeated_finish_no_notification
#print axioms FastHTTP.ReadySignal.unregister_preserves_ready
#print axioms FastHTTP.ReadySignal.unregister_releases_waiter
#print axioms FastHTTP.ReadySignal.finish_unregister_register
#print axioms FastHTTP.ReadySignal.unregister_finish_register
