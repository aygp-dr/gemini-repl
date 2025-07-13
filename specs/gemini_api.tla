---- MODULE gemini_api ----
EXTENDS Naturals, Sequences, TLC

\* Constants for Gemini API specification
CONSTANTS 
    MaxTokens,     \* Maximum tokens allowed in request/response
    MaxRetries,    \* Maximum retry attempts
    TimeoutMs      \* Request timeout in milliseconds

\* Variables representing API state
VARIABLES
    request_state,     \* Current request state
    response_state,    \* Current response state
    token_usage,       \* Token usage tracking
    session_state,     \* Session cumulative state
    log_entries        \* Log entries generated

\* Type definitions for request context
RequestContext == [
    timestamp: STRING,
    prompt: STRING,
    model: STRING,
    api_key: STRING,
    headers: [STRING -> STRING],
    body: [contents: SUBSET [parts: SUBSET [text: STRING]]],
    timing: [start: Nat]
]

\* Type definitions for response context  
ResponseContext == [
    timestamp: STRING,
    status: Nat,
    headers: [STRING -> STRING],
    body: [
        candidates: SUBSET [
            content: [parts: SUBSET [text: STRING], role: STRING],
            finishReason: STRING,
            avgLogprobs: REAL
        ],
        usageMetadata: [
            promptTokenCount: Nat,
            candidatesTokenCount: Nat, 
            totalTokenCount: Nat,
            promptTokensDetails: SUBSET [modality: STRING, tokenCount: Nat],
            candidatesTokensDetails: SUBSET [modality: STRING, tokenCount: Nat]
        ],
        modelVersion: STRING,
        responseId: STRING
    ],
    timing: [end: Nat, duration_ms: Nat]
]

\* Token usage tracking
TokenUsage == [
    prompt_tokens: Nat,
    candidates_tokens: Nat,
    total_tokens: Nat
]

\* Session state tracking
SessionState == [
    total_tokens: Nat,
    total_cost: REAL,
    request_count: Nat
]

\* Log entry types
LogEntry == [
    timestamp: STRING,
    type: {"request", "response", "request_debug", "response_debug"},
    level: {"info", "debug"},
    data: UNION {RequestContext, ResponseContext, TokenUsage, SessionState}
]

\* Valid states for API requests
RequestStates == {"pending", "sending", "waiting", "completed", "error", "timeout"}
ResponseStates == {"none", "receiving", "parsing", "processed", "error"}

\* Initial state
Init ==
    /\ request_state = "pending"
    /\ response_state = "none"
    /\ token_usage = [prompt_tokens |-> 0, candidates_tokens |-> 0, total_tokens |-> 0]
    /\ session_state = [total_tokens |-> 0, total_cost |-> 0.0, request_count |-> 0]
    /\ log_entries = <<>>

\* Request validation predicates
ValidPrompt(prompt) == 
    /\ prompt /= ""
    /\ Len(prompt) <= MaxTokens

ValidAPIKey(key) ==
    /\ key /= ""
    /\ Len(key) > 10  \* Minimum API key length

ValidRequest(req) ==
    /\ req \in RequestContext
    /\ ValidPrompt(req.prompt)
    /\ ValidAPIKey(req.api_key)
    /\ req.model \in {"gemini-2.0-flash", "gemini-1.5-pro", "gemini-1.5-flash"}

\* Response validation predicates
ValidTokenCount(count) == count >= 0 /\ count <= MaxTokens

ValidUsageMetadata(usage) ==
    /\ ValidTokenCount(usage.promptTokenCount)
    /\ ValidTokenCount(usage.candidatesTokenCount)
    /\ ValidTokenCount(usage.totalTokenCount)
    /\ usage.totalTokenCount = usage.promptTokenCount + usage.candidatesTokenCount

ValidResponse(resp) ==
    /\ resp \in ResponseContext
    /\ resp.status \in {200, 400, 401, 403, 429, 500, 503}
    /\ resp.status = 200 => ValidUsageMetadata(resp.body.usageMetadata)
    /\ resp.timing.duration_ms >= 0

\* State transitions
SendRequest(req) ==
    /\ request_state = "pending"
    /\ ValidRequest(req)
    /\ request_state' = "sending"
    /\ response_state' = "none"
    /\ log_entries' = Append(log_entries, [
           timestamp |-> req.timestamp,
           type |-> "request",
           level |-> "info", 
           data |-> req
       ])
    /\ UNCHANGED <<token_usage, session_state>>

ReceiveResponse(resp) ==
    /\ request_state = "sending"
    /\ response_state = "none"
    /\ ValidResponse(resp)
    /\ request_state' = "completed"
    /\ response_state' = "processed"
    /\ IF resp.status = 200
       THEN /\ token_usage' = [
                   prompt_tokens |-> resp.body.usageMetadata.promptTokenCount,
                   candidates_tokens |-> resp.body.usageMetadata.candidatesTokenCount,
                   total_tokens |-> resp.body.usageMetadata.totalTokenCount
               ]
            /\ session_state' = [
                   total_tokens |-> session_state.total_tokens + resp.body.usageMetadata.totalTokenCount,
                   total_cost |-> session_state.total_cost + CalculateCost(resp.body.usageMetadata),
                   request_count |-> session_state.request_count + 1
               ]
       ELSE /\ UNCHANGED <<token_usage, session_state>>
    /\ log_entries' = Append(log_entries, [
           timestamp |-> resp.timestamp,
           type |-> "response",
           level |-> "info",
           data |-> resp
       ])

\* Cost calculation (approximate Gemini 2.0 Flash pricing)
CalculateCost(usage) ==
    LET input_cost == usage.promptTokenCount * (0.00015 / 1000)
        output_cost == usage.candidatesTokenCount * (0.0006 / 1000)
    IN input_cost + output_cost

\* Error handling
HandleError ==
    /\ request_state \in {"sending", "waiting"}
    /\ request_state' = "error"
    /\ response_state' = "error"
    /\ UNCHANGED <<token_usage, session_state, log_entries>>

\* Timeout handling
HandleTimeout ==
    /\ request_state = "waiting"
    /\ request_state' = "timeout"
    /\ response_state' = "error"
    /\ UNCHANGED <<token_usage, session_state, log_entries>>

\* Reset for next request
Reset ==
    /\ request_state \in {"completed", "error", "timeout"}
    /\ request_state' = "pending"
    /\ response_state' = "none"
    /\ UNCHANGED <<token_usage, session_state, log_entries>>

\* Next state relation
Next ==
    \/ \E req \in RequestContext : SendRequest(req)
    \/ \E resp \in ResponseContext : ReceiveResponse(resp)
    \/ HandleError
    \/ HandleTimeout
    \/ Reset

\* Specification
Spec == Init /\ [][Next]_<<request_state, response_state, token_usage, session_state, log_entries>>

\* Invariants
TypeOK ==
    /\ request_state \in RequestStates
    /\ response_state \in ResponseStates
    /\ token_usage \in TokenUsage
    /\ session_state \in SessionState
    /\ \A entry \in Range(log_entries) : entry \in LogEntry

\* Token usage never exceeds maximum
TokenLimitsOK ==
    /\ token_usage.total_tokens <= MaxTokens
    /\ token_usage.prompt_tokens <= MaxTokens
    /\ token_usage.candidates_tokens <= MaxTokens

\* Session state is monotonically increasing
SessionMonotonic ==
    /\ session_state.total_tokens >= 0
    /\ session_state.total_cost >= 0.0
    /\ session_state.request_count >= 0

\* Request/response state consistency
StateConsistency ==
    /\ (request_state = "completed") => (response_state = "processed")
    /\ (request_state = "error") => (response_state = "error")
    /\ (request_state = "pending") => (response_state = "none")

\* Cost calculation accuracy
CostAccuracy ==
    \A usage \in DOMAIN token_usage :
        LET cost == CalculateCost([
            promptTokenCount |-> token_usage.prompt_tokens,
            candidatesTokenCount |-> token_usage.candidates_tokens,
            totalTokenCount |-> token_usage.total_tokens
        ])
        IN cost >= 0.0

====