---------------------------- MODULE api_client ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS
    API_ENDPOINT,
    MAX_RETRIES,
    TIMEOUT_MS

VARIABLES
    requestQueue,
    responseQueue,
    connectionState,
    retryCount,
    rateLimitRemaining

\* API States
ConnectionStates == {"disconnected", "connecting", "connected", "error"}

\* Request structure
Request == [
    id: Nat,
    prompt: STRING,
    config: [temperature: Real, maxTokens: Nat],
    timestamp: Nat
]

\* Response structure  
Response == [
    id: Nat,
    content: STRING,
    status: {"success", "error", "rate_limited"},
    latency: Nat
]

Init ==
    /\ requestQueue = <<>>
    /\ responseQueue = <<>>
    /\ connectionState = "disconnected"
    /\ retryCount = 0
    /\ rateLimitRemaining = 100

\* Send API request
SendRequest(req) ==
    /\ connectionState = "connected"
    /\ rateLimitRemaining > 0
    /\ requestQueue' = Append(requestQueue, req)
    /\ rateLimitRemaining' = rateLimitRemaining - 1

\* Handle rate limiting
HandleRateLimit ==
    /\ rateLimitRemaining = 0
    /\ connectionState' = "error"
    /\ UNCHANGED <<requestQueue, responseQueue, retryCount>>

\* Retry logic
RetryRequest(req) ==
    /\ retryCount < MAX_RETRIES
    /\ connectionState = "error"
    /\ retryCount' = retryCount + 1
    /\ SendRequest(req)

\* Liveness property: All requests eventually get responses
Liveness ==
    \A req \in Range(requestQueue):
        <>(
            \E resp \in Range(responseQueue):
                resp.id = req.id
        )

=============================================================================
