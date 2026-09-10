(ns gemini-repl.specs
  "Data specs for gemini-repl (https://clojure.org/guides/spec).
  Function specs (s/fdef) live next to each defn in gemini-repl.core.
  Generators are built inside thunks, so loading this ns never needs
  test.check (it is part of the release build)."
  (:require [clojure.spec.alpha :as s]
            [clojure.spec.gen.alpha :as gen]
            [clojure.string :as str]))

;; --- Environment ---

(def env-keys
  "Environment variables the REPL reads (see .env.example and README)."
  #{"GEMINI_API_KEY" "GEMINI_SHOW_METADATA" "GEMINI_LOG_ENABLED"
    "GEMINI_LOG_TYPE" "GEMINI_LOG_LEVEL" "GEMINI_LOG_FIFO" "GEMINI_LOG_PATH"})

(s/def ::env-key
  (s/with-gen (s/and string? #(re-matches #"[A-Za-z_][A-Za-z0-9_]*" %))
    #(gen/one-of [(gen/elements (sort env-keys))
                  (gen/fmap (fn [s] (str "GEMINI_TEST_" s)) (gen/string-alphanumeric))])))

(s/def ::log-level #{"debug" "info"})

;; --- REPL commands ---

(def commands
  "Slash commands handled by gemini-repl.core/handle-command."
  #{"/help" "/exit" "/clear" "/debug" "/stats" "/context"})

(s/def ::command commands)

;; A trimmed REPL line starting with "/", known or not.
(s/def ::command-line
  (s/with-gen (s/and string? #(str/starts-with? % "/"))
    #(gen/one-of [(s/gen ::command)
                  (gen/fmap (fn [s] (str "/" s)) (gen/string-alphanumeric))])))

;; Any line typed at the prompt.
(s/def ::input string?)

;; --- Conversation history (Gemini "contents" wire format) ---

(s/def :gemini-repl.part/text string?)
(s/def ::part (s/keys :req-un [:gemini-repl.part/text]))
(s/def ::parts (s/coll-of ::part :kind vector? :min-count 1 :gen-max 3))
(s/def ::role #{"user" "model"})
(s/def ::message (s/keys :req-un [::role ::parts]))
(s/def ::history (s/coll-of ::message :kind vector? :gen-max 8))

;; --- Usage, cost, confidence ---

(s/def :gemini-repl.usage/prompt-tokens (s/nilable nat-int?))
(s/def :gemini-repl.usage/candidates-tokens (s/nilable nat-int?))
(s/def :gemini-repl.usage/total-tokens (s/nilable nat-int?))
(s/def ::token-usage
  (s/keys :opt-un [:gemini-repl.usage/prompt-tokens
                   :gemini-repl.usage/candidates-tokens
                   :gemini-repl.usage/total-tokens]))

(s/def ::estimated-cost (s/double-in :min 0 :infinite? false :NaN? false))
;; Gemini's avgLogprobs: a natural log of a probability, so <= 0.
(s/def ::logprob (s/double-in :max 0 :infinite? false :NaN? false))
(s/def ::duration nat-int?)
(s/def ::confidence #{"🟢" "🟡" "🔴"})

;; --- Raw API response (a parsed JS object) ---

(defn- gen-usage-metadata []
  (gen/fmap (fn [[p c]] {"promptTokenCount" p
                         "candidatesTokenCount" c
                         "totalTokenCount" (+ p c)})
            (gen/tuple (gen/large-integer* {:min 0 :max 1000000})
                       (gen/large-integer* {:min 0 :max 1000000}))))

(defn- gen-response-body []
  (gen/fmap (fn [[text logprob usage]]
              (clj->js (cond-> {"candidates"
                                [{"content" {"role" "model" "parts" [{"text" text}]}
                                  "avgLogprobs" logprob}]}
                         usage (assoc "usageMetadata" usage))))
            (gen/tuple (gen/string-alphanumeric)
                       (s/gen ::logprob)
                       (gen/one-of [(gen/return nil) (gen-usage-metadata)]))))

(s/def ::response-body (s/with-gen object? gen-response-body))

;; --- Session state (gemini-repl.core/session-state) ---

(s/def :gemini-repl.session/total-tokens nat-int?)
(s/def :gemini-repl.session/total-cost ::estimated-cost)
(s/def ::session-state
  (s/keys :req-un [:gemini-repl.session/total-tokens
                   :gemini-repl.session/total-cost]))

;; --- make-request callback payload ---

(s/def :gemini-repl.result/text (s/nilable string?))
(s/def :gemini-repl.result/token-usage (s/nilable ::token-usage))
(s/def :gemini-repl.result/estimated-cost (s/nilable ::estimated-cost))
(s/def :gemini-repl.result/duration (s/nilable ::duration))
(s/def :gemini-repl.result/logprob (s/nilable ::logprob))
(s/def ::result
  (s/keys :req-un [:gemini-repl.result/text]
          :opt-un [:gemini-repl.result/token-usage
                   :gemini-repl.result/estimated-cost
                   :gemini-repl.result/duration
                   :gemini-repl.result/logprob]))

;; --- Log entries (log-entry / log-to-fifo / log-to-file) ---

(s/def :gemini-repl.log/timestamp string?)
(s/def :gemini-repl.log/type #{"request" "request_debug" "response" "response_debug"})
(s/def :gemini-repl.log/level ::log-level)
(s/def :gemini-repl.log/prompt string?)
(s/def ::log-entry
  (s/keys :req-un [:gemini-repl.log/timestamp :gemini-repl.log/type]
          :opt-un [:gemini-repl.log/level :gemini-repl.log/prompt]))
