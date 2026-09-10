(ns gemini-repl.core
  (:require ["readline" :as readline]
            ["https" :as https]
            ["process" :as process]
            ["dotenv" :as dotenv]
            ["fs" :as fs]
            [clojure.string :as str]
            [clojure.spec.alpha :as s]
            [gemini-repl.specs :as specs]))

;; Load environment variables
(.config dotenv)

(defn get-env [key]
  (aget (.-env process) key))

(s/fdef get-env
  :args (s/cat :key ::specs/env-key)
  :ret (s/nilable string?))

;; Simple FIFO and file logging
(defn log-to-fifo [entry]
  (let [fifo-path (or (get-env "GEMINI_LOG_FIFO") "/tmp/gemini.fifo")]
    (when (get-env "GEMINI_LOG_ENABLED")
      (try
        ;; Use synchronous write for better FIFO compatibility
        (let [data (str (.stringify js/JSON (clj->js entry)) "\n")]
          (try
            (.appendFileSync fs fifo-path data)
            (catch js/Error _e
              ;; Silently ignore FIFO errors (no reader, etc.)
              nil)))
        (catch js/Error _e
          ;; Ignore errors to not disrupt REPL
          nil)))))

(s/fdef log-to-fifo
  :args (s/cat :entry ::specs/log-entry)
  :ret nil?)

(defn log-to-file [entry]
  (let [log-path (or (get-env "GEMINI_LOG_PATH") "./logs/gemini-repl.log")
        log-type (get-env "GEMINI_LOG_TYPE")]
    (when (and (get-env "GEMINI_LOG_ENABLED")
               (or (= log-type "both") (= log-type "file")))
      (try
        (let [data (str (.stringify js/JSON (clj->js entry)) "\n")]
          (.appendFileSync fs log-path data))
        (catch js/Error _e
          ;; Ignore errors to not disrupt REPL
          nil)))))

(s/fdef log-to-file
  :args (s/cat :entry ::specs/log-entry)
  :ret nil?)

(defn get-log-level []
  (or (get-env "GEMINI_LOG_LEVEL") "info"))

(s/fdef get-log-level
  :args (s/cat)
  :ret string?)

(defn should-log-level? [level]
  (let [current-level (get-log-level)]
    (case current-level
      "debug" true
      "info" (= level "info")
      false)))

(s/fdef should-log-level?
  :args (s/cat :level string?)
  :ret boolean?
  ;; only "info" passes, unless the current level is "debug"
  :fn (fn [{{:keys [level]} :args ret :ret}]
        (or (not ret) (= level "info") (= "debug" (get-log-level)))))

(defn log-entry [entry]
  (let [log-type (get-env "GEMINI_LOG_TYPE")
        level (or (:level entry) "info")]
    (when (should-log-level? level)
      (when (or (= log-type "both") (= log-type "fifo"))
        (log-to-fifo entry))
      (when (or (= log-type "both") (= log-type "file"))
        (log-to-file entry)))))

(s/fdef log-entry
  :args (s/cat :entry ::specs/log-entry)
  :ret nil?)

(defn create-interface []
  (.createInterface readline
                    #js {:input (.-stdin process)
                         :output (.-stdout process)
                         :prompt "gemini> "
                         :terminal true
                         :historySize 100}))

(s/fdef create-interface
  :args (s/cat)
  :ret some?)

(defn extract-token-usage [body]
  (try
    (when-let [usage (aget body "usageMetadata")]
      {:prompt-tokens (aget usage "promptTokenCount")
       :candidates-tokens (aget usage "candidatesTokenCount")
       :total-tokens (aget usage "totalTokenCount")})
    (catch js/Error _e nil)))

(s/fdef extract-token-usage
  :args (s/cat :body (s/nilable ::specs/response-body))
  :ret (s/nilable ::specs/token-usage)
  ;; a usage map exactly when the body carries usageMetadata
  :fn (fn [{{:keys [body]} :args ret :ret}]
        (= (some? ret) (some? (some-> body (aget "usageMetadata"))))))

(defn calculate-estimated-cost [token-usage]
  (when token-usage
    (let [input-cost-per-1k 0.00015  ; Gemini 2.0 Flash pricing (approximate)
          output-cost-per-1k 0.0006
          input-cost (* (or (:prompt-tokens token-usage) 0) (/ input-cost-per-1k 1000))
          output-cost (* (or (:candidates-tokens token-usage) 0) (/ output-cost-per-1k 1000))]
      (+ input-cost output-cost))))

(s/fdef calculate-estimated-cost
  :args (s/cat :token-usage (s/nilable ::specs/token-usage))
  :ret (s/nilable ::specs/estimated-cost)
  :fn (fn [{{:keys [token-usage]} :args ret :ret}]
        (= (nil? ret) (nil? token-usage))))

;; Session state for tracking cumulative usage
(defonce session-state (atom {:total-tokens 0 :total-cost 0.0}))

;; Conversation history for context
(defonce conversation-history (atom []))

(defn update-session-usage [token-usage estimated-cost]
  (when (and token-usage estimated-cost)
    (swap! session-state
           (fn [state]
             {:total-tokens (+ (:total-tokens state) (:total-tokens token-usage))
              :total-cost (+ (:total-cost state) estimated-cost)}))))

(s/fdef update-session-usage
  :args (s/cat :token-usage (s/nilable ::specs/token-usage)
               :estimated-cost (s/nilable ::specs/estimated-cost))
  :ret (s/nilable ::specs/session-state)
  :fn (fn [{{:keys [token-usage estimated-cost]} :args ret :ret}]
        (= (nil? ret) (or (nil? token-usage) (nil? estimated-cost)))))

(defn confidence-indicator [logprob]
  (when logprob
    (let [confidence (* 100 (js/Math.exp logprob))]
      (cond
        (> confidence 95) "🟢"
        (> confidence 80) "🟡"
        :else "🔴"))))

(s/fdef confidence-indicator
  :args (s/cat :logprob (s/nilable number?))
  :ret (s/nilable ::specs/confidence)
  :fn (fn [{{:keys [logprob]} :args ret :ret}]
        (= (nil? ret) (nil? logprob))))

(defn display-response-with-metadata [text token-usage estimated-cost duration logprob]
  (println (str "\n" text))
  (when (get-env "GEMINI_SHOW_METADATA")
    (let [duration-str (if (and duration (< duration 1000))
                         (str duration "ms")
                         (when duration (str (.toFixed (/ duration 1000) 1) "s")))]
      (println (str "\n["
                    (when-let [indicator (confidence-indicator logprob)]
                      (str indicator " "))
                    (when token-usage (str (:total-tokens token-usage) " tokens"))
                    (when estimated-cost (str " | $" (.toFixed estimated-cost 4)))
                    (when duration-str (str " | " duration-str))
                    "]")))))

(s/fdef display-response-with-metadata
  :args (s/cat :text (s/nilable string?)
               :token-usage (s/nilable ::specs/token-usage)
               :estimated-cost (s/nilable ::specs/estimated-cost)
               :duration (s/nilable ::specs/duration)
               :logprob (s/nilable number?))
  :ret nil?)

(defn separator []
  nil)

(s/fdef separator
  :args (s/cat)
  :ret nil?)

(defn make-request [api-key prompt callback]
  ;; Add user message to history
  (swap! conversation-history conj
         #js {:role "user"
              :parts #js [#js {:text prompt}]})

  (let [start-time (.now js/Date)
        data (.stringify js/JSON
                         #js {:contents (clj->js @conversation-history)})
        options #js {:hostname "generativelanguage.googleapis.com"
                     :port 443
                     :path "/v1beta/models/gemini-2.0-flash:generateContent"
                     :method "POST"
                     :headers #js {"x-goog-api-key" api-key
                                   "Content-Type" "application/json"
                                   "Content-Length" (.-length data)}}]

    ;; Log basic request
    (log-entry {:timestamp (.toISOString (js/Date.))
                :type "request"
                :level "info"
                :prompt prompt})

    ;; Log debug request with full details
    (log-entry {:timestamp (.toISOString (js/Date.))
                :type "request_debug"
                :level "debug"
                :request {:url (str "https://" (.-hostname options) (.-path options))
                          :method (.-method options)
                          :headers (js->clj (.-headers options))
                          :body (js->clj (.parse js/JSON data))
                          :timing {:start start-time}}
                :prompt prompt})

    (let [req (.request https options
                        (fn [^js res]
                          (let [chunks (atom [])]
                            (.on res "data" (fn [chunk] (swap! chunks conj chunk)))
                            (.on res "end"
                                 (fn []
                                   (let [end-time (.now js/Date)
                                         duration (- end-time start-time)]
                                     (try
                                       (let [body (.parse js/JSON (.concat js/Buffer (clj->js @chunks)))
                                             text (-> body
                                                      (aget "candidates")
                                                      (aget 0)
                                                      (aget "content")
                                                      (aget "parts")
                                                      (aget 0)
                                                      (aget "text"))
                                             token-usage (extract-token-usage body)
                                             estimated-cost (calculate-estimated-cost token-usage)
                                             logprob (try
                                                       (-> body
                                                           (aget "candidates")
                                                           (aget 0)
                                                           (aget "avgLogprobs"))
                                                       (catch js/Error _e nil))]

                                ;; Update session state
                                         (update-session-usage token-usage estimated-cost)

                                ;; Log basic response
                                         (log-entry {:timestamp (.toISOString (js/Date.))
                                                     :type "response"
                                                     :level "info"
                                                     :response text})

                                ;; Log debug response with full details
                                         (log-entry {:timestamp (.toISOString (js/Date.))
                                                     :type "response_debug"
                                                     :level "debug"
                                                     :request {:prompt prompt}
                                                     :response {:status (.-statusCode res)
                                                                :headers (js->clj (.-headers res))
                                                                :body (js->clj body)
                                                                :text text
                                                                :timing {:end end-time
                                                                         :duration-ms duration}}
                                                     :usage token-usage
                                                     :estimated-cost-usd estimated-cost
                                                     :session @session-state})

                                ;; Add assistant response to history
                                         (swap! conversation-history conj
                                                #js {:role "model"
                                                     :parts #js [#js {:text text}]})

                                         (callback nil {:text text
                                                        :token-usage token-usage
                                                        :estimated-cost estimated-cost
                                                        :duration duration
                                                        :logprob logprob}))
                                       (catch js/Error e
                                         (callback e nil)))))))))]
      (.on req "error" (fn [err] (callback err nil)))
      (.write req data)
      (.end req))))

(s/fdef make-request
  :args (s/cat :api-key string? :prompt string? :callback fn?)
  :ret some?)

(defn handle-command [cmd rl]
  (case cmd
    "/help" (do
              (println "\nCommands:")
              (println "  /help   - Show this help")
              (println "  /exit   - Exit the REPL")
              (println "  /clear  - Clear the screen")
              (println "  /debug  - Toggle debug logging")
              (println "  /stats  - Show session usage statistics")
              (println "  /context - Show conversation context")
              (println "\nOr type any text to send to Gemini\n"))
    "/exit" (do
              (println "Goodbye!")
              (.close rl)
              (.exit process 0))
    "/clear" (do
               (.write (.-stdout process) "\u001b[2J\u001b[0;0H")
               (.prompt rl))
    "/debug" (do
               (let [current-level (get-log-level)]
                 (if (= current-level "debug")
                   (do
                     (set! (.-GEMINI_LOG_LEVEL (.-env process)) "info")
                     (println "🔍 Debug logging disabled"))
                   (do
                     (set! (.-GEMINI_LOG_LEVEL (.-env process)) "debug")
                     (println "🔍 Debug logging enabled"))))
               (.prompt rl))
    "/stats" (do
               (let [stats @session-state]
                 (println "\n📊 Session Statistics:")
                 (println (str "  Total tokens used: " (:total-tokens stats)))
                 (println (str "  Estimated cost: $" (.toFixed (:total-cost stats) 6)))
                 (println (str "  Log level: " (get-log-level)))
                 (println))
               (.prompt rl))
    "/context" (do
                 (println "\n📜 Conversation Context:")
                 (println (str "Messages: " (count @conversation-history)))
                 (.prompt rl))
    (println (str "Unknown command: " cmd "\nType /help for commands"))))

(s/fdef handle-command
  :args (s/cat :cmd ::specs/command-line :rl some?)
  :ret nil?)

(defn handle-input [rl api-key input]
  (let [trimmed (.trim input)]
    (cond
      (empty? trimmed) (.prompt rl)
      (str/starts-with? trimmed "/") (handle-command trimmed rl)
      :else (do
              (println "\nThinking...")
              (make-request api-key trimmed
                            (fn [err result]
                              (if err
                                (println "Error:" (.-message err))
                                (if (string? result)
                      ;; Handle legacy string result
                                  (println (str "\n" result "\n"))
                      ;; Handle new metadata result
                                  (display-response-with-metadata
                                   (:text result)
                                   (:token-usage result)
                                   (:estimated-cost result)
                                   (:duration result)
                                   (:logprob result))))
                              (println)
                              (.prompt rl)))))))

(s/fdef handle-input
  :args (s/cat :rl some? :api-key string? :input ::specs/input)
  ;; returns whatever readline/https returned; nothing to promise
  :ret any?)

(defn show-banner []
  (if (.existsSync fs "resources/repl-banner.txt")
    (let [banner (.readFileSync fs "resources/repl-banner.txt" "utf8")]
      (print banner))
    ;; Fallback to current banner
    (do
      (println "\n🤖 Gemini API REPL")
      (println "================")
      (println "Type /help for commands\n"))))

(s/fdef show-banner
  :args (s/cat)
  :ret nil?)

(defn main []
  (let [api-key (get-env "GEMINI_API_KEY")]
    (if-not api-key
      (do
        (println "Error: GEMINI_API_KEY not set in environment")
        (.exit process 1))
      (let [rl (create-interface)]
        (show-banner)
        (.prompt rl)
        (.on rl "line"
             (fn [input]
               (handle-input rl api-key input)))))))

(s/fdef main
  :args (s/cat)
  :ret any?)

(defn ^:export -main [& _args]
  (main))

(s/fdef -main
  :args (s/cat :args (s/* string?))
  :ret any?)
