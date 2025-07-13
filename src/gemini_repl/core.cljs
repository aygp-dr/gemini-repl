(ns gemini-repl.core
  (:require ["readline" :as readline]
            ["https" :as https]
            ["process" :as process]
            ["dotenv" :as dotenv]
            [clojure.string :as str]))

;; Load environment variables
(.config dotenv)

(defn get-env [key]
  (aget (.-env process) key))

(defn create-interface []
  (.createInterface readline
    #js {:input (.-stdin process)
         :output (.-stdout process)
         :prompt "gemini> "}))

(defn make-request [api-key prompt callback]
  (let [data (.stringify js/JSON
               #js {:contents #js [#js {:parts #js [#js {:text prompt}]}]})
        options #js {:hostname "generativelanguage.googleapis.com"
                     :port 443
                     :path "/v1beta/models/gemini-2.0-flash:generateContent"
                     :method "POST"
                     :headers #js {"x-goog-api-key" api-key
                                   "Content-Type" "application/json"
                                   "Content-Length" (.-length data)}}]
    (let [req (.request https options
                (fn [res]
                  (let [chunks (atom [])]
                    (.on res "data" #(swap! chunks conj %))
                    (.on res "end"
                         #(try
                            (let [body (.parse js/JSON (.concat js/Buffer (clj->js @chunks)))
                                  text (-> body
                                           (aget "candidates")
                                           (aget 0)
                                           (aget "content")
                                           (aget "parts")
                                           (aget 0)
                                           (aget "text"))]
                              (callback nil text))
                            (catch js/Error e
                              (callback e nil)))))))]
      (.on req "error" #(callback % nil))
      (.write req data)
      (.end req))))

(defn handle-command [cmd rl]
  (case cmd
    "/help" (do
              (println "\nCommands:")
              (println "  /help   - Show this help")
              (println "  /exit   - Exit the REPL")
              (println "  /clear  - Clear the screen")
              (println "\nOr type any text to send to Gemini\n"))
    "/exit" (do
              (println "Goodbye!")
              (.close rl)
              (.exit process 0))
    "/clear" (.write (.-stdout process) "\u001b[2J\u001b[0;0H")
    (println (str "Unknown command: " cmd "\nType /help for commands"))))

(defn handle-input [rl api-key input]
  (let [trimmed (.trim input)]
    (cond
      (empty? trimmed) nil
      (str/starts-with? trimmed "/") (handle-command trimmed rl)
      :else (do
              (println "\nThinking...")
              (make-request api-key trimmed
                (fn [err result]
                  (if err
                    (println "Error:" (.-message err))
                    (println (str "\n" result "\n")))
                  (.prompt rl)))))))

(defn main []
  (let [api-key (get-env "GEMINI_API_KEY")]
    (if-not api-key
      (do
        (println "Error: GEMINI_API_KEY not set in environment")
        (.exit process 1))
      (let [rl (create-interface)]
        (println "\n🤖 Gemini API REPL")
        (println "================")
        (println "Type /help for commands\n")
        (.prompt rl)
        (.on rl "line"
             (fn [input]
               (handle-input rl api-key input)
               (when-not (#{"/exit"} (.trim input))
                 (.prompt rl))))))))

(defn ^:export -main [& args]
  (main))
