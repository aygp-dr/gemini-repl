(ns gemini-repl.specs-test
  "Generative checks for every pure s/fdef'd fn, plus data-spec sanity.
  Per https://clojure.org/guides/spec (Testing). No test here touches the
  network: make-request and everything that calls it are never invoked."
  (:require [cljs.test :refer [deftest is testing]]
            [clojure.set :as set]
            [clojure.spec.alpha :as s]
            [clojure.spec.test.alpha :as stest]
            [clojure.test.check]
            [clojure.test.check.clojure-test :refer [defspec]]
            [clojure.test.check.properties :as prop]
            [gemini-repl.core :as core]
            [gemini-repl.specs :as specs]))

(def ^:private check-opts {:clojure.spec.test.check/opts {:num-tests 50}})

;; Side-effecting fns: fdef'd for instrumentation, never generatively checked.
(def ^:private side-effecting
  `#{core/log-to-fifo core/log-to-file core/log-entry ; file/FIFO writes
     core/create-interface                            ; opens stdin
     core/update-session-usage                        ; swaps session-state (see below)
     core/display-response-with-metadata              ; prints
     core/handle-command core/show-banner             ; prints, may exit
     core/make-request core/handle-input              ; HTTPS to the Gemini API
     core/main core/-main})

(defn- fdefd []
  (set (filter s/get-spec (stest/enumerate-namespace 'gemini-repl.core))))

;; cljs stest/check is a macro, so the checked fns are listed literally; the
;; last assertion keeps this list in sync with the fdefs in core.
(deftest fdefs-hold-under-generative-testing
  (let [results (stest/check `[core/get-env core/get-log-level core/should-log-level?
                               core/extract-token-usage core/calculate-estimated-cost
                               core/confidence-indicator core/separator]
                             check-opts)]
    (is (seq results) "expected at least one fdef'd fn to check")
    (doseq [r results]
      (testing (str (:sym r))
        (is (nil? (:failure r))
            (pr-str (stest/abbrev-result r)))))
    (is (= (set/difference (fdefd) side-effecting) (set (map :sym results)))
        "every fdef in core is either checked or listed as side-effecting")))

(deftest data-specs-generate-and-conform
  (doseq [k [::specs/env-key ::specs/command ::specs/command-line ::specs/message
             ::specs/history ::specs/token-usage ::specs/response-body
             ::specs/session-state ::specs/result ::specs/log-entry]]
    (testing (str k)
      (is (every? (fn [[v _]] (s/valid? k v)) (s/exercise k 10))))))

;; State transition: update-session-usage adds one response's usage to the
;; running totals. Runs against a scratch value and restores session-state.
(defspec session-usage-accumulates 50
  (prop/for-all [start (s/gen ::specs/session-state)
                 usage (s/gen ::specs/token-usage)
                 cost (s/gen ::specs/estimated-cost)]
                (let [saved @core/session-state]
                  (try
                    (reset! core/session-state start)
                    (let [ret (core/update-session-usage usage cost)]
                      (and (= ret @core/session-state)
                           (= (:total-tokens ret) (+ (:total-tokens start) (or (:total-tokens usage) 0)))
                           (= (:total-cost ret) (+ (:total-cost start) cost))))
                    (finally (reset! core/session-state saved))))))

(deftest session-usage-ignores-incomplete-responses
  (let [saved @core/session-state]
    (try
      (reset! core/session-state {:total-tokens 7 :total-cost 0.5})
      (is (nil? (core/update-session-usage nil 0.1)))
      (is (nil? (core/update-session-usage {:total-tokens 3} nil)))
      (is (= {:total-tokens 7 :total-cost 0.5} @core/session-state))
      (finally (reset! core/session-state saved)))))

(deftest real-values-conform
  (testing "initial session state"
    (is (s/valid? ::specs/session-state {:total-tokens 0 :total-cost 0.0})))
  (testing "usage parsed from the core_test response fixture"
    (let [body #js {"usageMetadata" #js {"promptTokenCount" 100
                                         "candidatesTokenCount" 50
                                         "totalTokenCount" 150}}
          usage (core/extract-token-usage body)]
      (is (s/valid? ::specs/response-body body))
      (is (s/valid? ::specs/token-usage usage))
      (is (s/valid? ::specs/estimated-cost (core/calculate-estimated-cost usage)))))
  (testing "a history turn as make-request builds it"
    (is (s/valid? ::specs/message
                  (js->clj #js {:role "user" :parts #js [#js {:text "hi"}]}
                           :keywordize-keys true))))
  (testing "README commands"
    (is (every? #(s/valid? ::specs/command-line %) specs/commands))))
