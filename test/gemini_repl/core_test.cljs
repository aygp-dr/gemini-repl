(ns gemini-repl.core-test
  (:require [cljs.test :refer-macros [deftest testing is]]
            [gemini-repl.core :as core]))

(deftest test-get-log-level
  (testing "get-log-level returns a valid log level"
    ;; Test that it returns some valid log level (default or env-set)
    (let [level (core/get-log-level)]
      (is (string? level))
      (is (seq level)))))

(deftest test-should-log-level
  (testing "should-log-level? with debug level"
    (with-redefs [core/get-log-level (constantly "debug")]
      (is (true? (core/should-log-level? "debug")))
      (is (true? (core/should-log-level? "info")))))
  
  (testing "should-log-level? with info level"
    (with-redefs [core/get-log-level (constantly "info")]
      (is (false? (core/should-log-level? "debug")))
      (is (true? (core/should-log-level? "info")))))
  
  (testing "should-log-level? with unrecognized level"
    (with-redefs [core/get-log-level (constantly "error")]
      (is (false? (core/should-log-level? "debug")))
      (is (false? (core/should-log-level? "info"))))))

(deftest test-calculate-estimated-cost
  (testing "calculate-estimated-cost with valid token usage"
    (let [token-usage {:prompt-tokens 1000
                       :candidates-tokens 500
                       :total-tokens 1500}
          result (core/calculate-estimated-cost token-usage)]
      (is (number? result))
      (is (> result 0))))
  
  (testing "calculate-estimated-cost with nil input"
    (is (nil? (core/calculate-estimated-cost nil))))
  
  (testing "calculate-estimated-cost with missing tokens"
    (let [token-usage {:total-tokens 100}
          result (core/calculate-estimated-cost token-usage)]
      (is (number? result))
      (is (>= result 0)))))

(deftest test-confidence-indicator
  (testing "confidence-indicator with high confidence"
    (is (= "🟢" (core/confidence-indicator -0.01))))  ; ~99% confidence
  
  (testing "confidence-indicator with medium confidence"  
    (is (= "🟡" (core/confidence-indicator -0.2))))   ; ~82% confidence
  
  (testing "confidence-indicator with low confidence"
    (is (= "🔴" (core/confidence-indicator -1.0))))   ; ~37% confidence
  
  (testing "confidence-indicator with nil input"
    (is (nil? (core/confidence-indicator nil)))))

(deftest test-extract-token-usage
  (testing "extract-token-usage with valid body"
    (let [body #js {"usageMetadata" #js {"promptTokenCount" 100
                                         "candidatesTokenCount" 50
                                         "totalTokenCount" 150}}
          result (core/extract-token-usage body)]
      (is (map? result))
      (is (= 100 (:prompt-tokens result)))
      (is (= 50 (:candidates-tokens result)))
      (is (= 150 (:total-tokens result)))))
  
  (testing "extract-token-usage with missing metadata"
    (let [body #js {}
          result (core/extract-token-usage body)]
      (is (nil? result))))
  
  (testing "extract-token-usage with nil body"
    (is (nil? (core/extract-token-usage nil)))))