(ns gemini-repl.core-test
  (:require [cljs.test :refer-macros [deftest is testing]]
            [gemini-repl.core :as core]))

(deftest format-response-test
  (testing "Format valid response"
    (let [mock-response #js {:candidates #js [#js {:content
                                                    #js {:parts
                                                         #js [#js {:text "Hello from Gemini!"}]}}]}]
      (is (= "Hello from Gemini!" (core/format-response mock-response)))))
  
  (testing "Handle nil response"
    (is (= "No response received" (core/format-response nil))))
  
  (testing "Handle malformed response"
    (is (string? (core/format-response #js {})))))

(deftest api-key-test
  (testing "API key is configured"
    (is (string? core/api-key))))
