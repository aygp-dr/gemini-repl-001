(ns gemini-repl.specs-test
  "Generative checks for every pure s/fdef'd fn, plus data-spec sanity.
  Per https://clojure.org/guides/spec (Testing). No test here touches the
  network: make-request and everything that calls it are never invoked."
  (:require [cljs.test :refer [deftest is testing]]
            [clojure.set :as set]
            [clojure.spec.alpha :as s]
            [clojure.spec.test.alpha :as stest]
            [clojure.string :as str]
            [clojure.test.check]
            [clojure.test.check.clojure-test :refer [defspec]]
            [clojure.test.check.properties :as prop]
            [gemini-repl.core :as core]
            [gemini-repl.specs :as specs]))

(def ^:private check-opts {:clojure.spec.test.check/opts {:num-tests 50}})

;; Side-effecting fns: fdef'd for instrumentation, never generatively checked.
(def ^:private side-effecting
  `#{core/show-help core/clear-screen core/show-stats core/show-context ; print
     core/log-to-fifo core/log-to-file core/log-entry                   ; file/FIFO writes
     core/make-request core/process-input                               ; HTTPS to the Gemini API
     core/show-banner core/-main core/reload})

(defn- fdefd []
  (set (filter s/get-spec (stest/enumerate-namespace 'gemini-repl.core))))

;; cljs stest/check is a macro, so the checked fns are listed literally; the
;; last assertion keeps this list in sync with the fdefs in core.
(deftest fdefs-hold-under-generative-testing
  (let [results (stest/check `[core/format-response] check-opts)]
    (is (seq results) "expected at least one fdef'd fn to check")
    (doseq [r results]
      (testing (str (:sym r))
        (is (nil? (:failure r))
            (pr-str (stest/abbrev-result r)))))
    (is (= (set/difference (fdefd) side-effecting) (set (map :sym results)))
        "every fdef in core is either checked or listed as side-effecting")))

(deftest data-specs-generate-and-conform
  (doseq [k [::specs/command ::specs/message ::specs/history ::specs/response-body
             ::specs/formatted ::specs/log-data]]
    (testing (str k)
      (is (every? (fn [[v _]] (s/valid? k v)) (s/exercise k 10))))))

(defn- context-lines [out]
  (keep #(re-matches #"  (\d+)\. \[(user|model)\] (.*)" %) (str/split-lines out)))

;; History formatting: /context prints one numbered line per turn, in order,
;; with the content cut to 50 chars plus "...". Runs against a scratch
;; history and restores conversation-history afterwards.
(defspec show-context-lists-every-message 50
  (prop/for-all [history (s/gen ::specs/history)]
                (let [saved @core/conversation-history]
                  (try
                    (reset! core/conversation-history history)
                    (let [out (with-out-str (core/show-context))
                          lines (context-lines out)]
                      (if (empty? history)
                        (and (empty? lines) (str/includes? out "No conversation history yet."))
                        (and (= (map str (range 1 (inc (count history)))) (map second lines))
                             (= (map :role history) (map #(nth % 2) lines))
                             (= (map (fn [{:keys [content]}]
                                       (if (> (count content) 50) (str (subs content 0 50) "...") content))
                                     history)
                                (map #(nth % 3) lines)))))
                    (finally (reset! core/conversation-history saved))))))

(deftest real-values-conform
  (testing "the core_test response fixture"
    (let [mock #js {:candidates #js [#js {:content
                                          #js {:parts
                                               #js [#js {:text "Hello from Gemini!"}]}}]}]
      (is (s/valid? ::specs/response-body mock))
      (is (s/valid? ::specs/formatted (core/format-response mock)))
      (is (s/valid? ::specs/formatted (core/format-response nil)))))
  (testing "history turns as make-request stores them"
    (is (s/valid? ::specs/history [{:role "user" :content "Hello"}
                                   {:role "model" :content "Hi there!"}])))
  (testing "log payloads as make-request builds them"
    (is (s/valid? ::specs/log-data {:prompt_length 5 :model "gemini-1.5-flash"}))
    (is (s/valid? ::specs/log-data {:duration_ms 812 :status 200 :has_candidates true})))
  (testing "README commands"
    (is (every? #(s/valid? ::specs/command %) ["/help" "/exit" "/clear" "/stats"]))))
