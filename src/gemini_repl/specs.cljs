(ns gemini-repl.specs
  "Data specs for gemini-repl (https://clojure.org/guides/spec).
  Function specs (s/fdef) live next to each defn in gemini-repl.core.
  Generators are built inside thunks, so loading this ns never needs
  test.check (it is part of the release build)."
  (:require [clojure.spec.alpha :as s]
            [clojure.spec.gen.alpha :as gen]))

;; --- REPL commands ---

(def commands
  "Slash commands handled by gemini-repl.core/process-input."
  #{"/help" "/exit" "/clear" "/stats" "/context"})

(s/def ::command commands)

;; Any line typed at the prompt.
(s/def ::input string?)

;; --- Conversation history (clj maps; make-request turns them into
;; Gemini "contents" on the wire) ---

(s/def ::role #{"user" "model"})
(s/def :gemini-repl.message/content string?)
(s/def ::message (s/keys :req-un [::role :gemini-repl.message/content]))
(s/def ::history (s/coll-of ::message :kind vector? :gen-max 8))

;; --- Raw API response (a parsed JS object) ---

(defn- gen-usage-metadata []
  (gen/fmap (fn [[p c]] {"promptTokenCount" p
                         "candidatesTokenCount" c
                         "totalTokenCount" (+ p c)})
            (gen/tuple (gen/large-integer* {:min 0 :max 1000000})
                       (gen/large-integer* {:min 0 :max 1000000}))))

(defn- gen-response-body []
  (gen/fmap (fn [[text usage]]
              (clj->js (cond-> {"candidates"
                                [{"content" {"role" "model" "parts" [{"text" text}]}}]}
                         usage (assoc "usageMetadata" usage))))
            (gen/tuple (gen/string-alphanumeric)
                       (gen/one-of [(gen/return nil) (gen-usage-metadata)]))))

(s/def ::response-body (s/with-gen object? gen-response-body))

;; --- format-response result ---

(s/def :gemini-repl.metadata/tokens (s/nilable nat-int?))
;; NaN when usageMetadata lacks totalTokenCount (tokens undefined)
(s/def :gemini-repl.metadata/cost (s/nilable number?))
(s/def :gemini-repl.metadata/confidence #{"🟢" "🟡" "🔴"})
(s/def ::metadata
  (s/keys :req-un [:gemini-repl.metadata/tokens
                   :gemini-repl.metadata/cost
                   :gemini-repl.metadata/confidence]))

(s/def :gemini-repl.formatted/content (s/nilable string?))
(s/def :gemini-repl.formatted/metadata (s/nilable ::metadata))
(s/def ::formatted
  (s/keys :req-un [:gemini-repl.formatted/content
                   :gemini-repl.formatted/metadata]))

;; --- Log events (log-entry / log-to-fifo / log-to-file) ---

(s/def ::event-type #{"api_request" "api_response"})
(s/def ::log-data
  (s/map-of simple-keyword? (s/or :string string? :number number? :boolean boolean?)
            :gen-max 4))
