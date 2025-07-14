(ns gemini-repl.core
  (:require [cljs.nodejs :as nodejs]))

(nodejs/enable-util-print!)

(def readline (nodejs/require "readline"))
(def process (nodejs/require "process"))
(def https (nodejs/require "https"))
(def fs (nodejs/require "fs"))

(defonce rl (atom nil))
(defonce conversation-history (atom []))

;; Forward declarations
(declare format-response)

;; Configuration
(def api-key (or (.-GEMINI_API_KEY (.-env process))
                 (throw (js/Error. "GEMINI_API_KEY environment variable is required"))))

(def api-endpoint "generativelanguage.googleapis.com")

;; Logging configuration
(def log-enabled (= "true" (.-GEMINI_LOG_ENABLED (.-env process))))
(def log-type (or (.-GEMINI_LOG_TYPE (.-env process)) "fifo"))
(def log-fifo (or (.-GEMINI_LOG_FIFO (.-env process)) "/tmp/gemini-repl.fifo"))
(def log-file (or (.-GEMINI_LOG_FILE (.-env process)) "logs/gemini-repl.log"))

;; Commands
(defn show-help []
  (println "
Gemini REPL Commands:
  /help    - Show this help message
  /exit    - Exit the REPL
  /clear   - Clear the screen
  /stats   - Show session statistics
  /context - Show conversation context
  
Type your prompt and press Enter to send to Gemini API."))

(defn clear-screen []
  (print "\033[2J\033[H"))

(defn show-stats []
  (println "\nSession Statistics:")
  (println "  Total requests: 0")
  (println "  Total tokens: 0")
  (println "  Session time: 0 minutes"))

(defn show-context []
  (println "\nConversation Context:")
  (if (empty? @conversation-history)
    (println "  No conversation history yet.")
    (doseq [[idx msg] (map-indexed vector @conversation-history)]
      (println (str "  " (inc idx) ". [" (:role msg) "] " 
                   (subs (:content msg) 0 (min 50 (count (:content msg)))) 
                   (when (> (count (:content msg)) 50) "..."))))))

;; Logging
(defn log-to-fifo [event-type data]
  (when (and log-enabled (or (= log-type "fifo") (= log-type "both")))
    (let [log-entry (js/JSON.stringify
                     #js {:timestamp (.toISOString (js/Date.))
                          :event event-type
                          :data (clj->js data)})]
      (try
        (.appendFileSync fs log-fifo (str log-entry "\n"))
        (catch js/Error _e
          ;; Silently ignore FIFO errors
          nil)))))

(defn log-to-file [event-type data]
  (when (and log-enabled (or (= log-type "file") (= log-type "both")))
    (let [log-entry (js/JSON.stringify
                     #js {:timestamp (.toISOString (js/Date.))
                          :event event-type
                          :data (clj->js data)})]
      (try
        (.appendFileSync fs log-file (str log-entry "\n"))
        (catch js/Error _e
          ;; Silently ignore file errors
          nil)))))

(defn log-entry [event-type data]
  (log-to-fifo event-type data)
  (log-to-file event-type data))

;; API Communication
(defn make-request [prompt callback]
  ;; Add user message to history
  (swap! conversation-history conj {:role "user" :content prompt})
  
  (log-entry "api_request" {:prompt_length (count prompt)
                             :model "gemini-1.5-flash"})
  
  ;; Build contents array with full conversation history
  (let [contents (clj->js (mapv (fn [msg]
                                   #js {:role (:role msg)
                                        :parts #js [#js {:text (:content msg)}]})
                                 @conversation-history))
        data (js/JSON.stringify #js {:contents contents})
        options #js {:hostname api-endpoint
                     :port 443
                     :path (str "/v1beta/models/gemini-1.5-flash:generateContent?key=" api-key)
                     :method "POST"
                     :headers #js {"Content-Type" "application/json"
                                   "Content-Length" (.-length data)}}
        start-time (.now js/Date)
        req (.request https options
                      (fn [res]
                        (let [chunks (atom [])]
                          (.on res "data" (fn [chunk]
                                            (swap! chunks conj chunk)))
                          (.on res "end" (fn []
                                           (let [body (.toString (.concat js/Buffer (clj->js @chunks)))
                                                 response (js/JSON.parse body)
                                                 duration (- (.now js/Date) start-time)]
                                             (log-entry "api_response" 
                                                        {:duration_ms duration
                                                         :status (.-statusCode res)
                                                         :has_candidates (boolean (.-candidates response))})
                                             ;; Add model response to history
                                             (let [formatted (format-response response)]
                                               (when (:content formatted)
                                                 (swap! conversation-history conj {:role "model" :content (:content formatted)}))
                                               (callback response))))))))]
    (.on req "error" (fn [e]
                       (println "Error:" (.-message e))
                       (callback nil)))
    (.write req data)
    (.end req)))

(defn format-response [response]
  (if response
    (try
      (let [candidates (.-candidates response)
            content (-> candidates
                       (aget 0)
                       (.-content)
                       (.-parts)
                       (aget 0)
                       (.-text))
            usage-metadata (.-usageMetadata response)
            total-tokens (.-totalTokenCount usage-metadata)
            ;; Rough cost estimate (Gemini 1.5 Flash pricing)
            cost (* total-tokens 0.0000001)
            confidence "🟢"]  ;; TODO: Determine from response
        {:content content
         :metadata {:tokens total-tokens
                    :cost cost
                    :confidence confidence}})
      (catch js/Error e
        {:content (str "Error parsing response: " (.-message e))
         :metadata nil}))
    {:content "No response received"
     :metadata nil}))

;; REPL Loop
(defn process-input [input]
  (let [trimmed (.trim input)]
    (cond
      (= trimmed "/help") (show-help)
      (= trimmed "/exit") (do
                            (println "Goodbye!")
                            (.close @rl)
                            (.exit process 0))
      (= trimmed "/clear") (clear-screen)
      (= trimmed "/stats") (show-stats)
      (= trimmed "/context") (show-context)
      (empty? trimmed) nil
      :else (do
              (print "\nGemini: ")
              (let [start-time (.now js/Date)]
                (make-request trimmed
                              (fn [response]
                                (let [formatted (format-response response)
                                      duration (/ (- (.now js/Date) start-time) 1000)]
                                  (println (:content formatted))
                                  (when-let [metadata (:metadata formatted)]
                                    (println (str "[" (:confidence metadata) " " 
                                                (:tokens metadata) " tokens | " 
                                                "$" (.toFixed (:cost metadata) 4) " | "
                                                (.toFixed duration 1) "s]")))
                                  (print "\n> ")
                                  (.prompt @rl true)))))))))

(defn show-banner []
  (try
    (let [banner-path "resources/repl-banner.txt"]
      (if (.existsSync fs banner-path)
        (print (.readFileSync fs banner-path "utf8"))
        (println "GEMINI REPL v0.1.0\n==================\n")))
    (catch js/Error _e
      (println "GEMINI REPL v0.1.0\n==================\n")))
  (println "Type /help for commands, /exit to quit.\n"))

(defn -main [& _args]
  (show-banner)
  (let [rl-interface (.createInterface readline
                                       #js {:input (.-stdin process)
                                            :output (.-stdout process)
                                            :prompt "> "})]
    (reset! rl rl-interface)
    
    (.on rl-interface "line"
         (fn [line]
           (process-input line)))
    
    (.on rl-interface "close"
         (fn []
           (println "\nGoodbye!")
           (.exit process 0)))
    
    (.prompt rl-interface)))

(defn reload []
  (println "Code reloaded!"))

(set! *main-cli-fn* -main)
