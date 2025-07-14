(ns gemini-repl.core
  (:require [cljs.nodejs :as nodejs]))

(nodejs/enable-util-print!)

(def readline (nodejs/require "readline"))
(def process (nodejs/require "process"))
(def https (nodejs/require "https"))
(def fs (nodejs/require "fs"))

(defonce rl (atom nil))

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
  
Type your prompt and press Enter to send to Gemini API."))

(defn clear-screen []
  (print "\033[2J\033[H"))

(defn show-stats []
  (println "\nSession Statistics:")
  (println "  Total requests: 0")
  (println "  Total tokens: 0")
  (println "  Session time: 0 minutes"))

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
  (log-entry "api_request" {:prompt_length (count prompt)
                             :model "gemini-1.5-flash"})
  (let [data (js/JSON.stringify
              #js {:contents
                   #js [#js {:parts
                             #js [#js {:text prompt}]}]})
        options #js {:hostname api-endpoint
                     :port 443
                     :path (str "/v1beta/models/gemini-1.5-flash:generateContent?key=" api-key)
                     :method "POST"
                     :headers #js {"Content-Type" "application/json"
                                   "Content-Length" (.-length data)}}
        start-time (.now js/Date)]
    
    (let [req (.request https options
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
                                               (callback response)))))))]
      (.on req "error" (fn [e]
                         (println "Error:" (.-message e))
                         (callback nil)))
      (.write req data)
      (.end req))))

(defn format-response [response]
  (if response
    (try
      (let [candidates (.-candidates response)
            content (-> candidates
                       (aget 0)
                       (.-content)
                       (.-parts)
                       (aget 0)
                       (.-text))]
        content)
      (catch js/Error e
        (str "Error parsing response: " (.-message e))))
    "No response received"))

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
      (empty? trimmed) nil
      :else (do
              (print "\nGemini: ")
              (make-request trimmed
                            (fn [response]
                              (println (format-response response))
                              (print "\n> ")
                              (.prompt @rl true)))))))

(defn show-banner []
  (try
    (let [banner-path "resources/repl-banner.txt"]
      (if (.existsSync fs banner-path)
        (print (.readFileSync fs banner-path "utf8"))
        (println "GEMINI REPL v0.1.0\n==================\n")))
    (catch js/Error _e
      (println "GEMINI REPL v0.1.0\n==================\n")))
  (println "Type /help for commands, /exit to quit.\n"))

(defn -main [& args]
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
