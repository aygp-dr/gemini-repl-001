(ns gemini-repl.core
  (:require [cljs.nodejs :as nodejs]))

(nodejs/enable-util-print!)

(def readline (nodejs/require "readline"))
(def process (nodejs/require "process"))
(def https (nodejs/require "https"))

(defonce rl (atom nil))

;; Configuration
(def api-key (or (.-GEMINI_API_KEY (.-env process))
                 (throw (js/Error. "GEMINI_API_KEY environment variable is required"))))

(def api-endpoint "generativelanguage.googleapis.com")

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

;; API Communication
(defn make-request [prompt callback]
  (let [data (js/JSON.stringify
              #js {:contents
                   #js [#js {:parts
                             #js [#js {:text prompt}]}]})
        options #js {:hostname api-endpoint
                     :port 443
                     :path (str "/v1beta/models/gemini-1.5-flash:generateContent?key=" api-key)
                     :method "POST"
                     :headers #js {"Content-Type" "application/json"
                                   "Content-Length" (.-length data)}}]
    
    (let [req (.request https options
                        (fn [res]
                          (let [chunks (atom [])]
                            (.on res "data" (fn [chunk]
                                              (swap! chunks conj chunk)))
                            (.on res "end" (fn []
                                             (let [body (.toString (.concat js/Buffer @chunks))
                                                   response (js/JSON.parse body)]
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
  (println "
╔═══════════════════════════════════╗
║        GEMINI REPL v0.1.0         ║
║   ClojureScript + Gemini API      ║
╚═══════════════════════════════════╝

Type /help for commands, /exit to quit.
"))

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
