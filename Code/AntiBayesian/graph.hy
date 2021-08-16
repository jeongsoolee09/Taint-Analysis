(require [hy.contrib.walk [let]])

(import json)
(import [traceback-with-variables [activate-by-import]])
(import [networkx :as nx])
(import [matplotlib.pyplot :as plt])
(import [networkx.drawing.nx-agraph [graphviz-layout]])

(defclass InvalidStatus [Exception]
  (defn --init-- [self msg]
    (setv self.msg msg)))


(defn parse-json []
  (with [jsonfile (open "/Users/jslee/Dropbox/Taint-Analysis/Code/benchmarks/realworld/relational-data-access/Chain.json")]
    (setv json-dict (json.load jsonfile)))
  json-dict)


(defn refine-json [parsed-json]
  (defn sublist? [sublist superlist]
    (for [left-index (range (+ (- (len superlist) (len sublist)) 1))]
      (setv superlist-slice (cut superlist left-index (+ left-index (len sublist))))
      (when (= sublist superlist-slice)
        (return True)))
    (return False))

  (setv parsed-json-copy (cut parsed-json))  ; to be destructively updated
  (setv combs (combinations parsed-json 2))
  (for [(, elem1 elem2) combs]
    (cond [(sublist? (get elem1 "chain") (get elem2 "chain"))
           (.remove parsed-json-copy elem1)]
          [(sublist? (get elem2 "chain") (get elem1 "chain"))
           (.remove parsed-json-copy elem2)]))
  parsed-json-copy)  ; destructively updated version.


(defn make-thread [json-chain]
  (setv current-state (get json-chain "defining_method"))

  (defn define-handler [activity]
    (setv new-state (, (get activity "current_method")
                       (get activity "location")))
    (setv current-state new-state)
    new-state)

  (defn call-handler [activity]
    (setv new-state (, (get activity "callee")
                       (get activity "location")))
    (setv current-state new-state)
    new-state)

  (defn redefine-handler [activity]
    (setv new-state (, (get activity "current_method")
                       (get activity "location")))
    (setv current-state new-state)
    new-state)

  (defn dead-handler [last-linum activity]
    (, (get activity "current_method")
       last-linum))

  (setv current-chain [])

  (for [activity (get json-chain "chain")]
    (setv status (get activity "status"))
    (cond [(= status "Define") (.append current-chain
                                        (define-handler activity))]
          [(= status "Call") (.append current-chain
                                      (call-handler activity))]
          [(= status "Redefine") (.append current-chain
                                          (redefine-handler activity))]
          [(= status "Dead") (let [last-activity (last current-chain)
                                   last-linum (second last-activity)]
                               (.append current-chain
                                        (dead-handler last-linum activity)))]
          [:else (raise (InvalidStatus status))]))
  current-chain)


(defn make-threads [refined-json]
  (list (map make-thread refined-json)))


(defn summarize-node [node]
  "return the summarized version of the node, which is a tuple of strings."
  (defn summarize-methname [full-signature]
    (->> full-signature
         ((fn [string] (get (.split string ".") 1)))
         ((fn [string] (get (.split string "(") 0)))))
  (defn summarize-locset-string [locset-string]
    (setv is-singleton? (= (.count locset-string "line") 1))
    (if is-singleton?
        (->> locset-string
             ((fn [string] (.strip string "{ ")))
             ((fn [string] (.strip string " }")))
             ((fn [string] (.strip string "line "))))
        (->> locset-string
             ((fn [string] (.strip string "{ ")))
             ((fn [string] (.strip string " }")))
             ((fn [string] (.replace string "line " ""))))))
  (assert (= (type node) tuple)) ; a node is a tuple
  (setv (, method-sig locset-string) node)
  (, (summarize-methname method-sig)
     (summarize-locset-string locset-string)))


(defn construct-graph [threads]
  (setv g (nx.DiGraph))
  (for [thread threads]
    (setv previous-state None)
    (for [current-state thread]
      (.add-node g (summarize-node current-state))
      (when previous-state
        (.add-edge g (summarize-node previous-state)
                   (summarize-node current-state)))
      (setv previous-state current-state)))
  g)


(defn draw-graph [graph]
  (plt.figure "sample graph" :dpi 1000)
  (nx.draw
    graph
    :with-labels True
    :pos (graphviz-layout graph :prog "dot"))
  (plt.savefig "graph.svg" :format "svg"))


(defclass ProbabiltyDistribution []
  "Represents a probability distribution of a node."
  (defn --init-- [self methname]
    (setv (. self methname) methname)
    (setv (. self src-prob) 0.25)
    (setv (. self sin-prob) 0.25)
    (setv (. self san-prob) 0.25)
    (setv (. self non-prob) 0.25))

  (defn --repr-- [self]
    f"[dist of {self.name} = (src: {self.src-prob}, sin: {self.sin-prob}, san: {self.san-prob}, non: {self.non-prob})]")

  (defn check-sanity [self]
    (assert (sum [(. self src-prob)
                  (. self sin-prob)
                  (. self san-prob)
                  (. self non-prob)]) 1))

  ;; ============ several probabability manipulators ============
  ;; They are just effectful functions; they return nothing useful!

  (defn boost-and-decrease [self amount add-to subtract-from]
    ;; add-to: string
    ;; subtract-from: string
    (setv add-to (cond [(= add-to "src") (. self src-prob)]
                       [(= add-to "sin") (. self sin-prob)]
                       [(= add-to "san") (. self san-prob)]
                       [(= add-to "non") (. self non-prob)]))
    (setv subtract-from (cond [(= add-to "src") (. self src-prob)]
                              [(= add-to "sin") (. self sin-prob)]
                              [(= add-to "san") (. self san-prob)]
                              [(= add-to "non") (. self non-prob)]))
    ;; boost `add-to`
    (setv add-to (+ add-to amount))
    ;; subtract from `subtract-from`
    (setv subtract-from (- subtract-from amount))
    (check-sanity))

  (defn flatten-dist [self]
    "Turn the distribution to its initial state."
    (setv (. self src-prob) 0.25)
    (setv (. self sin-prob) 0.25)
    (setv (. self san-prob) 0.25)
    (setv (. self non-prob) 0.25)
    (check-sanity))

  (defn boost-and-decrement-others [self add-to amount]
    "Boost a target by a given amount, and decrement each by 1/3 of that amount"
    (setv add-to (cond [(= add-to "src") (. self src-prob)]
                       [(= add-to "sin") (. self sin-prob)]
                       [(= add-to "san") (. self san-prob)]
                       [(= add-to "non") (. self non-prob)]))
    (setv decrement-amount (/ amount 3))
    ;; boost `add-to`
    (+= add-to amount)
    ;; subtract all others
    (cond [(is add-to (. self src-prob))
           (do
             (-= (. self sin-prob) decrement-amount)
             (-= (. self san-prob) decrement-amount)
             (-= (. self non-prob) decrement-amount))]
          [(is add-to (. self sin-prob))
           (do
             (-= (. self src-prob) decrement-amount)
             (-= (. self san-prob) decrement-amount)
             (-= (. self non-prob) decrement-amount))]
          [(is add-to (. self san-prob))
           (do
             (-= (. self src-prob) decrement-amount)
             (-= (. self sin-prob) decrement-amount)
             (-= (. self non-prob) decrement-amount))]
          [(is add-to (. self non-prob))
           (do
             (-= (. self src-prob) decrement-amount)
             (-= (. self sin-prob) decrement-amount)
             (-= (. self san-prob) decrement-amount))])
    (check-sanity)))


(defclass InferenceEngine []
  (defn --init-- [self graph]
    ;; need the network topology information!
    (setv (. self graph) graph))

  (defn --repr-- [self]
    "concat all the textual representation of each graph node."
    (setv acc "")
    (setv nodes (. self graph nodes))
    (for [node nodes]
      (+= acc )
      ))

  (defn infer-on [self]

    )

  (defn find-node-to-ask [self]

    )

  (defn ask [self]

    ))


(defn main []
  "main function for the REPL."
  (->> (parse-json)
       (refine-json)
       (make-threads)
       (construct-graph)
       (draw-graph)))


(defmain []
  "main function for running this as a script."
  (->> (parse-json)             ; raw parsed json
       (refine-json)            ; refined json, removed subchains
       (make-threads)           ; threads made from the refined json
       (construct-graph)        ; graph constructed with the threads
       (draw-graph)))


;; For the REPL
(comment
  (do
    (setv parsed-json (parse-json))
    (setv refined-json (refine-json parsed-json))
    (setv threads (make-threads refined-json))
    (setv sample-thread (get threads 0))
    (setv g (construct-graph threads))
    ))
