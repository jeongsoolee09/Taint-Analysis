(import json)
(import [traceback-with-variables [activate-by-import]])
(import [networkx :as nx])
(import [matplotlib.pyplot :as plt])
(import [networkx.drawing.nx-agraph [graphviz-layout]])


(defclass InvalidStatus [Exception]
  (defn --init-- [self msg]
    (setv self.msg msg)))


(defclass TODO [Exception])


(defclass JsonHandler []
  (with-decorator staticmethod
    (defn parse-json []
      (with [jsonfile (open "/Users/jslee/Dropbox/Taint-Analysis/Code/benchmarks/realworld/relational-data-access/Chain.json")]
        (setv json-dict (json.load jsonfile)))
      json-dict))


  (with-decorator staticmethod
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
      parsed-json-copy)))  ; destructively updated version.


(defclass ThreadMaker []

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


  (with-decorator staticmethod
    (defn handle-spurious-dead [refined-json]
      (defn one-pass [refined-json-slice]
        (setv refined-json-chain (get refined-json-slice "chain"))
        (when (>= (len refined-json-chain) 3)
          (do
            (setv (, third-activity
                     second-activity
                     first-activity) (tuple (take 3 (reversed refined-json-chain))))
            (setv first-activity-is-call?
                  (= (get first-activity "status") "Call"))
            (setv second-activity-is-define?
                  (= (get second-activity "status") "Define"))
            (setv second-activity-using-matches-first-callee?
                  (if second-activity-is-define?
                      (do (setv first-activity-callee (get first-activity "callee"))
                          (setv second-activity-using (get second-activity "using"))
                          (= first-activity-callee second-activity-using))
                      False))
            (setv second-activity-defined-var-is-frontend?
                  (if second-activity-is-define?
                      (or (in "$irvar" (get second-activity "access_path"))
                          (in "$bcvar" (get second-activity "access_path")))
                      False))
            (setv third-activity-is-dead?
                  (= (get third-activity "status") "Dead"))
            (when (and first-activity-is-call?
                       second-activity-is-define?
                       second-activity-using-matches-first-callee?
                       second-activity-defined-var-is-frontend?
                       third-activity-is-dead?)
              (setv (get refined-json-slice "chain" (- (len refined-json-chain) 1) "current_method")
                    first-activity-callee)))))
      (for [refined-json-slice refined-json]
        (one-pass refined-json-slice))
      refined-json))


  (defn make-thread [json-chain]
    (setv current-state (get json-chain "defining_method"))
    (setv current-chain [])
    (for [activity (get json-chain "chain")]
      (setv status (get activity "status"))
      (cond [(= status "Define") (.append current-chain
                                          (ThreadMaker.define-handler activity))]
            [(= status "Call") (.append current-chain
                                        (ThreadMaker.call-handler activity))]
            [(= status "Redefine") (.append current-chain
                                            (ThreadMaker.redefine-handler activity))]
            [(= status "Dead") (do
                                 (setv last-activity (last current-chain))
                                 (setv last-linum (second last-activity))
                                 (.append current-chain
                                          (ThreadMaker.dead-handler last-linum activity)))]
            [:else (raise (InvalidStatus status))]))
    current-chain)


  (with-decorator staticmethod
    (defn make-threads [refined-json]
      (list (map ThreadMaker.make-thread refined-json)))))



(defclass GraphMaker []
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


  (with-decorator staticmethod
    (defn construct-graph [threads]
      (setv g (nx.DiGraph))
      (for [thread threads]
        (setv previous-state None)
        (for [current-state thread]
          (.add-node g (GraphMaker.summarize-node current-state))
          (when previous-state
            (.add-edge g (GraphMaker.summarize-node previous-state)
                       (GraphMaker.summarize-node current-state)))
          (setv previous-state current-state)))
      g))


  (with-decorator staticmethod
    (defn draw-graph [graph]
      (plt.figure "sample graph" :dpi 1000)
      (nx.draw
        graph
        :with-labels True
        :pos (graphviz-layout graph :prog "dot"))
      (plt.savefig "graph.svg" :format "svg"))))



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
    "check if this distribution is a valid one."
    (assert (sum [(. self src-prob)
                  (. self sin-prob)
                  (. self san-prob)
                  (. self non-prob)]) 1))

  ;; ============ several probabability manipulators ============

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
      (+= acc (+ ((. node --repr--)) "\n"))))


  (defn uncharted? [node]
    "do we have certainty on this node's distribution?")


  (defn find-node-to-ask [self]
    "find the uncharted nodes and pick one of them.")


  (defn ask [to-ask-node]
    (assert (= (type to-ask-node) ProbabilityDistribution))
    (setv response (input f"What is the label of {(. to-ask-node methname)}? ([src|sin|san|non]): "))
    (, to-ask-node response))


  (defn trigger-inference [self node label]
    "start propagation")

  ;; ============ Inference Rules ============


  (defn f [])

  ;; ============ Asking Rules ============


  (defn g [])

  )


(defmain []
  "main function for running this as a script."
  (->> (JsonHandler.parse-json)             ; raw parsed json
       (JsonHandler.refine-json)            ; refined json, removed subchains
       (ThreadMaker.make-threads)           ; threads made from the refined json
       (GraphMaker.construct-graph)         ; graph constructed with the threads
       (GraphMaker.draw-graph)))            ; visualize it


;; For the REPL
(comment
  (do
    (setv parsed-json (JsonHandler.parse-json))
    (setv refined-json (JsonHandler.refine-json parsed-json))
    (setv spurious-dead-handled (ThreadMaker.handle-spurious-dead refined-json))
    (setv threads (ThreadMaker.make-threads refined-json))
    (setv sample-thread (get threads 0))
    (setv g (GraphMaker.construct-graph threads))

    (defn main []
      "main function for the REPL."
      (->> (JsonHandler.parse-json)             ; raw parsed json
           (JsonHandler.refine-json)            ; refined json, removed subchains
           (ThreadMaker.make-threads)           ; threads made from the refined json
           (GraphMaker.construct-graph)         ; graph constructed with the threads
           (GraphMaker.draw-graph)))            ; visualize it
    ))
