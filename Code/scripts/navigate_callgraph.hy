(import [networkx :as nx])
(import [networkx.algorithms :as nxalg])
(import argparse)
(import glob)
(import [rich [print]])
(import [traceback-with-variables [activate-by-import]])


(defclass NoMatches [Exception]
  (defn --init-- [self cwd]
    (setv (. self cwd) cwd)))



(defclass TooManyMatches [Exception]
  (defn --init-- [self msg]
    (setv (. self msg) msg)))



(defclass DirectoryHandler []
  (defn find-callgraph-txt []
    (setv out (glob.glob "Callgraph.txt"))
    (cond [(= (len out) 0) (do (import os)
                               (raise (NoMatches (os.getcwd))))]
          [(= (len out) 1) (first out)]
          [(>= (len out) 2) (raise (TooManyMatches (str out)))])))



(defclass FileReadParse []
  (defn parse-arrow [string]
    (tuple (.split string " -> ")))


  (with-decorator staticmethod
    (defn parse-file [directory]
      (map FileReadParse.parse-arrow (with [f (open directory "r+")]
                                       (->> (.readlines f)
                                            (map (fn [string] (.rstrip string)))))))))



(defclass GraphHandler []
  (with-decorator staticmethod
    (defn construct-graph [parsed-file]
      (setv g (nx.DiGraph))
      (for [(, meth1 meth2) parsed-file]
        (.add-edge g meth1 meth2))
      g))


  (with-decorator staticmethod
    (defn root? [graph node]
      (= (len (.in-edges graph node)) 0)))


  (with-decorator staticmethod
    (defn leaf? [graph node]
      (= (len (.out-edges graph node)) 0)))


  (with-decorator staticmethod
    (defn find-roots [graph]
      (filter (fn [node] (GraphHandler.root? graph node)) (. graph nodes))))


  (with-decorator staticmethod
    (defn find-leaves [graph]
      (filter (fn [node] (GraphHandler.leaf? graph node)) (. graph nodes))))


  (with-decorator staticmethod
    (defn internal? [graph node]
      (not (or (GraphHandler.root? graph node)
               (GraphHandler.leaf? graph node))))))



(defclass Path []
  (defn --init-- [self node-list]
    (setv (. self node-list) node-list))


  (defn --repr-- [self]
    (reduce + (butlast (interleave (. self node-list)
                                   (* [" --> "] (len (. self node-list)))))))

  (defn highlight-node [self nodestr]
    (when (not (in nodestr (. self node-list)))
      (raise (NoMatches nodestr)))
    (setv str-list (butlast (interleave (. self node-list)
                                        (* [" --> "] (len (. self node-list))))))
    (for [string str-list]
      (if (= nodestr string)
          (print f"[bold red]{string}[/bold red]")
          (print string)))))



(defclass PathFinder []
  (defn from-root-to-target [graph target]
    (setv all-paths [])
    (setv roots (GraphHandler.find-roots graph))
    (for [root roots]
      (setv paths (list ((. nxalg simple-paths all-simple-paths)
                          graph root target)))
      (+= all-paths paths))
    all-paths)


  (defn from-target-to-leaf [graph target]
    (setv all-paths [])
    (setv leaves (GraphHandler.find-leaves graph))
    (for [leaf leaves]
      (setv paths (list ((. nxalg simple-paths all-simple-paths)
                          graph target leaf)))
      (+= all-paths paths))
    all-paths)


  (with-decorator staticmethod
    (defn find-context [graph target]
      (setv from-root-to-targets (PathFinder.from-root-to-target graph target))
      (setv from-target-to-leaf (PathFinder.from-target-to-leaf graph target))
      (setv carpro [])
      (for [p1 from-root-to-targets]
        (for [p2 from-target-to-leaf]
          (when (not (in "__" (last p2)))
            (setv concatted (+ p1 (list (rest p2))))
            (.append carpro (Path concatted)))))
       carpro)))



(defmain []
  (setv parser (argparse.ArgumentParser))
  (.add_argument parser "method_sig"
                 :help "method signature to look up."
                 :type str)
  (setv args (parser.parse_args))
  (setv graph (->> (DirectoryHandler.find-callgraph-txt)
                   (FileReadParse.parse-file)
                   (GraphHandler.construct-graph)))
  (setv res
        (PathFinder.find-context graph args.method-sig))
  (if (empty? res)
      (print "No matches!")
      (for [path res]
        (print (* "=" 40))
        (.highlight-node path args.method-sig))))


(comment
  ;; for the REPL
  (do
    (setv graph (->> (DirectoryHandler.find-callgraph-txt)
                     (FileReadParse.parse-file)
                     (GraphHandler.construct-graph)))
    (setv nodes graph.nodes)
    (setv roots (GraphHandler.find-roots graph))
    (setv leaves (GraphHandler.find-leaves graph))
    (setv target "void BlogPostContentRendererTests.rendersMultipleCallouts()")
    (setv target2 "byte[] GithubClient.downloadRepositoryAsZipball(String,String)")
    (PathFinder.from-target-to-leaf graph target)
    (PathFinder.from-root-to-target graph target)
    (GraphHandler.root? graph target)
    (GraphHandler.root? graph target2)
    (GraphHandler.leaf? graph target2)
    (GraphHandler.internal? graph target2)
    (in target2 nodes)
    (PathFinder.from-target-to-leaf graph target2)
    (PathFinder.from-root-to-target graph target2)
    (PathFinder.find-context graph target2)))
