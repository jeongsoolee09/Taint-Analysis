(import [networkx :as nx])
(import [networkx.algorithms :as nxalg])
(import glob)
(import [rich [print]])
;; (import [traceback-with-variables [activate-by-import]])


(defclass NoMatches [Exception]
  (defn --init-- [self cwd]
    (setv (. self cwd) cwd)))



(defclass TooManyMatches [Exception]
  (defn --init-- [self msg]
    (setv (. self msg) msg)))



(defclass DirectoryHandler []
  (defn find-callgraph-txt []
    (setv out (glob.glob "/Users/jslee/Dropbox/Taint-Analysis/Code/benchmarks/realworld/sagan/Callgraph.txt"))
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
               (GraphHandler.leaf? graph node)))))


  (with-decorator staticmethod
    (defn lookup [graph methname]
      (list (filter (fn [node] (in (+ (.lower methname) "(") (.lower node)))
                    (. graph nodes))))))



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


  (defn filter-Tests [paths]
    (filter (fn [path] (not (some (fn [node] (in "Test" node)) path)))
            paths))


  (defn filter-frontend [paths]
    (filter (fn [path] (not (some (fn [node] (in "__" node)) path)))
            paths))


  (with-decorator staticmethod
    (defn find-context [graph target]
      (setv out [])
      (cond
        [(GraphHandler.root? graph target)
         (do (setv from-target-to-leaf (->> (PathFinder.from-target-to-leaf graph target)
                                            (PathFinder.filter-Tests)
                                            (PathFinder.filter-frontend)))
             (for [p from-target-to-leaf]
               (.append out (Path p)))
             out)]
        [(GraphHandler.internal? graph target)
         (do (setv from-roots-to-target (->> (PathFinder.from-root-to-target graph target)
                                             (PathFinder.filter-Tests)
                                             (PathFinder.filter-frontend)))
             (setv from-target-to-leaf (->> (PathFinder.from-target-to-leaf graph target)
                                            (PathFinder.filter-Tests)
                                            (PathFinder.filter-frontend)))
             (for [p1 from-roots-to-target]
               (for [p2 from-target-to-leaf]
                 (setv concatted (+ p1 (list (rest p2))))
                 (.append out (Path concatted))))
             out)]
        [(GraphHandler.leaf? graph target)
         (do (setv from-roots-to-target (->> (PathFinder.from-root-to-target graph target)
                                             (PathFinder.filter-Tests)
                                             (PathFinder.filter-frontend)))
             (for [p from-roots-to-target]
               (.append out (Path p)))
             out)])))


  (with-decorator staticmethod
    (defn print-paths [pathlist]
      (for [path pathlist]
        (print (* "=" 50))
        (print path)))))



(defmain []
  (import argparse)
  (setv parser (argparse.ArgumentParser :description "Callgraph navigation wizard."))
  (.add_argument parser "--lookup"
                 :help "Lookup the given methname's signature."
                 :required False
                 :type str)
  (.add_argument parser "--find-context"
                 :help "Find the contexts the given method is in."
                 :required False
                 :type str)
  (.add_argument parser "--check-root"
                 :help "Check if a given method is a root."
                 :required False
                 :type str)
  (.add_argument parser "--check-leaf"
                 :help "Check if a given method is a leaf."
                 :required False
                 :type str)
  (setv args (parser.parse_args))
  (setv graph (->> (DirectoryHandler.find-callgraph-txt)
                   (FileReadParse.parse-file)
                   (GraphHandler.construct-graph)))

  ;; dispatch on command-line args
  (cond [args.lookup (do (setv res (GraphHandler.lookup graph args.lookup))
                         (if (empty? res)
                             (print "No matches!")
                             (for [sig res]
                               (print sig))))]
        [args.find-context (do (setv res (PathFinder.find-context graph args.find-context))
                               (if (empty? res)
                                   (print "No matches!")
                                   (for [path res]
                                     (print (* "=" 40))
                                     (.highlight-node path args.find-context)))
                               (print (* "=" 50))
                               (cond [(GraphHandler.root? graph args.find-context)
                                      (print f"{args.find-context} is a root!!")]
                                     [(GraphHandler.leaf? graph args.find-context)
                                      (print f"{args.find-context} is a leaf")]
                                     [:else
                                      (print f"{args.find-context} is an internal node")]))]
        [args.check-root (if (GraphHandler.root? graph args.check-root)
                             (print f"{args.check-root} is a root!")
                             (print f"{args.check-root} is not a root!"))]
        [args.check-leaf (if (GraphHandler.leaf? graph args.check-leaf)
                             (print f"{args.check-leaf} is a leaf!")
                             (print f"{args.check-leaf} is not a leaf!"))]))
