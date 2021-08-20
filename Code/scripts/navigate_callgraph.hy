(import [networkx :as nx])
(import [networkx.algorithms :as nxalg])
(import argparse)
(import glob)
(import [rich [print]])


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


  (defn find-roots [graph]
    (filter (fn [node] (= (len (.in-edges graph node)) 0))
            (. graph nodes)))


  (defn find-leaves [graph]
    (filter (fn [node] (= (len (.out-edges graph node)) 0))
            (. graph nodes))))



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
      (if (= string nodestr)
          (print f"[bold red]{string}[/bold red]")
          (print string)))))



(defclass PathFinder []
  (defn root-to-leaf-paths [graph]
    (setv roots (GraphHandler.find-roots graph))
    (setv leaves (GraphHandler.find-leaves graph))
    (setv all-paths [])
    (for [root roots]
      (for [leaf leaves]
        (setv paths (list ((. nxalg simple-paths all-simple-paths)
                            graph root leaf)))
        (when (not (empty? paths))
          (for [path paths]
            (.append all-paths
                     (Path path))))))
    all-paths)


  (defn find-member-paths [node graph]
    (setv all-paths (PathFinder.root-to-leaf-paths graph))
    (setv member-paths [])
    (for [path all-paths]
      (when (in node path.node-list)
        (.append member-paths path)))
    member-paths))


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
        (PathFinder.find-member-paths args.method-sig graph))
  (if (empty? res)
      (print "No matches!")
      (for [path res]
        (print (* "=" 40))
        (.highlight-node path args.method-sig))))
