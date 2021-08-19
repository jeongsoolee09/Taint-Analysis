(import [networkx :as nx])
(import [networkx.algorithms :as nxalg])
(import argparse)
(import glob)


(defclass NoMatches [Exception]
  (defn --init-- [self cwd]
    (setv (. self cwd) cwd)))



(defclass DirectoryHandler []
  (defn find-callgraph-txt []
    (setv out (glob.glob "Callgraph.txt"))
    (if (= (len out) 0)
        (do (import os)
            (raise (NoMatches (os.getcwd))))
        out)))



(defclass FileReadParse []
  (defn reader [directory]
    (with [f (open directory "r+")]
      (->> (.readlines f)
           (map (fn [string] (.rstrip string))))))


  (defn parse-arrow [string]
    (tuple (.split string "->")))


  (with-decorator staticmethod
    (defn parse-file []
      (map parse-arrow (reader)))))



(defclass GraphHandler []
  (with-decorator staticmethod
    (defn construct-graph [parsed-file]
      (setv g (nx.DiGraph))
      (for [(, meth1 meth2) parsed-file]
        (.add-edge g meth1 meth2))
      g))


  (defn find-roots [graph]
    (filter (fn [node] (= (len (.out-edges graph node)) 0))
            (. graph nodes)))


  (defn find-leaves [graph]
    (filter (fn [node] (= (len (.in-edges graph node)) 0))
            (. graph nodes))))



(defclass Path []
  (defn --init-- [self node-list]
    (setv (. self node-list)))


  (defn --repr-- [self]
    (reduce + (butlast (interleave (. self node-list)
                                   (* [" --> "] (len node-list)))))))



(defclass PathFinder []
  (defn root-to-leaf-paths [graph]
    (setv roots (find-roots graph))
    (setv leaves (find-roots graph))
    (setv paths [])
    (for [root roots]
      (for [leaf leaves]
        (.append paths
                 (Path (list ((. nxalg simple-paths all-simple-paths)
                               graph root leaf))))))
    paths)


  (defn find-member-paths [node graph]
    (setv all-paths (root-to-leaf-paths graph))
    (setv member-paths [])
    (for [path all-paths]
      (when (in node path.node-list)
        (.append path member-paths)))
    member-paths))


(defmain []
  ;; argparse stuffs
  (setv parser (argparse.ArgumentParser))
  (.add_argument parser "method-sig"
                 :help "method signature to look up."
                 :type str)
  (setv args (parser.parse_args))

  (setv graph (->> (DirectoryHandler.find-callgraph-txt)
                   (FileReadParse.parse-file)
                   (GraphHandler.construct-graph)))
  (PathFinder.find-member-paths (args.method-sig) graph))
