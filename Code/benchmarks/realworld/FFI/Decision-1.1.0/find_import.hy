;;; finding the libraries used in the current project by looking at its import statements.

(import os.path)
(import os)
(import [pandas :as pd])
(import glob)


(setv exclude-keyword ["com.stratio.decision"
                       "siddhi."
                       "java."
                       "javax."])


;; all .java files in this project, and
;; all packages in this project.


(defn starts-with-import? [string]
  "Does the string start with an \"import\"?"
  (= (cut string 0 6) "import"))


(defn remove-import [string]
  "remove the leading \"import\" from the given string."
  (cut string 7 (len string)))


(defn collect-import-statements [filename]
  (with [javafile (open filename "r+")]
    (->> (.readlines javafile)
         (map (fn [c] (c.strip)))
         (map (fn [c] (c.rstrip ";")))
         (filter (fn [string] (starts-with-import? string)))
         (list))))


(setv *all-java-files* (->> (glob.glob "**/*.java" :recursive True)
                            (filter (fn [string] (not (in "/test/" string))))
                            (list))

      *all-packages* (->> *all-java-files*
                          (map collect-import-statements)
                          (map (fn [lst] (list (map remove-import lst))))
                          (flatten)
                          (remove (fn [package] (in exclude-keyword package)))
                          (list)))


(defn count-occurrence-of-package [target-package]
  (setv cnt 0)
  (for [package *all-packages*]
    (when (= package target-package)
      (+= cnt 1)))
  cnt)


;; organize them into a pandas dataframe.
;; columns = [libraries, count]
;; especially, count the occurrences of each library.


(defn count-occurrence-of-each-package []
  (->> *all-packages*
       (set)
       (map (fn [package] (, package (count-occurrence-of-package package))))
       (list)
       (pd.DataFrame)))


(defmain []
  (setv count-packages (count-occurrence-of-each-package))
  (print count-packages)
  (.to_csv count-packages "packages-count.csv"))
