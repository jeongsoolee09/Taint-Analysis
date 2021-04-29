(import [pandas :as pd])
(import os.path)
(import os)
(import [functools [reduce]])


(setv root (os.path.join "/Users" "jslee" "Taint-Analysis" "Code"
                         "benchmarks" "realworld" "spring-guides"))


(setv dirs (->> (os.listdir :path root)
                (filter (fn [x] (in "gs" x)))
                (list)))


(defn one-pass [directory]
  "Read the SwanFeatures.csv residing in /complete
   and return it."
  (setv path (os.path.join directory "complete"))
  (os.chdir path)
  (print path)
  (try
    (pd.read_csv "SwanFeatures.csv")
    (except []
      (pd.DataFrame))))


(defmain []
  (os.chdir root)
  (setv acc (pd.DataFrame))
  (for [directory dirs]
    (setv acc (.append acc (one-pass directory)))
    (os.chdir root))
  (.to_csv acc "AggregateFeatureVector.csv" :mode "w+"))
