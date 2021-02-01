(require [hy.contrib.walk [let]])

(import csv)
(import sklearn)
(import [pandas :as pd])
(import [itertools [dropwhile]])

(setv feature-df (pd.read-csv "../benchmarks/realworld/spring-guides/AggregateFeatureVector.csv"))


(setv fun (fn [string] (-> (.replace string "(SwanFeatureExtractor.Methname" "")
                           (remove-char "\"")
                           (remove-char " ")
                           (remove-char "\n"))))


(defn normalize-csv-value [dataframe]
  "Replace all stringified booleans into real booleans in a dataframe."
  (let [mapfunc (fn [x]
                  (cond [(= x "SwanFeatureExtractor.True") True]
                        [(= x "SwanFeatureExtractor.False") False]
                        [(in "SwanFeatureExtractor.Methname" x) (fun x)]
                        [:else x]))]
    (.applymap dataframe mapfunc)))


(defn remove-char [string char]
  (.replace string char ""))


(defmain []
  (normalize-csv-value feature-df))
