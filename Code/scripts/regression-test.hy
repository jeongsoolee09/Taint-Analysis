(import os)

(setv to-test {:fabricated ["~/Taint-Analysis/Code/benchmarks/fabricated/WhatIWantExample.java"
                            "~/Taint-Analysis/Code/benchmarks/fabricated/ObjectFlowing.java"
                            "~/Taint-Analysis/Code/benchmarks/fabricated/ArrayExample.java"]
               :realworld ["~/Taint-Analysis/Code/benchmarks/realworld/relational-data-access"]})


(defn test-fabricated []
  (setv infer-run-rtn-codes (list (map (fn [java-file] (, java-file (.system os f"infer -g run -- javac {java-file}")))
                                       (:fabricated to-test))))
  (setv infer-spechunter-rtn-codes (list (map (fn [java-file] (, java-file (.system os f"infer spechunter")))
                                              (:fabricated to-test))))
  (, infer-run-rtn-codes infer-spechunter-rtn-codes))


(defn test-realworld []
  (setv infer-run-rtn-codes (list (map (fn [directory] (, directory (.system os f"infer -g run")))
                                       (:realworld to-test))))
  (setv infer-spechunter-rtn-codes (list (map (fn [directory] (, directory (.system os f"infer spechunter")))
                                              (:realworld to-test))))
  (, infer-run-rtn-codes infer-spechunter-rtn-codes))


(defn report [infer-run-rtn-codes infer-spechunter-rtn-codes]
  (print "==================== INFER-RUN RESULT ======================")
  (for [(, java-file rtn-code) infer-run-rtn-codes]
    (print (if (= rtn-code 0)
               f"Infer-Run Result for {java-file}: SUCCESS"
               f"Infer-Run Result for {java-file}: FAIL")))
  (print "==================== INFER-SPECHUNTER RESULT ======================")
  (for [(, java-file rtn-code) infer-spechunter-rtn-codes]
    (print (if (= rtn-code 0)
               f"Infer-Spechunter Result for {java-file}: SUCCESS"
               f"Infer-SpecHunter Result for {java-file}: FAIL"))))


(defmain []
  (setv fabricated-test-result (test-fabricated))
  (setv realworld-test-result (test-realworld))
  (report #*fabricated-test-result)
  (report #*realworld-test-result))
