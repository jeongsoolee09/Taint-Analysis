(import re)


(defn collect-signatures []
  (with [org-file (open "builtin-collection.org" "r+")]
    (setv lines (->> (.readlines org-file)
                     (map (fn [s] (.lstrip s)))
                     (map (fn [s] (.rstrip s)))
                     (list))))
  (setv signatures (->> lines
                        (filter (fn [s] (.startswith s "- [X]")))
                        (map (fn [s] (cut s 6)))
                        (list)))
  signatures)


(defn handle-paramlist [paramlist]
  (setv split-on-comma (.split paramlist ", "))
  (setv mapfunc (fn [param-and-type] (->> param-and-type
                                          ((fn [s] (.split s " ")))
                                          (butlast)
                                          (reduce +))))
  (setv intypes (if (empty? paramlist)
                    (list)
                    (list (map mapfunc split-on-comma))))
  (if (empty? intypes)
      "()"
      (->> intypes
           (interpose ",")
           (reduce +)
           ((fn [s] (+ "(" s ")"))))))


;; we may need this later...
(defn process-signature [signature]
  (setv regex r"(:static\s)?(:protected\s)?(?P<rtntype>[a-zA-Z]+) (?P<class>[a-zA-Z]+)\.(?P<methname>[a-zA-Z]+)\((?P<paramlist>.*)\)")
  (setv match (re.search regex signature))
  (setv rtntype (.group match "rtntype"))
  (setv class (.group match "class"))
  (setv methname (.group match "methname"))
  (setv paramlist (.group match "paramlist"))
  (+ rtntype " " class "." methname (handle-paramlist paramlist)))


(defn extract-classname [signature]
  (setv regex r"(:static\s)?(:protected\s)?(?P<rtntype>[a-zA-Z]+) (?P<class>[a-zA-Z]+)\.(?P<methname>[a-zA-Z]+)\((?P<paramlist>.*)\)")
  (setv match (re.search regex signature))
  (when (is match None)
    (do (print signature)
        (raise AssertionError)))
  (setv classname (.group match "class"))
  classname)


(defn extract-methname [signature]
  (setv regex r"(:static\s)?(:protected\s)?(?P<rtntype>[a-zA-Z]+) (?P<class>[a-zA-Z]+)\.(?P<methname>[a-zA-Z]+)\((?P<paramlist>.*)\)")
  (setv match (re.search regex signature))
  (when (is match None)
    (do (print signature)
        (raise AssertionError)))
  (setv methname (.group match "methname"))
  methname)


(defn legalize-classname [classname]
  (+ (.lower (str (first classname))) (cut classname 1)))


(defn partition-by-class [signatures]
  ;; finding all class names.
  (setv class-acc (set))
  (for [signature signatures]
    (.add class-acc (extract-classname signature)))
  (setv mapfunc (fn [classname]
                  (setv acc (set))
                  (for [signature signatures]
                    (when (= classname (extract-classname signature))
                      (.add acc (extract-methname signature))))
                  (, classname (list acc))))
  (list (map mapfunc class-acc)))


(defn to-ocaml-list-separated [class-partition]
  (setv (, classname methnames) class-partition)
  (setv acc "")
  (+= acc f"let {(legalize-classname classname)} = [\n")
  (+= acc f"    { (, classname (first methnames)) }\n")
  (for [methname (rest methnames)]
    (+= acc f"  ; { (, classname methname) }\n"))
  (+= acc f"]\n\n")
  acc)


(defn to-ocaml-list-unseparated [signatures]
  (setv acc "")
  (setv head-sig (first signatures))
  (+= acc f"let methods = [\n")
  (+= acc f"    { (, (extract-classname head-sig) (extract-methname head-sig)) }\n")
  (for [signature (rest signatures)]
    (+= acc f"  ; { (, (extract_classname signature) (extract-methname signature)) }\n"))
  (+= acc f"]\n\n")
  acc)


(defn write-ocaml [ocaml-list-decl]
  (with [ml (open "defLocAliasModels.ml" "w+")]
    (for [decl ocaml-list-decl]
      (.write ml decl))))


(defmain []
  (->> (collect-signatures)
       (to-ocaml-list-unseparated)
       (write-ocaml)))
