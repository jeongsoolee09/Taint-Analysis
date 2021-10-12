(import [urllib.request [urlopen]])
(import [bs4 [BeautifulSoup]])
(import re)


(defn scrape-interesting-relpaths []
  "scrape all interesting relpaths from documentation of the java collection system."
  (setv java-collection "https://docs.oracle.com/javase/8/docs/api/java/util/Collection.html")
  (setv html (urlopen java-collection))
  (setv bs (BeautifulSoup html :features "lxml"))
  (setv all-tags (.find-all bs "dd"))
  (setv all-known-subinterfaces (->> (get all-tags 2)
                                     (.findChildren)))
  (setv all-known-implementing-classes (->> (get all-tags 3)
                                            (.findChildren)))
  (setv see-also (->> (get all-tags 6)
                      (.findChildren)
                      (filter (fn [x] (not (empty? x.attrs))))
                      (list)))
  (->> (+ all-known-subinterfaces all-known-implementing-classes see-also)
       (map (fn [tag] (get (. tag attrs) "href")))
       (list)))


(defn relpath-to-abspath [relpath abspath]
  "convert a relative path to an absolute path"
  (setv relpath-splitted (.split relpath "/"))
  (setv abspath-splitted (.split abspath "/"))
  (setv abspath-cutoff (->> (drop (.count relpath-splitted "..")
                                  (rest (reversed abspath-splitted)))
                            (list)
                            (reversed)
                            (list)
                            (map (fn [string] (+ string "/")))
                            (list)
                            (reduce +)))
  (setv relpath-cutoff (->> (.split relpath "/")
                            (filter (fn [string] (!= string "..")))
                            (map (fn [string] (if (in ".html" string)
                                                  string
                                                  (+ string "/"))))
                            (list)
                            (reduce +)))
  (+ abspath-cutoff relpath-cutoff))


(setv sample-relpath "../../java/util/AbstractCollection.html")
(setv sample-url "https://docs.oracle.com/javase/8/docs/api/java/util/concurrent/DelayQueue.html")


;; Do we need this?
(defn handle-paramlist [paramlist-str]
  (cond [(= paramlist-str "()") ; input type is void.
         []]
        [(not-in "," paramlist-str) ; there are only 1 param.
         (raise TODO)] ;
        [(in "," paramlist-str) ; there are more than 1 params.
         (raise TODO)]
        [:else (raise TODO)])) ; what?


(defn scrape-method-off-page [page-url]
  "scraping methods off a page"
  (setv html (urlopen page-url))
  (setv parsed (BeautifulSoup html :features "lxml"))
  (setv trs (+ (.find-all (.find parsed "table" {"summary" "Method Summary table, listing methods, and an explanation"})
                          "tr" {"class" "altColor"})
               (.find-all (.find parsed "table" {"summary" "Method Summary table, listing methods, and an explanation"})
                          "tr" {"class" "rowColor"})))
  (setv class-or-interface-name (->> page-url
                                     ((fn [s] (.split s "/")))
                                     (last)
                                     ((fn [s] (.split s ".")))
                                     (first)))
  (->> trs
       (map (fn [tr] (do (setv colFirst-text (->> (.find tr "td" {"class" "colFirst"})
                                                  ((fn [tag] (. tag code text)))
                                                  ((fn [s] (.replace s "\xa0" " ")))))
                         (setv colLast-text (->> (.find tr "td" {"class" "colLast"})
                                                 ((fn [tag] (. tag code text)))
                                                 ((fn [s] (.replace s " " " ")))
                                                 ((fn [s] (.replace s "\n" " ")))
                                                 ((fn [s] (.replace s "\xa0" "")))
                                                 ((fn [s] (re.sub r",\s+" ", " s)))))
                         (, colFirst-text " " class-or-interface-name "." colLast-text))))
       (list)
       ((fn [lst] (sorted lst :key (fn [x] (get x 4)))))
       (map (fn [strings] (reduce + strings)))
       ((fn [signatures] (, class-or-interface-name (sorted signatures))))))


(defmain []
  (setv java-collection "https://docs.oracle.com/javase/8/docs/api/java/util/Collection.html")
  (setv interesting-relpaths (scrape-interesting-relpaths))
  (setv interesting-abspaths (->> interesting-relpaths
                                  (map (fn [relpath] (relpath-to-abspath relpath java-collection)))))
  (setv all-methods (->> interesting-abspaths
                         (map (fn [page-url] (scrape-method-off-page page-url)))))
  (with [org (open "builtin-collection.org" "w+")]
    (.write org "* Java Builtin Collection Methods\n\n")
    (for [(, class-or-interface-name methods) all-methods]
      (.write org f"** {class-or-interface-name}\n\n")
      (for [method methods]
        (.write org f"   - [ ] {method}\n"))
      (.write org "\n"))))
