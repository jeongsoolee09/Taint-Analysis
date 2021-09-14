(import [urllib.request [urlopen]])
(import [bs4 [BeautifulSoup]])
(import re)


;; get the interesting relative paths

(setv java-collection "https://docs.oracle.com/javase/8/docs/api/java/util/Collection.html")
(setv html (urlopen java-collection))
(setv bs (BeautifulSoup html "html.parser"))
(setv interesting (cut (.find-all bs "dd") 2 4))
(setv interesting! (list (map (fn [dd-tag] (.findChildren dd-tag)) interesting)))
(setv all-tags [])
(for [tag-list interesting!]
  (for [tag tag-list]
    (.append all-tags tag)))
(setv relpaths (list (map (fn [tag] (get (. tag attrs) "href")) all-tags)))


;; convert a relative path to an absolute path

(setv relpath "../../java/beans/beancontext/BeanContext.html") ; to generalize
(setv abspath java-collection)

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

(+ abspath-cutoff relpath-cutoff)


;; scraping methods from a page

(setv page-url "https://docs.oracle.com/javase/8/docs/api/java/beans/beancontext/BeanContext.html")
(setv html (urlopen page-url))

(setv parsed (BeautifulSoup html))

(setv trs (+ (.find-all (.find parsed "table" {"summary" "Method Summary table, listing methods, and an explanation"})
                        "tr" {"class" "altColor"})
             (.find-all (.find parsed "table" {"summary" "Method Summary table, listing methods, and an explanation"})
                        "tr" {"class" "rowColor"})))

(for [tr trs]
  (setv colFirst-text (. (.find tr "td" {"class" "colFirst"}) code text))
  (print colFirst-text)
  (setv colLast-text (.replace (. (.find tr "td" {"class" "colLast"}) code text) " " " "))
  (print colLast-text))

