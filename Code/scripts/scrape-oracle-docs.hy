(import [urllib.request [urlopen]])
(import [bs4 [BeautifulSoup]])
(import re)


(defn scrape-interesting-relpaths []
  "scrape all interesting relpaths from documentation of the java collection system."
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
  relpaths)


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
  (setv relpath-cutoff (->> (.split relpath "/")
                            (filter (fn [string] (!= string "..")))
                            (map (fn [string] (if (in ".html" string)
                                                  string
                                                  (+ string "/"))))
                            (list)
                            (reduce +)))
  (+ abspath-cutoff relpath-cutoff))


(setv sample-url "https://docs.oracle.com/javase/8/docs/api/java/beans/beancontext/BeanContext.html")
        

(defn handle-paramlist [paramlist-str]
  (if (in "," paramlist-str)
      (raise TODO)
      (raise TODO)))


(defn scrape-method-off-page [page-url]
  "scraping methods off a page"
  (setv html (urlopen page-url))
  (setv parsed (BeautifulSoup html))
  (setv trs (+ (.find-all (.find parsed "table" {"summary" "Method Summary table, listing methods, and an explanation"})
                          "tr" {"class" "altColor"})
               (.find-all (.find parsed "table" {"summary" "Method Summary table, listing methods, and an explanation"})
                          "tr" {"class" "rowColor"})))
  (setv signature-acc [])
  (for [tr trs]
    (setv colFirst-text (->> (.find tr "td" {"class" "colFirst"})
                             ((fn [tag] (. tag code text)))))
    (setv colLast-text (->> (.find tr "td" {"class" "colLast"})
                            ((fn [tag] (. tag code text)))
                            ((fn [s] (.replace s " " " ")))
                            ((fn [s] (.replace s "\n" " ")))))
    (.append signature-acc (+ colFirst-text " " (.replace colLast-text " " ""))))
  ;; TODO: handle each paramlist-str appropriately.
  signature-acc)
