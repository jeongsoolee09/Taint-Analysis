;; 일단 이 두 개만 해 봅시다.
;; 일단 모든 메소드에 대해 스크랩하고, 나중에 필요 없는 것들은 수동으로 걸러내기.

(require 'cl)
(require 's)
(require 'dash)


;; utils ============================================
;; ==================================================

(defmacro comment (&body)
  "dummy macro which implements a rich comment block")


(defun get-only-filename (fullname)
  (let* ((splitted (s-split "/" fullname)))
    (-last-item splitted)))


;; target root urls =================================
;; ==================================================


(defvar *spring-jdbc-url*
  "https://docs.spring.io/spring-framework/docs/current/javadoc-api/org/springframework/jdbc/core/"
  "Spring Jdbc")


(defvar *spring-jms-url*
  "https://docs.spring.io/spring-framework/docs/current/javadoc-api/org/springframework/jms/core/"
  "Spring Jms")


;; Parser ===========================================
;; ==================================================


(defun parse-html (url)
  "parse the HTML document retrieved by making a request to a given url."
  (set-buffer (url-retrieve-synchronously url))
  (let ((contents (libxml-parse-html-region (point-min) (point-max))))
    (caddr contents)))


;; Extractor ========================================
;; ==================================================

(defun find-by-tag (data tag)
  (let ((res))
    (subst nil nil data :test (lambda (a b)
                                (when (and (listp b)
                                           (eql (car b) tag))
                                  (push b res))
                                nil))
    res))


(defun get-attribute-list (parsed-html-fragment)
  (let ((data (cadr parsed-html-fragment)))
    (when (-all? #'dotted-pairp data)
      data)))


(defun find-by-tag-and-attribute (data tag attr)
  "find the tag containing the given (attribute . attribute-value) pair."
  (let ((res))
    (subst nil nil data :test (lambda (a b)
                                (when (and (listp b)
                                           (eql (car b) tag)
                                           (-contains? (get-attribute-list b) attr))
                                  (push b res))
                                nil))
    res))


(defun interface-html-collect (package-frame-url)
  (cl-flet ((extractor (list)
                       (->> list
                            (caddr)
                            (cdaadr))))
    (->> (parse-html package-frame-url)
         ((lambda (parsed)
            (find-by-tag-and-attribute parsed
                                       'ul
                                       '(title . "Interfaces"))))
         (car)
         (remove-if-not #'listp)
         (mapcar #'extractor)
         (remove-if #'null))))


(defun class-html-collect (package-frame-url)
  (cl-flet ((extractor (list)
                       (->> list
                            (caddr)
                            (cdaadr))))
    (->> (parse-html package-frame-url)
         ((lambda (parsed)
            (find-by-tag-and-attribute parsed
                                       'ul
                                       '(title . "Classes"))))
         (car)
         (remove-if-not #'listp)
         (mapcar #'extractor)
         (remove-if #'null))))


;; Traverser ========================================
;; ==================================================


(defun collect-directory (parsed-html)
  (let* ((ahrefs (find-by-tag parsed-html 'a))
         (all (mapcar #'cdaadr ahrefs))
         (folders (remove-if-not (lambda (str)
                                   (s-matches? "[a-z]+/" str))
                                 all))
         (htmls (remove-if-not (lambda (str)
                                 (s-matches? "[a-zA-Z-]+\\.html" str))
                               all)))
    `(:folders ,folders :htmls ,htmls)))


(defun recursive-html-collect (root-url)
  (cl-labels ((inner (current-html current-url htmls-acc)
                     (let* ((result (collect-directory current-html))
                            (folders (plist-get result :folders))
                            (htmls (mapcar (lambda (html-name)
                                             (concat current-url html-name))
                                           (plist-get result :htmls))))
                       (if (null result)
                           (append htmls-acc htmls)
                         (->> htmls-acc
                              (append htmls)
                              (append (reduce #'(lambda (acc folder)
                                                  (let ((new-url (concat current-url folder)))
                                                    (inner (parse-html new-url)
                                                           new-url
                                                           acc)))
                                              folders :initial-value nil)))))))
    (inner (parse-html root-url) root-url nil)))


(defun collect-all-interfaces (all-htmls)
  (cl-flet ((get-full-url-based-on-filename (filename)
                                            (dolist (html all-htmls)
                                              (when (string= (get-only-filename html)
                                                             filename)
                                                (return html)))))
    (let* ((all-package-frame-urls (remove-if-not #'package-frame? all-htmls))
           (all-interface-filenames (flatten-list
                                     (mapcar
                                      #'interface-html-collect
                                      all-package-frame-urls))))
      (mapcar #'get-full-url-based-on-filename all-interface-filenames))))


(defun collect-all-classes (all-htmls)
  (cl-flet ((get-full-url-based-on-filename (filename)
                                            (dolist (html all-htmls)
                                              (when (and (string= (get-only-filename html)
                                                                  filename)
                                                         (not (s-contains? "/class-use/" html)))
                                                (return html)))))
    (let* ((all-package-frame-urls (remove-if-not #'package-frame? all-htmls))
           (all-class-filenames (flatten-list
                                 (mapcar
                                  #'interface-html-collect
                                  all-package-frame-urls))))
      (mapcar #'get-full-url-based-on-filename all-class-filenames))))


;; class html page scraper ==========================
;; ==================================================

(defun find-first-open-parens (lst)
  (dolist (elem lst)
    (when (and (stringp elem)
               (s-contains? "(" elem))
      (return elem))))


(defun find-first-closing-parens (lst)
  (dolist (elem lst)
    (when (and (stringp elem)
               (s-contains? ")" elem))
      (return elem))))


(defun find-with-and-between-parens-strings (lst)
  (let* ((open-parens (find-first-open-parens lst))
         (closing-parens (find-first-closing-parens lst))
         (open-parens-index (-elem-index open-parens lst))
         (closing-parens-index (-elem-index closing-parens lst))
         (sliced (-slice lst
                         open-parens-index
                         (+ closing-parens-index 1))))
    (->> sliced
         (mapcar (lambda (str) (s-replace " " " " str)))
         (mapcar #'s-trim)
         (mapcar (lambda (str) (if (s-contains? ")" str)
                                   (let ((parens-index (s-index-of ")" str)))
                                     (substring str 0 (+ parens-index 1)))
                                 str))))))


(defun anchor-content-organize (anchor-content-list)
  "Organize the anchor's content into a plist."
  (let* ((annots (remove-if-not (lambda (str)
                                  (s-starts-with? "@" str))
                                anchor-content-list))
         (exceptions (remove-if-not (lambda (str)
                                      (s-ends-with? "Exception" str))
                                    anchor-content-list))
         (paramtypes (remove-if-not (lambda (str)
                                      (not (or (-contains? annots str)
                                               (-contains? exceptions str))))
                                    anchor-content-list)))
    `(:annots ,annots :rtntype ,(car paramtypes)
              :paramtypes ,(cdr paramtypes) :exceptions ,exceptions)))


(defun non-anchor-content-organize (non-anchor-content-list)
  (let ((str-with-open-paren (find-first-open-parens non-anchor-content-list)))
    `(:methname ,(s-chop-suffix "(" str-with-open-paren)
                :params ,(->> non-anchor-content-list
                              (cdr)
                              (mapcar (lambda (str)
                                        (s-chop-suffixes '("," ")") str)))))))


(defun collect-method-from-scrape-class-html (class-html-name)
  (cl-flet* ((scrape-anchors (pre-elem)
                            (let ((anchors (find-by-tag pre-elem 'a)))
                              (mapcar (lambda (a) (nth 2 a))
                                      anchors)))
            (scrape-strings (pre-elem)
                            (let ((atoms (remove-if-not #'atom pre-elem)))
                              (find-with-and-between-parens-strings atoms)))
            (assemble-pre (pre-elem classname)
                          (let* ((anchor-contents-plist (->> (reverse (scrape-anchors pre-elem))
                                                             (anchor-content-organize)))
                                 (non-anchor-contents-plist (->> (scrape-strings pre-elem)
                                                                 (non-anchor-content-organize))))
                            `(:annots ,(plist-get anchor-contents-plist :annots)
                                      :rtntype ,(plist-get non-anchor-contents-plist :rtntype)
                                      :classname ,classname
                                      :methname ,(plist-get non-anchor-contents-plist :methname)
                                      :params-and-types ,(-zip (plist-get anchor-contents-plist :paramtypes)
                                                                (plist-get non-anchor-contents-plist :params))
                                      :exceptions ,(plist-get anchor-contents-plist :exceptions)))))
    (let* ((parsed (parse-html class-html-name))
           (pres (find-by-tag parsed 'pre))
           (classname (car (s-split "\\." (get-only-filename class-html-name)))))
      (mapcar (lambda (pre) (assemble-pre pre classname)) (cdr (reverse pres))))))


(comment
 (progn
   (collect-method-from-scrape-class-html sample-class-html)
   ))


;; 가설: 우리가 원하는 것은 인터페이스가 *아니라* 클래스이다.

;; Some predicates on html names. ===================
;; ==================================================


(defun interesting-html? (fullname)
  (let* ((filename (get-only-filename fullname))
         (first-char (substring filename 0 1)))
    (and (s-uppercase? first-char)
         (not (or (s-contains? "/class-use/" fullname)
                  (s-contains? "/support/" fullname))))))


(defun package-use? (fullname)
  (s-equals? (get-only-filename fullname) "package-use.html"))


(defun package-tree? (fullname)
  (s-equals? (get-only-filename fullname) "package-tree.html"))


(defun package-summary? (fullname)
  (s-equals? (get-only-filename fullname) "package-summary.html"))


(defun package-frame? (fullname)
  (s-equals? (get-only-filename fullname) "package-frame.html"))


;; main function ====================================
;; ==================================================

(comment
 (progn
   (parse-html "https://docs.spring.io/spring-framework/docs/current/javadoc-api/org/springframework/jdbc/core/namedparam/class-use/NamedParameterJdbcOperations.html")

   (setq all-htmls (recursive-html-collect *spring-jdbc-url*))
   (setq interface-htmls (collect-all-interfaces all-htmls))
   (setq class-htmls (collect-all-classes all-htmls))

   ))


(defun scrape-main ()
  (let* ((all-htmls (recursive-html-collect *spring-jms-url*))
         (interface-htmls (collect-all-interfaces
                           all-htmls))
         (class-htmls (collect-all-classes
                       all-htmls)))
    (append (mapcar
             #'collect-method-from-scrape-class-html
             class-htmls))
    ))
