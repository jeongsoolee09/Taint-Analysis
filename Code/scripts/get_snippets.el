;; 일단 이 두 개만 해 봅시다.
;; 일단 모든 메소드에 대해 스크랩하고, 나중에 필요 없는 것들은 수동으로 걸러내기.

(require 'cl)
(require 's)

(defvar *spring-jdbc*
  "https://docs.spring.io/spring-framework/docs/current/javadoc-api/org/springframework/jdbc/core/"
  "Spring Jdbc")


(defvar *spring-jms*
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



(defun recursive-html-collect (url)
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
    (inner (parse-html url) url nil)))






;; 이제 html을 recursive하게 모았으니, 각각의 html 문서들을 파싱할 차례이다.
;; 그 전에, package-frame.html을 파싱해 html 파일이 인터페이스이고 클래스인지를 찾아내자.
;; 가설: 우리가 원하는 것은 인터페이스가 *아니라* 클래스이다.

;; Some predicates on html names. ===================
;; ==================================================


(defun get-only-filename (fullname)
  (let* ((splitted (s-split "/" fullname)))
    (car (last splitted))))


(defun interesting-html? (fullname)
  (let* ((filename (get-only-filename fullname))
         (first-char (substring filename 0 1)))
    (and (s-uppercase? first-char)
         (not (or (s-contains? "/class-use/" fullname)
                  (s-contains? "/support/" fullname))))))


(defun package-use? (html-filename)
  (s-equals? html-filename "package-use.html"))


(defun package-tree? (html-filename)
  (s-equals? html-filename "package-tree.html"))


(defun package-summary? (html-filename)
  (s-equals? html-filename "package-summary.html"))


(defun package-frame? (html-filename)
  (s-equals? html-filename "package-frame.html"))



(defun main ()

  )
