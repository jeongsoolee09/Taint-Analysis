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


(defun parse-html (url)
  "parse the HTML document retrieved by making a request to a given url."
  (set-buffer (url-retrieve-synchronously url))
  (let ((contents (libxml-parse-html-region (point-min) (point-max))))
    (caddr contents)))


(defun find-by-tag (data tag)
  (let ((res))
    (subst nil nil data :test (lambda (a b)
                                (when (and (listp b)
                                           (eql (car b) tag))
                                  (push b res))
                                nil))
    res))


(defun directory-collect (parsed-html)
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
  (labels ((inner (current-html current-url htmls-acc)
                  (let* ((result (directory-collect current-html))
                         (folders (plist-get result :folders))
                         (htmls (plist-get result :htmls)))
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
