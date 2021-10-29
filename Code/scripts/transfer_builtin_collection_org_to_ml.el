(require 's)

(defun readlines (path)
  (with-temp-buffer
    (insert-file-contents path)
    (split-string (buffer-string) "\n" t)))


(defun remove-unmarked (strlist)
  (remove-if (lambda (str) (or (s-contains? "- [ ] " str)
                               (s-contains? "* Java Builtin" str)))
             strlist))


(defun group-by-subheadings (strlist)
  (cl-labels ((inner (strlist smol-acc large-acc)
                     (if (null strlist)
                         (remove-if #'null (cons (reverse smol-acc) large-acc))
                         (if (s-contains? "** " (car strlist))
                             (inner (cdr strlist) (cons (car strlist) ()) (cons (reverse smol-acc) large-acc))
                             (inner (cdr strlist) (cons (car strlist) smol-acc) large-acc)))))
    (inner strlist () ())))


;; so sad that elisp doesn't have TCO...
(setq max-lisp-eval-depth 1000000000)
(setq max-specpdl-size 10000000000)


(defun extract-methname (signature)
  (when (string-match "[a-zA-Z ]*[a-zA-Z<> ]*[a-zA-Z]+\.\\([a-zA-Z]+\\)(.*)" signature)
    (match-string 1 signature)))


(defun group->ml (strgroup)
  (assert (s-contains? "** " (car strgroup)))
  (let* ((classname (s-chop-prefix "** " (car strgroup)))
         (ml-body (let* ((ingredients (cdr strgroup)))
                                    (mapcar (lambda (str)
                                              (->> (s-chop-prefix "   - [X] " str)
                                                   (extract-methname))) ingredients))))
    (apply #'concat (mapcar (lambda (methodname) (concat "; (\"" classname "\", \"" methodname "\")\n")) ml-body))))


(defun wrap-ml (ml-list)
  (concat "let treat_as_void_calls = [\n" ml-list "]\n"))


(defun output-to-file (str)
  (find-file "defLocAliasModels.ml")
  (insert str))


(defun main ()
  (->> (readlines "./builtin-collection.org")
       (remove-unmarked)
       (group-by-subheadings)
       (mapcar #'group->ml)
       (apply #'concat)
       (wrap-ml)
       (output-to-file)))
