(defun find-all-txts-starting-with-number (directory)
  (interactive "fFilename: ")
  (directory-files-recursively directory "[0-9]+.*\.txt"))


(defun bicycle-chain (lst)
  (-zip (butlast lst) (cdr lst)))


(defun ediff-all ()
  (let ((txt-file-bicycle-chain (->> (find-all-txts-starting-with-number "~/Dropbox/Taint-Analysis/Code/benchmarks/realworld/relational-data-access")
                                     ((lambda (x) (sort x #'string<)))
                                     (bicycle-chain))))
    (dolist (cell txt-file-bicycle-chain)
      (eyebrowse-create-window-config)
      (ediff (car cell) (cdr cell)))))


(defun ediff-all-cleanup ()
  (progn
    (dolist (txt (find-all-txts-starting-with-number "~/Dropbox/Taint-Analysis/Code/benchmarks/realworld/relational-data-access"))
      (kill-buffer (directory-file-name (car (last (s-split "/" txt))))))
    (ibuffer)
    (ibuffer-mark-by-name-regexp "[e|E]diff")
    (ibuffer-do-delete)
    (kill-buffer "*Ibuffer*")))
