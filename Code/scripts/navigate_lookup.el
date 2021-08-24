(require 'cl)
(require 's)


(setq *navigate-script-location*
      "/Users/jslee/Dropbox/Taint-Analysis/Code/benchmarks/realworld/sagan/navigate_callgraph.hy")


(defun get-this-thing-at-point ()
  "return the thing at the point as a string."
  (thing-at-point 'symbol))


(defun return-region-as-string ()
  "return the region's content as a string."
  (when (and (region-active-p) (not (region-noncontiguous-p)))
    (buffer-substring (region-beginning) (region-end))))


(defun lookup ()
  (let* ((thing-at-point (get-this-thing-at-point))
         (out-buffer (shell-command (concat "hy " *navigate-script-location*
                                            " --lookup=" thing-at-point)
                                    "lookup-output")))
    (progn (switch-to-buffer "lookup-output")
           (let ((output (buffer-string)))
             (previous-buffer)
             (insert (concat " " output))))))


(defun find-context ()
  (let* ((region-string (return-region-as-string))
         (out-buffer (shell-command (concat "hy " *navigate-script-location*
                                            " --find-context=\"" region-string "\"")
                                    "find-context-output")))
    (switch-to-buffer "find-context-output")))


(defun check-root ()
  (let* ((region-string (return-region-as-string))
         (out-buffer (shell-command (concat "hy " *navigate-script-location*
                                            " --check-root=\"" region-string "\"")
                                    "check-root-output")))
    (switch-to-buffer "check-root-output")))


(defun check-leaf ()
  (let* ((region-string (return-region-as-string))
         (out-buffer (shell-command (concat "hy " *navigate-script-location*
                                            " --check-leaf=\"" region-string "\"")
                                    "check-leaf-output")))
    (switch-to-buffer "check-leaf-output")))
