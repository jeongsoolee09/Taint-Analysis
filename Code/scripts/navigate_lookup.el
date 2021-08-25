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


(defun has-multiple-lines? ()
  (let ((buffer-content (buffer-string)))
    (> (length (s-split "\n" buffer-content)) 2)))


(defun lookup ()
  (interactive)
  (let* ((region-string (return-region-as-string))
         (out-buffer (shell-command (concat "hy " *navigate-script-location*
                                            " --lookup=" region-string)
                                    "lookup-output")))
    (progn (switch-to-buffer "lookup-output")
           (let ((output (buffer-string)))
             (when (not (has-multiple-lines?))
                 (progn
                   (previous-buffer)
                   (insert (concat " " output))))))))


(defun find-context ()
  (interactive)
  (let* ((region-string (return-region-as-string))
         (out-buffer (shell-command (concat "hy " *navigate-script-location*
                                            " --find-context=\"" region-string "\"")
                                    "find-context-output")))
    (switch-to-buffer "find-context-output")))


(defun check-root ()
  (interactive)
  (let* ((region-string (return-region-as-string))
         (out-buffer (shell-command (concat "hy " *navigate-script-location*
                                            " --check-root=\"" region-string "\"")
                                    "check-root-output")))
    (switch-to-buffer "check-root-output")))


(defun check-leaf ()
  (interactive)
  (let* ((region-string (return-region-as-string))
         (out-buffer (shell-command (concat "hy " *navigate-script-location*
                                            " --check-leaf=\"" region-string "\"")
                                    "check-leaf-output")))
    (switch-to-buffer "check-leaf-output")))


(spacemacs/set-leader-keys-for-major-mode 'org-mode "ll" 'lookup)
(spacemacs/set-leader-keys-for-major-mode 'org-mode "lc" 'find-context)
(spacemacs/set-leader-keys-for-major-mode 'org-mode "lr" 'check-root)
(spacemacs/set-leader-keys-for-major-mode 'org-mode "lf" 'check-leaf)
