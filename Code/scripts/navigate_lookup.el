;; -*- lexical-binding: t -*-

(require 'cl-lib)
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
                 (kill-new output)
                 (previous-buffer)
                 (spacemacs/evil-mc-paste-after)))))))


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


(defun tidy-sig (raw-signature)
  (let* ((signature (->> raw-signature
                         (s-replace-regexp "@[a-zA-Z]+([a-zA-Z0-9=,\" ]+)" "")
                         (s-replace-regexp "@[a-zA-Z]+" "")))
         (split-on-space (s-split " " signature))
         (rtntype (car split-on-space))
         (split-on-open-parens (s-split "(" signature))
         (qualified-methname (cadr (s-split " " (car split-on-open-parens))))
         (unqualified-methname-parts (reverse (-take 2 (reverse (s-split "\\." qualified-methname)))))
         (unqualified-methname (concat (car unqualified-methname-parts)
                                       "." (cadr unqualified-methname-parts)))
         (param-and-types (s-split "," (cadr split-on-open-parens)))
         (params (mapcar (lambda (param-and-type)
                           (car (s-split " " (s-trim-left param-and-type))))
                         param-and-types))
         (param-string (apply #'concat
                              (butlast
                               (-interleave params
                                            (-repeat (length params) ",")))))
         (out (concat rtntype " " unqualified-methname "(" param-string ")")))
    (if (s-contains? "()" out)
        (->> out
             (s-replace "))" ")")
             (s-replace-regexp "<[a-zA-Z0-9]+>" ""))
      (s-replace-regexp "<[a-zA-Z0-9]+>" "" out))))


(defun copy-sig ()
  (interactive)
  (progn (spacemacs/evil-smart-doc-lookup)
         (switch-to-buffer "*lsp-help*")
         (let ((raw-sig (car (s-split "\n" (buffer-string)))))
           (kill-new (tidy-sig raw-sig)))
         (kill-buffer "*lsp-help*")
         (message "Signature copied.")))


(defun copy-sig-full ()
  (interactive)
  (progn (spacemacs/evil-smart-doc-lookup)
         (switch-to-buffer "*lsp-help*")
         (let ((raw-sig (car (s-split "\n" (buffer-string)))))
           (kill-new raw-sig))
         (kill-buffer "*lsp-help*")
         (message "Signature copied.")))


(setq f (let ((x 132))
            (lambda ()
              (insert (concat " (" (int-to-string (incf x)) ", [])")))))

(defun fresh-ap ()
  (interactive)
  (funcall f))


(evil-define-key 'normal 'org-mode-map (kbd "<localleader>ll") 'lookup)
(evil-define-key 'normal 'org-mode-map (kbd "<localleader>lc") 'find-context)
(evil-define-key 'normal 'org-mode-map (kbd "<localleader>lr") 'check-root)
(evil-define-key 'normal 'org-mode-map (kbd "<localleader>lf") 'check-leaf)
(evil-define-key 'normal 'org-mode-map (kbd "<localleader>la") 'fresh-ap)
(evil-define-key 'normal 'java-mode-map (kbd "<localleader>ls") 'copy-sig)
(evil-define-key 'normal 'java-mode-map (kbd "<localleader>lf") 'copy-sig-full)
