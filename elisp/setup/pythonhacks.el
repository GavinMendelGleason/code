;; poetry
;; (use-package poetry
;;   ;; :straight t
;;   ;; :init
;;   ;; imperfect tracking strategy causes lags in builds
;;   ;; (setq poetry-tracking-strategy 'switch-buffer)
;;   :hook
;;   ;; activate poetry-tracking-mode when python-mode is active
;;   (python-mode . poetry-tracking-mode)
;;   )

(use-package blacken
  :ensure t
  :hook (python-mode . blacken-mode)
  :custom
  (blacken-line-length 88))

(use-package elpy :ensure elpy)

(add-hook 'python-mode-hook
          (lambda ()
            (elpy-enable)
            (blacken-mode)
            (flymake-mode-off)
            (flycheck-mode 1)))

(add-hook 'before-save-hook
          (lambda ()
            (when (eq major-mode 'python-mode)
              (blacken-buffer))))
 
(provide 'pythonhacks)
