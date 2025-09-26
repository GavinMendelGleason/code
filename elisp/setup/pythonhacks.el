;; poetry
(use-package poetry
  ;; :straight t
  ;; :init
  ;; imperfect tracking strategy causes lags in builds
  ;; (setq poetry-tracking-strategy 'switch-buffer)
  :hook
  ;; activate poetry-tracking-mode when python-mode is active
  (python-mode . poetry-tracking-mode)
  )

(use-package blacken :ensure blacken)
(use-package elpy :ensure elpy)

(add-hook 'python-mode-hook
          (lambda ()
            (elpy-enable)
            (blacken-mode)
            (flymake-mode-off)
            (flycheck-mode 1)))

(add-hook 'elpy-mode-hook
          (lambda ()
            (poetry-tracking-mode)))

(provide 'pythonhacks)
