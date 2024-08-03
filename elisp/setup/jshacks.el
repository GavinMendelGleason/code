;; Javascript mode setup

(use-package js2-mode
  :config
  (add-hook 'js2-mode-hook 'js/js-mode-hook))

(defun js/js-mode-hook ()
  (lsp)
  (set-variable 'js2-basic-offset 2)
  (set-variable 'indent-tabs-mode nil))

(add-to-list 'auto-mode-alist '("\\.js\\'" . js2-mode))
(setq js2-strict-missing-semi-warning nil)
(setq js2-basic-offset 2)

(provide 'jshacks)
