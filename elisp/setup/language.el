;;; *******************************************
;;; Languages

;; Web-mode
(require 'web-mode)
(add-to-list 'auto-mode-alist '("\\.phtml\\'" . web-mode))
(add-to-list 'auto-mode-alist '("\\.php\\'" . web-mode))
(add-to-list 'auto-mode-alist '("\\.[agj]sp\\'" . web-mode))
(add-to-list 'auto-mode-alist '("\\.as[cp]x\\'" . web-mode))
(add-to-list 'auto-mode-alist '("\\.erb\\'" . web-mode))
(add-to-list 'auto-mode-alist '("\\.mustache\\'" . web-mode))
(add-to-list 'auto-mode-alist '("\\.djhtml\\'" . web-mode))

(defun my-web-mode-hook ()
  (web-mode-use-tabs))

(add-hook 'web-mode-hook 'my-web-mode-hook)

;; Agda
;;(load-file (let ((coding-system-for-read 'utf-8))
;;             (shell-command-to-string "agda-mode locate")))
;;(require 'agda-mode)

;; RDF
(add-to-list 'auto-mode-alist '("\\.ttl\\'" . ttl-mode))

;; Javascript
(add-to-list 'auto-mode-alist '("\\.js\\'" . js2-mode))
(setq js2-strict-missing-semi-warning nil)
(setq-default js2-basic-offset 2)
(setq js2-mode-hook
      '(lambda () (progn
                    (set-variable 'js2-basic-offset 2)
                    (set-variable 'indent-tabs-mode nil))))

;; Whitespace mode
(require 'whitespace)

(provide 'language)
