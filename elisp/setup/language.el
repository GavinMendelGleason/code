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

;; Whitespace mode
(require 'whitespace)

;; Markdown
(require 'markdown-mode)
(setq markdown-fontify-code-blocks-natively t)
(add-to-list 'markdown-code-lang-modes '("graphql" . graphql-mod))

(provide 'language)
