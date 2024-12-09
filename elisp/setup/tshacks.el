(use-package typescript-mode
  :ensure typescript-mode
  :config
  (add-hook 'typescript-mode-hook 'ts/ts-mode-hook))

(use-package prettier-rc :ensure prettier-rc)

(set-variable 'typescript-indent-level 2)

(defun ts/ts-mode-hook ()
  ;; start the appropriate language server (eslint and ts-ls)
  (lsp)
  ;; format our code using prettier on each save
  (prettier-rc-mode)
  ;;(add-hook 'before-save-hook 'lsp-format-buffer nil t)
)

;; Emacs tries to be clever and uses the shebang in a file to force it to be javascript.
;; This affects CLI startup scripts even if they are written in typescript.
;; This snippet gets rid of that association between a node shebang
;; and js, making it fall back to knowing by extension.
(setq interpreter-mode-alist (assoc-delete-all "node" interpreter-mode-alist))
(add-to-list 'magic-mode-alist
             '((lambda ()
                 (string-match "\\.ts$" (buffer-file-name))) . typescript-mode))

(provide 'tshacks)
