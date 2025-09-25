;; Kill the useless menu bar
(menu-bar-mode -1)

;; Long lines handling
(setq-default bidi-paragraph-direction 'left-to-right)
(if (version<= "27.1" emacs-version)
    (setq bidi-inhibit-bpa t))

(if (version<= "27.1" emacs-version)
    (global-so-long-mode 1))

;;; Fucking bell
(setq visible-bell nil)
(setq ring-bell-function 'ignore)

;; Tabs / spaces
(setq-default tab-width 4)
(defvaralias 'c-basic-offset 'tab-width)
(defvaralias 'cperl-indent-level 'tab-width)
(setq-default indent-tabs-mode nil)
(setq-default show-trailing-whitespace t)

;; British English
(setq ispell-dictionary "british")

;; Emacs basics
(tool-bar-mode -1)
(tooltip-mode nil)
(setq tooltip-use-echo-area t)

(setq lsp-keymap-prefix "C-c C-c")

;; Colour theme
;;(load-theme 'suscolors t)
;;(load-theme 'nordic-night t)
(load-theme 'tango-dark t)

;;(load-theme 'github t)
(defun light-contrast-mode ()
  "Light contrast"
  (interactive)
  (load-theme 'github t))

(defun dark-contrast-mode ()
  "Dark contrast"
  (interactive)
  (load-theme 'suscolors t))

;; ;; Fix emacs env variables
;; (defun set-exec-path-from-shell-PATH ()
;;   "Set up Emacs' `exec-path' and PATH environment variable to match
;; that used by the user's shell.

;; This is particularly useful under Mac OS X and macOS, where GUI
;; apps are not started from a shell."
;;   (interactive)
;;   (let ((path-from-shell (replace-regexp-in-string
;;               "[ \t\n]*$" "" (shell-command-to-string
;;                       "$SHELL --login -c 'echo $PATH'"
;;                             ))))
;;     (setenv "PATH" path-from-shell)
;;     (setq exec-path (split-string path-from-shell path-separator))))

;; Requires downloading from https://www.nerdfonts.com/font-downloads
;; copying to ~/.fonts and running `fc-cache -fv`
(set-frame-font "Inconsolata Nerd Font Mono")

;; session
(use-package session :ensure session)
(add-hook 'after-init-hook 'session-initialize)

;;; *****************
;;; window navigation
(windmove-default-keybindings)

;;; *******************************************
;;; Fixes
;; Open in the RIGHT fecking window
(add-to-list
 'display-buffer-alist
 '("^\\*shell\\*$" . (display-buffer-same-window)))

;; Frame buffer name in titlebar
(setq frame-title-format
      (list (format "%s %%S: %%j " (system-name))
        '(buffer-file-name "%f" (dired-directory dired-directory "%b"))))

;;; Editor hooks for 'with-editor' which enables *shell* etc. to use emacs
(add-hook 'shell-mode-hook  'with-editor-export-editor)
(add-hook 'term-exec-hook   'with-editor-export-editor)
(add-hook 'eshell-mode-hook 'with-editor-export-editor)
(add-hook 'shell-mode-hook 'with-editor-export-git-editor)


(use-package direnv
  :ensure direnv
  :config
  (direnv-mode))

(use-package vterm
  :ensure vterm)

(add-hook 'vterm-mode-hook
          (lambda ()
            (setq-local show-trailing-whitespace nil)))

(provide 'tweaks)
