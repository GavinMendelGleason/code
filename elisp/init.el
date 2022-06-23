;;; Gavin's .emacs

;;; *******************************************
;;; MELPA
(require 'package) ;; You might already have this line
(setq package-archives '(("gnu" . "http://elpa.gnu.org/packages/")
                         ("melpa" . "http://melpa.org/packages/")))
(package-initialize) ;; You might already have this line

;; Kill the useless menu bar
(menu-bar-mode -1)

;; do something smart if lines are super long
(global-so-long-mode 1)

;;; Fucking bell
(setq visible-bell nil)
(setq ring-bell-function 'ignore)

;; Set Path manually (v8.2.4)
(setenv "PATH" "/home/gavin/.cabal/bin:/home/gavin/.swivm/versions/v8.5.8/bin:/home/gavin/tmp/google-cloud-sdk/bin:/home/gavin/bin:/home/gavin/.local/bin:/home/gavin/go/bin:/home/gavin/.cargo/bin:/home/gavin/.local/bin:/home/gavin/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/usr/games:/usr/local/games:/snap/bin")

(defun set-exec-path-from-shell-PATH ()
  "Set up Emacs' `exec-path' and PATH environment variable to match
that used by the user's shell.

This is particularly useful under Mac OS X and macOS, where GUI
apps are not started from a shell."
  (interactive)
  (let ((path-from-shell (replace-regexp-in-string
              "[ \t\n]*$" "" (shell-command-to-string
                      "$SHELL --login -c 'echo $PATH'"
                            ))))
    (setenv "PATH" path-from-shell)
    (setq exec-path (split-string path-from-shell path-separator))))

(set-exec-path-from-shell-PATH)

;; session
(require 'session)
(add-hook 'after-init-hook 'session-initialize)

;;; GitHub Pull Requests
;;(require 'magit-gh-pulls)
;;(add-hook 'magit-mode-hook 'turn-on-magit-gh-pulls)


;;; ******
;;; Lean
;;;(setq lean-rootdir "/home/gavin/lib/lean-4.0.0-m2-linux/")
;;(global-set-key (kbd "S-SPC") #'company-complete)

;;; *******************************************
;;; Emacs as window manager? Surely you're joking?!
;;(require 'exwm)
;;(require 'exwm-config)
;;(exwm-config-example)

;;; *****************
;;; window navigation
(windmove-default-keybindings)

;;; *******************************************
;;; Fixes
;; Open in the RIGHT fecking window
(add-to-list
 'display-buffer-alist
 '("^\\*shell\\*$" . (display-buffer-same-window)))

;; Git password control
(require 'shell)
(setq comint-password-prompt-regexp
      (concat comint-password-prompt-regexp
              "\\|^Password for .*:\\s *\\'"))

;; Tabs / spaces
(setq-default tab-width 4)
(defvaralias 'c-basic-offset 'tab-width)
(defvaralias 'cperl-indent-level 'tab-width)
(setq-default indent-tabs-mode nil)
(setq-default show-trailing-whitespace t)

;; Emacs basics
(tool-bar-mode -1)
(tooltip-mode nil)
(setq tooltip-use-echo-area t)

;; Colour theme
(load-theme 'suscolors t)
;;(load-theme 'github t)
(defun light-contrast-mode ()
  "Light contrast"
  (interactive)
  (load-theme 'github t))

(defun dark-contrast-mode ()
  "Dark contrast"
  (interactive)
  (load-theme 'suscolors t))

;; Tramp Colour
;;(setq tramp-default-method "ssh")
;;(setq tramp-theme-face-remapping-alist '(background . "Purple"))
;; (require 'tramp-theme)
;; (setq tramp-theme-face-remapping-alist
;; 			'((nil "^root$" (fringe (:inherit fringe :inverse-video t)))
;; 				("^spartacus$" nil (default (:background "DarkPurple")))
;; 				("^gaius$" nil (default (:background "DarkGreen")))))

;; unicode-fonts
(require 'unicode-fonts)
;;(unicode-fonts-setup)

;; Frame buffer name in titlebar
(setq frame-title-format
      (list (format "%s %%S: %%j " (system-name))
        '(buffer-file-name "%f" (dired-directory dired-directory "%b"))))

;;; Editor hooks for 'with-editor' which enables *shell* etc. to use emacs
(add-hook 'shell-mode-hook  'with-editor-export-editor)
(add-hook 'term-exec-hook   'with-editor-export-editor)
(add-hook 'eshell-mode-hook 'with-editor-export-editor)
(add-hook 'shell-mode-hook 'with-editor-export-git-editor)

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
(load-file (let ((coding-system-for-read 'utf-8))
             (shell-command-to-string "agda-mode locate")))
;;(require 'agda-mode)

;; RDF (n3 mode)
;;(require 'n3-mode)
(add-to-list 'auto-mode-alist '("\\.ttl\\'" . ttl-mode))

;; Abella
;;(load-file "/home/francoisbabeuf/.emacs.d/lib/abella/lprolog.el")

;; Twelf
;;(setq twelf-root "/home/francoisbabeuf/Documents/build/twelf/")
;;(load (concat twelf-root "emacs/twelf-init.el"))

;; Event ML
;;(load-file "/home/francoisbabeuf/.emacs.d/lib/eml/eventml-mode.el")

;; JonPRL
;;(load-file "/home/francoisbabeuf/.emacs.d/lib/jonprl-mode/jonprl-compat.el")
;;(load-file "/home/francoisbabeuf/.emacs.d/lib/jonprl-mode/jonprl-mode.el")

;; OCaML
;;(add-to-list 'auto-mode-alist '("\\.ml\\'" . tuareg-mode))

;;;; OPAM  for OCaM
;; (let ((opam-share (ignore-errors (car (process-lines "opam" "config" "var" "share")))))
;;   (when (and opam-share (file-directory-p opam-share))
;;        ;; Register Merlin
;; 	(add-to-list 'load-path (expand-file-name "emacs/site-lisp" opam-share))
;; 	(autoload 'merlin-mode "merlin" nil t nil)
;; 	;; Automatically start it in OCaml buffers
;; 	(add-hook 'tuareg-mode-hook 'merlin-mode t)
;; 	(add-hook 'caml-mode-hook 'merlin-mode t)
;; 	;; custom key bindings
;; 	(add-hook 'merlin-mode-hook
;;        (lambda ()
;; 		 (local-set-key (quote [?\C-x?\C-d]) (quote merlin-destruct))))
;; 	;; Use opam switch to lookup ocamlmerlin binary
;; 	(setq merlin-command 'opam)))

;; Flymake (prep for other things which use flymake)
;;(flymake-mode-on)
;;(defadvice flymake-post-syntax-check (before flymake-force-check-was-interrupted)
;;  (setq flymake-check-was-interrupted t))
;;(ad-activate 'flymake-post-syntax-check)

;; Fstar
;;(setq fstar-executable "/home/francoisbabeuf/.opam/system/bin/fstar.exe")
;; (setq fstar-executable "/home/francoisbabeuf/Documents/build/FStar/bin/fstar.exe")

;; RedPRL
;;(load-file "/home/francoisbabeuf/.emacs.d/lib/redprl/redprl-mode.el")
;;(load-file "/home/francoisbabeuf/.emacs.d/lib/redprl/ob-redprl.el")
;;(load-file "/home/francoisbabeuf/.emacs.d/lib/redprl/redprl.el")
;;(setq redprl-command "/home/francoisbabeuf/Documents/build/sml-redprl/bin/redprl")

;; Agda
;;(load-file (let ((coding-system-for-read 'utf-8))
;;                (shell-command-to-string "agda-mode locate")))

;;'(agda2-include-dirs
;;   (quote
;;	("." "/usr/share/agda-stdlib" "/home/francoisbabeuf/Documents/code/agda/agda-stdlib/" "/home/francoisbabeuf/Documents/code/agda/finset/")))

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

;; Magit
(require 'magit)
(global-set-key (kbd "C-x g") 'magit-status)

;; Rust
(require 'rust-mode)

;; load csp-mode setup code
;;(add-to-list 'load-path "/home/francoisbabeuf/share/emacs/site-lisp/csp-mode")
;;(load "csp-mode-startup")

;;; Prolog mode
;; (require 'lsp-mode)
;; (lsp-register-client
;;   (make-lsp-client
;;    :new-connection
;;    (lsp-stdio-connection (list "swipl"
;;                                "-g" "use_module(library(lsp_server))."
;;                                "-g" "lsp_server:main"
;;                                "-t" "halt"
;;                                "--" "stdio"))
;;    :major-modes '(prolog-mode)
;;    :priority 1
;;    :multi-root t
;;    :server-id 'prolog-ls))
;; (setq lsp-enable-snippet t)

;; (require 'lsp-mode)
;; (lsp-register-client
;;  (make-lsp-client
;;   :new-connection
;;   (lsp-stdio-connection (list "swipl"
;;                               "-g" "lsp_server:main"
;;                               "-t" "halt"
;;                               "/home/francoisbabeuf/Documents/build/lsp_server/prolog/lsp_server.pl"
;;                               "--" "stdio"))
;;   :major-modes '(prolog-mode)
;;   :priority 1
;;   :multi-root t
;;   :server-id 'prolog-ls))

(load-file "/home/gavin/.emacs.d/lib/prolog.el")
(setq prolog-electric-if-then-else-flag t)

;; ;; (setq prolog-electric-dot-flag t)
;; (setq prolog-system 'swi)
;; ;;(autoload 'prolog-mode "prolog" "Major mode for editing Prolog programs." t)
;; ;;(setq prolog-system 'mercury)

(setq auto-mode-alist (cons (cons "\\.pl" 'prolog-mode) auto-mode-alist))

(add-hook 'prolog-mode-hook
          (lambda ()
            (setq indent-tabs-mode nil)))

;;(setq prolog-program-name "swipl") ;;
;;(setq prolog-program-name "/home/francoisbabeuf/Documents/build/ClioPatria/run.pl")
(setq prolog-program-name "swipl")
(setenv "TERMINUSDB_FILE_STORAGE_PATH" "/home/gavin/dev/terminusdb/storage/")
;; (setenv "TERMINUSDB_HTTPS_ENABLED" "true")
;;(setenv "TERMINUSDB_HTTPS_ENABLED" "false")
(setenv "TERMINUSDB_SERVER_PORT" "6363")
;;(setenv "TERMINUSDB_SERVER_DB_PATH" "/home/gavin/dev/terminus_electron")
;;(setenv "TERMINUSDB_CONSOLE_BASE_URL" "https://dl.bintray.com/terminusdb/terminusdb/0.0.1")
;;(setenv "TERMINUSDB_CONSOLE_BASE_URL" "https://dl.bintray.com/terminusdb/terminusdb/0.0.1")
(setenv "TERMINUSDB_CONSOLE_BASE_URL" "https://dl.bintray.com/terminusdb/terminusdb/canary")
;;(setenv "TERMINUSDB_CONSOLE_BASE_URL" "https://dcm.ist/console/v4.0.0")
(setenv "TERMINUSDB_IGNORE_REF_AND_REPO_SCHEMA" "true")
;;(setq prolog-program-name "/home/gavin/dev/terminus-server/start.pl")
(setenv "TERMINUSDB_SERVER_DB_PATH" "/home/gavin/dev/terminusdb/storage/db")
(setenv "RUST_BACKTRACE" "1")

;; (setenv "AUTH0_DOMAIN" "terminushub.eu.auth0.com")
;; (setenv "AUTH0_CLIENT_ID" "MJJndGp0zUdM7o3POTQPmRJImY2ho0ai")
;; (setenv "AUDIENCE" "https://terminushub/registerUser")
;; (setenv "TERMINUS_BFF_URL" "https://hub-dev.dcm.ist/")
;; (setenv "TERMINUS_HUB_URL" "https://hub-dev-server.dcm.ist/")

(setenv "TERMINUS_BFF_URL" "https://terminusdb.com/")
(setenv "TERMINUS_HUB_URL" "https://hub.terminusdb.com/")
(setenv "AUTH0_DOMAIN" "terminusdb.eu.auth0.com")
(setenv "AUTH0_CLIENT_ID" "4EYIHQaVLgwi5V5m2gRNYdtpZZfbwtDz")
(setenv "AUDIENCE" "https://terminusdb.com/hubservices")

(setq prolog-system 'swi)
(setq prolog-program-name "swipl")
;;(setq prolog-program-name "/home/gavin/dev/terminusdb/start.pl")
;;(setq prolog-program-name "/home/gavin/dev/terminusdb/src/start.pl")
;;(setq prolog-program-switches '((t ("serve" "-i"))))
(setq prolog-program-switches '((t ())))

;;(setq prolog-program-name "swipl")
;; Automatic Etags for prolog
(setq tags-table-list
	  '("/home/gavin/dev/terminusdb"))

;; Run this the first time you use tags
;; (create-prolog-tags "/home/gavin/dev/terminus-server")
;;
(defun create-prolog-tags (dir-name)
  "Create prolog tags file."
  (interactive "DDirectory: ")
  (eshell-command
   (format "cd %s; find %s -type f -name \"*.pl\" | etags -l prolog -"
		   dir-name dir-name)))

(defadvice xref--find-definitions (around refresh-etags activate)
  "Rerun etags and reload tags if tag not found and redo find-tag.
    If buffer is modified, ask about save before running etags."
  (let ((extension (file-name-extension (buffer-file-name))))
	(condition-case err
 		ad-do-it
	  (error (and (buffer-modified-p)
				  (not (ding))
				  (y-or-n-p "Buffer is modified, save it? ")
				  (save-buffer))
			 (er-refresh-etags extension)
			 ad-do-it))))

(defun er-refresh-etags (&optional extension)
  "Run etags on all peer files in current dir and reload them silently."
  (let ((my-tags-file (locate-dominating-file default-directory "TAGS")))
	(when my-tags-file
	  (message "Loading tags file: %s" my-tags-file)
	  (let ((tags-dir (file-name-directory my-tags-file)))
		(create-prolog-tags tags-dir)
  		(visit-tags-table my-tags-file)))))

;; (lsp-register-client
;;   (make-lsp-client
;;    :new-connection
;;    (lsp-stdio-connection (list "swipl"
;;                                "-g" "use_module(library(lsp_server))."
;;                                "-g" "lsp_server:main"
;;                                "-t" "halt"
;;                                "--" "stdio"))
;;    :major-modes '(prolog-mode)
;;    :priority 1
;;    :multi-root t
;;    :server-id 'prolog-ls))

;;; Ciao mode
;;(setq load-path (cons "/usr/local/lib/ciao" load-path))
;; Java mode in ciao
;;(setq load-path (cons "/usr/lib/ciao" load-path))

;; (defun load-java-ciaopp-mode ()
;;   (require 'java-ciaopp)
;;   (java-ciaopp-setup))

;; (add-hook 'java-mode-hook 'load-java-ciaopp-mode)
;; (load-file "/usr/local/lib/ciao/ciao-site-file.el")
;; (if (file-exists-p "/usr/local/lib/ciao/ciao-site-file.el")
;; 	(load-file "/usr/local/lib/ciao/ciao-site-file.el")
;;   )

;; Mercury
;;(add-to-list 'load-path
;;			 "/usr/local/mercury-rotd-2017-06-22/lib/mercury/elisp")
;;(autoload 'mercury-mode "prolog" "Major mode for editing Mercury programs." t)

;;(autoload 'mdb "gud" "Invoke the Mercury debugger" t)

;;(defvar *flymake-mercury-checker* "/home/francoisbabeuf/bin/mercury-checker.sh")

;;(defun flymake-mercury-init ()
;;  (let* ((temp-file (flymake-init-create-temp-buffer-copy
;;                     'flymake-create-temp-inplace))
;;         (local-file (file-relative-name
;;                      temp-file
;;                      (file-name-directory buffer-file-name))))
;;    (list *flymake-mercury-checker* (list local-file))))

;; (eval-after-load 'flycheck
;;   '(progn
;; 	 (require 'flycheck-mercury)
;; 	 (push '("\\([^:]*\\):\\([0-9]+\\):[0-9]+: \\(.*\\)" 1 2 nil 3) flymake-err-line-patterns)
;; 	 (add-to-list 'flymake-allowed-file-name-masks '("\\.m\\'" flymake-mercury-init nil flymake-get-real-file-name))))

;; (add-hook 'mercury-mode-hook
;;           '(lambda ()
;; 			 (if (not (null buffer-file-name)) (flymake-mode))))

;; (add-to-list 'auto-mode-alist '("\\.m\\'" . mercury-mode))
;; (eval-after-load 'flycheck
;;   '(require 'flycheck-mercury))

;;; ************************************************
;;; Customisations

(custom-set-variables
 ;; custom-set-variables was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(agda2-include-dirs '("." "/home/gavin/lib/agda-stdlib/src"))
 '(agda2-program-args
   '("--include-path=/home/gavin/lib/agda-stdlib/src/" "--include-path=."))
 '(agda2-program-name "/home/gavin/.cabal/bin/agda")
 '(custom-safe-themes
   '("4e7e04c4b161dd04dc671fb5288e3cc772d9086345cb03b7f5ed8538905e8e27" "23562d67c3657a80dd1afc21e1e80652db0ff819e477649d23a38c1502d1245f" default))
 '(package-selected-packages
   '(restclient js2-mode session wc-mode exec-path-from-shell ttl-mode yaml-mode tide helm-lean company-lean ## lean-mode rustic flycheck magit-delta so-long tramp exwm xelb csv-mode rust-mode with-editor markdown-preview-eww spinner lsp-mode auto-sudoedit tramp-theme tramp-term flycheck-mercury yasnippet web-mode utop unicode-fonts tuareg suscolors-theme sparql-mode sml-mode redprl ocp-indent n3-mode merlin markdown-mode magit idris-mode ghc fstar-mode))
 '(prolog-compile-string
   '((eclipse "[%f].")
     (mercury "mmc ")
     (sicstus
      (eval
       (if
           (prolog-atleast-version
            '(3 . 7))
           "prolog:zap_file(%m,%b,compile,%l)." "prolog:zap_file(%m,%b,compile).")))
     (swi "[%f].")
     (t "compile(%f).")))
 '(safe-local-variable-values
   '((eval progn
           (let
               ((m31-root-directory
                 (when buffer-file-name
                   (locate-dominating-file buffer-file-name ".dir-locals.el")))
                (m31-project-find-file
                 (and
                  (boundp 'm31-project-find-file)
                  m31-project-find-file)))
             (when m31-root-directory
               (setq tags-file-name
                     (concat m31-root-directory "TAGS"))
               (add-to-list 'compilation-search-path m31-root-directory)
               (if
                   (not m31-project-find-file)
                   (setq compile-command
                         (concat "make -C " m31-root-directory))))
             (setq m31-executable
                   (concat m31-root-directory "andromeda.native"))))))
 '(send-mail-function 'mailclient-send-it)
 '(session-use-package t nil (session))
 '(ttl-indent-level 2))
(custom-set-faces
 ;; custom-set-faces was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(default ((t (:family "Ubuntu Mono" :foundry "DAMA" :slant normal :weight normal :height 125 :width normal))))
 '(agda2-highlight-datatype-face ((t (:foreground "sky blue"))))
 '(agda2-highlight-function-face ((t (:foreground "deep sky blue"))))
 '(agda2-highlight-postulate-face ((t (:foreground "tomato"))))
 '(agda2-highlight-primitive-face ((t (:foreground "brown"))))
 '(agda2-highlight-primitive-type-face ((t (:foreground "brown"))))
 '(agda2-highlight-record-face ((t (:foreground "magenta")))))
;; ## added by OPAM user-setup for emacs / base ## 56ab50dc8996d2bb95e7856a6eddb17b ## you can edit, but keep this line
;;(require 'opam-user-setup "~/.emacs.d/opam-user-setup.el")
;; ## end of OPAM user-setup addition for emacs / base ## keep this line
(put 'downcase-region 'disabled nil)

; @begin(93695291)@ - Do not edit these lines - added automatically!
;(if (file-exists-p "/home/gavin/dev/ciao/ciao_emacs/elisp/ciao-site-file.el")
;  (load-file "/home/gavin/dev/ciao/ciao_emacs/elisp/ciao-site-file.el"))
; @end(93695291)@ - End of automatically added lines.
