;;; Gavin's .emacs

;;; *******************************************
;;; MELPA
(require 'package) ;; You might already have this line
(add-to-list 'package-archives
             '("melpa" . "https://melpa.org/packages/"))
(package-initialize) ;; You might already have this line

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

;; Tabs
(setq-default tab-width 4)
(defvaralias 'c-basic-offset 'tab-width)
(defvaralias 'cperl-indent-level 'tab-width)
(setq indent-tabs-mode nil)

;; Colour theme 
(load-theme 'suscolors t)
;;(load-theme 'github t)

;; Tramp Colour
;;(setq tramp-theme-face-remapping-alist '(background . "Purple"))
(require 'tramp-theme)
(setq tramp-theme-face-remapping-alist
			'((nil "^root$" (fringe (:inherit fringe :inverse-video t)))
				("^spartacus$" nil (default (:background "DarkPurple")))
				("^gaius$" nil (default (:background "DarkGreen")))))

;; unicode-fonts
(require 'unicode-fonts)
(unicode-fonts-setup)

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
;;(require 'agda-mode)

;; RDF (n3 mode)
;;(require 'n3-mode)
;;(add-to-list 'auto-mode-alist '("\\.ttl\\'" . n3-mode))

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


;; load csp-mode setup code
;;(add-to-list 'load-path "/home/francoisbabeuf/share/emacs/site-lisp/csp-mode")
;;(load "csp-mode-startup")

;; Prolog mode
(load-file "/home/francoisbabeuf/.emacs.d/lib/prolog.el")
(setq prolog-electric-if-then-else-flag t)
(setq prolog-electric-dot-flag t)

;;(autoload 'prolog-mode "prolog" "Major mode for editing Prolog programs." t)
;;(setq prolog-system 'mercury)

(setq auto-mode-alist (cons (cons "\\.pl" 'prolog-mode) auto-mode-alist))

(add-hook 'prolog-mode-hook
          (lambda ()
            (setq indent-tabs-mode nil)))

(setq prolog-program-name "/home/francoisbabeuf/Documents/build/ClioPatria/run.pl")




;;(setq prolog-program-name "swipl")
;; Automatic Etags for prolog
(setq tags-table-list
	  '("~/Documents/build/ClioPatria/cpack/dqs"))

;; Run this the first time you use tags
;; (create-prolog-tags "~/Documents/build/ClioPatria/cpack/dqs")
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

;; (autoload 'run-ciao-toplevel "ciao"
;;          "Start a Ciao/Prolog top-level sub-process." t)
;; (autoload 'ciao-startup "ciao"
;;          "The Ciao/Prolog program development system startup screens." t)
;; (autoload 'ciao "ciao"
;;          "Start a Ciao/Prolog top-level sub-process." t)
;; (autoload 'prolog "ciao"
;;          "Start a Ciao/Prolog top-level sub-process." t)
;; (autoload 'run-ciao-preprocessor "ciao"
;;          "Start a Ciao/Prolog preprocessor sub-process." t)
;; (autoload 'ciaopp "ciao"
;;          "Start a Ciao/Prolog preprocessor sub-process." t)
;; (autoload 'ciao-mode "ciao"
;;          "Major mode for editing and running Ciao/Prolog" t)
;; (autoload 'ciao-inferior-mode "ciao"
;;          "Major mode for running Ciao/Prolog, CiaoPP, LPdoc, etc." t)
;;(setq auto-mode-alist (cons '("\\.pl$" . ciao-mode) auto-mode-alist))
;;(setq auto-mode-alist (cons '("\\.pls$" . ciao-mode) auto-mode-alist))
;;(setq auto-mode-alist (cons '("\\.lpdoc$" . ciao-mode) auto-mode-alist))
;;(setq completion-ignored-extensions
;;    (append '(".dep" ".itf" ".po" ".asr" ".cpx")
;;             completion-ignored-extensions))


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
 '(agda2-include-dirs
   (quote
	("." "/home/francoisbabeuf/lib/agda-prelude/" "/home/francoisbabeuf/lib/agda-stdlib/")))
 '(agda2-program-args
   (quote
	("--include-path=/home/francoisbabeuf/lib/agda-prelude/src/" "--include-path=.")))
 '(custom-safe-themes
   (quote
	("23562d67c3657a80dd1afc21e1e80652db0ff819e477649d23a38c1502d1245f" default)))
 '(package-selected-packages
   (quote
	(auto-sudoedit tramp-theme tramp-term flycheck-mercury yasnippet web-mode utop unicode-fonts tuareg suscolors-theme sparql-mode sml-mode redprl ocp-indent n3-mode merlin markdown-mode magit idris-mode ghc fstar-mode)))
 '(prolog-compile-string
   (quote
	((eclipse "[%f].")
	 (mercury "mmc ")
	 (sicstus
	  (eval
	   (if
		   (prolog-atleast-version
			(quote
			 (3 . 7)))
		   "prolog:zap_file(%m,%b,compile,%l)." "prolog:zap_file(%m,%b,compile).")))
	 (swi "[%f].")
	 (t "compile(%f)."))))
 '(safe-local-variable-values
   (quote
	((eval progn
		   (let
			   ((m31-root-directory
				 (when buffer-file-name
				   (locate-dominating-file buffer-file-name ".dir-locals.el")))
				(m31-project-find-file
				 (and
				  (boundp
				   (quote m31-project-find-file))
				  m31-project-find-file)))
			 (when m31-root-directory
			   (setq tags-file-name
					 (concat m31-root-directory "TAGS"))
			   (add-to-list
				(quote compilation-search-path)
				m31-root-directory)
			   (if
				   (not m31-project-find-file)
				   (setq compile-command
						 (concat "make -C " m31-root-directory))))
			 (setq m31-executable
				   (concat m31-root-directory "andromeda.native"))))))))
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
