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
(require 'n3-mode)
(add-to-list 'auto-mode-alist '("\\.ttl\\'" . n3-mode))

;; Abella
(load-file "/home/francoisbabeuf/.emacs.d/lib/abella/lprolog.el")

;; Twelf
(setq twelf-root "/home/francoisbabeuf/Documents/build/twelf/")
(load (concat twelf-root "emacs/twelf-init.el"))

;; Event ML
(load-file "/home/francoisbabeuf/.emacs.d/lib/eml/eventml-mode.el")

;; JonPRL
(load-file "/home/francoisbabeuf/.emacs.d/lib/jonprl-mode/jonprl-compat.el")
(load-file "/home/francoisbabeuf/.emacs.d/lib/jonprl-mode/jonprl-mode.el")

;; OCaML
(add-to-list 'auto-mode-alist '("\\.ml\\'" . tuareg-mode))

;;;; OPAM  for OCaM
(let ((opam-share (ignore-errors (car (process-lines "opam" "config" "var" "share")))))
  (when (and opam-share (file-directory-p opam-share))
       ;; Register Merlin
	(add-to-list 'load-path (expand-file-name "emacs/site-lisp" opam-share))
	(autoload 'merlin-mode "merlin" nil t nil)
	;; Automatically start it in OCaml buffers
	(add-hook 'tuareg-mode-hook 'merlin-mode t)
	(add-hook 'caml-mode-hook 'merlin-mode t)
	;; custom key bindings
	(add-hook 'merlin-mode-hook
       (lambda ()  
		 (local-set-key (quote [?\C-x?\C-d]) (quote merlin-destruct))))
	;; Use opam switch to lookup ocamlmerlin binary
	(setq merlin-command 'opam)))


;; Fstar
(setq fstar-executable "/home/francoisbabeuf/.opam/system/bin/fstar.exe")

;; RedPRL
;;(load-file "/home/francoisbabeuf/.emacs.d/lib/redprl/redprl-mode.el")
;;(load-file "/home/francoisbabeuf/.emacs.d/lib/redprl/ob-redprl.el")
;;(load-file "/home/francoisbabeuf/.emacs.d/lib/redprl/redprl.el")
(setq redprl-command "/home/francoisbabeuf/Documents/build/sml-redprl/bin/redprl")

;; Agda
(load-file (let ((coding-system-for-read 'utf-8))
                (shell-command-to-string "agda-mode locate")))

;; load csp-mode setup code
(add-to-list 'load-path "/home/francoisbabeuf/share/emacs/site-lisp/csp-mode")
(load "csp-mode-startup")

;; Prolog mode
(load-file "/home/francoisbabeuf/.emacs.d/lib/prolog-mode/prolog.el")
(autoload 'prolog-mode "prolog" "Major mode for editing Prolog programs." t)
(setq prolog-system 'mercury)

(setq auto-mode-alist (cons (cons "\\.pl" 'prolog-mode) auto-mode-alist))

(add-hook 'prolog-mode-hook
          (lambda ()
            (setq indent-tabs-mode nil)))

(setq prolog-program-name "/home/francoisbabeuf/Documents/build/ClioPatria/run.pl")

;; Mercury
(add-to-list 'load-path
			 "/usr/local/mercury-rotd-2017-06-22/lib/mercury/elisp")
(autoload 'mercury-mode "prolog" "Major mode for editing Mercury programs." t)

(autoload 'mdb "gud" "Invoke the Mercury debugger" t)

(defvar *flymake-mercury-checker* "/home/francoisbabeuf/bin/mercury-checker.sh")

(defun flymake-mercury-init ()
  (let* ((temp-file (flymake-init-create-temp-buffer-copy
                     'flymake-create-temp-inplace))
         (local-file (file-relative-name
                      temp-file
                      (file-name-directory buffer-file-name))))
    (list *flymake-mercury-checker* (list local-file))))

(eval-after-load 'flycheck
  '(progn
	 (require 'flycheck-mercury)
	 (push '("\\([^:]*\\):\\([0-9]+\\):[0-9]+: \\(.*\\)" 1 2 nil 3) flymake-err-line-patterns)
	 (add-to-list 'flymake-allowed-file-name-masks '("\\.m\\'" flymake-mercury-init nil flymake-get-real-file-name))))

(add-hook 'mercury-mode-hook
          '(lambda ()
			 (if (not (null buffer-file-name)) (flymake-mode))))

(add-to-list 'auto-mode-alist '("\\.m\\'" . mercury-mode))
(eval-after-load 'flycheck
  '(require 'flycheck-mercury))

;;; ************************************************
;;; Customisations

(custom-set-variables
 ;; custom-set-variables was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(agda2-include-dirs
   (quote
	("." "/usr/share/agda-stdlib" "/home/francoisbabeuf/Documents/code/agda/agda-stdlib/" "/home/francoisbabeuf/Documents/code/agda/finset/")))
 '(agda2-program-args
   (quote
	("--include-path=/home/francoisbabeuf/lib/agda-stdlib/src/" "--include-path=/home/francoisbabeuf/lib/parser-combinators.code/" "--include-path=.")))
 '(custom-safe-themes
   (quote
	("23562d67c3657a80dd1afc21e1e80652db0ff819e477649d23a38c1502d1245f" default)))
 '(package-selected-packages
   (quote
	(tramp-theme tramp-term flycheck-mercury yasnippet web-mode utop unicode-fonts tuareg suscolors-theme sparql-mode sml-mode redprl ocp-indent n3-mode merlin markdown-mode magit idris-mode ghc fstar-mode)))
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
(require 'opam-user-setup "~/.emacs.d/opam-user-setup.el")
;; ## end of OPAM user-setup addition for emacs / base ## keep this line
(put 'downcase-region 'disabled nil)
