;;; Gavin's .emacs

;;; *******************************************
;;; MELPA
(require 'package) ;; You might already have this line
(setq package-archives '(("gnu" . "http://elpa.gnu.org/packages/")
                         ("melpa" . "http://melpa.org/packages/")))
(package-initialize) ;; You might already have this line

(add-to-list 'load-path "~/.emacs.d/setup/")

(require 'tweaks)
(require 'magithacks)
;; assorted languages
(require 'language)
(require 'tshacks)
(require 'jshacks)
(require 'rusthacks)
(require 'ai)
(require 'cpp)
;; unicode-fonts
(require 'unicode-fonts)

(require 'prologhacks)

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
 '(ispell-dictionary nil)
 '(package-selected-packages
   '(astyle direnv cuda-mode vterm nix-mode chatgpt-shell rust-playground handlebars-mode python-black prettier-rc typescript-mode json-mode company lsp-ui use-package graphql-mode restclient js2-mode session wc-mode exec-path-from-shell ttl-mode yaml-mode tide helm-lean company-lean ## lean-mode rustic flycheck magit-delta so-long tramp exwm xelb csv-mode rust-mode with-editor markdown-preview-eww spinner lsp-mode auto-sudoedit tramp-theme tramp-term flycheck-mercury yasnippet web-mode utop unicode-fonts tuareg suscolors-theme sparql-mode sml-mode redprl ocp-indent n3-mode merlin markdown-mode magit idris-mode ghc fstar-mode))
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
 '(ttl-indent-level 2)
 '(warning-suppress-types '(((unlock-file)) (comp) (comp) (comp) (comp) (comp))))
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
 '(agda2-highlight-record-face ((t (:foreground "magenta"))))
 '(compilation-error ((t (:foreground "SkyBlue"))))
 '(compilation-info ((t (:foreground "SkyBlue"))))
 '(compilation-message ((t (:foreground "SkyBlue"))))
 '(compilation-warning ((t (:foreground "SkyBlue"))))
 '(lsp-ui-peek-line-number ((t (:foreground "grey"))))
 '(magit-reflog-checkout ((t (:foreground "DeepSkyBlue1"))))
 '(rustic-cargo-outdated ((t (:foreground "orange red"))))
 '(rustic-compilation ((t (:foreground "SkyBlue"))))
 '(rustic-compilation-column ((t (:inherit compilation-column-number))))
 '(rustic-compilation-error ((t (:foreground "SkyBlue"))))
 '(rustic-compilation-info ((t (:foreground "SkyBlue"))))
 '(rustic-compilation-line ((t (:foreground "LimeGreen"))))
 '(rustic-compilation-start ((t (:foreground "SkyBlue"))))
 '(rustic-compilation-warning ((t (:foreground "SkyBlue"))))
 '(rustic-errno-face ((t (:foreground "orange red"))))
 '(transient-blue ((t (:inherit transient-key :foreground "DeepSkyBlue1"))))
 '(which-func ((t (:foreground "DeepSkyBlue1")))))
;; ## added by OPAM user-setup for emacs / base ## 56ab50dc8996d2bb95e7856a6eddb17b ## you can edit, but keep this line
;;(require 'opam-user-setup "~/.emacs.d/opam-user-setup.el")
;; ## end of OPAM user-setup addition for emacs / base ## keep this line
(put 'downcase-region 'disabled nil)

; @begin(93695291)@ - Do not edit these lines - added automatically!
;(if (file-exists-p "/home/gavin/dev/ciao/ciao_emacs/elisp/ciao-site-file.el")
;  (load-file "/home/gavin/dev/ciao/ciao_emacs/elisp/ciao-site-file.el"))
; @end(93695291)@ - End of automatically added lines.
(put 'upcase-region 'disabled nil)
