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


(setenv "TERMINUSDB_SERVER_PORT" "6363")
(setenv "TERMINUSDB_CONSOLE_BASE_URL" "https://dl.bintray.com/terminusdb/terminusdb/canary")
(setenv "TERMINUSDB_IGNORE_REF_AND_REPO_SCHEMA" "true")
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
(setq prolog-program-name "/home/gavin/.swivm/versions/v9.2.1/bin/swipl")
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
(provide 'prologhacks)
