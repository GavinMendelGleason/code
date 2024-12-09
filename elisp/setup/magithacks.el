;; Magit
(use-package magit :ensure magit)
(require 'magit)
(global-set-key (kbd "C-x g") 'magit-status)

;; Git password control
(use-package shell :ensure shell)
(setq comint-password-prompt-regexp
      (concat comint-password-prompt-regexp
              "\\|^Password for .*:\\s *\\'"))

;;; GitHub Pull Requests
;;(require 'magit-gh-pulls)
;;(add-hook 'magit-mode-hook 'turn-on-magit-gh-pulls)


(provide 'magithacks)
