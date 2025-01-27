(use-package chatgpt-shell
  :ensure chatgpt-shell
  :commands (chatgpt-shell)
  :custom
  (chatgpt-shell-openai-key (auth-source-pick-first-password :host "api.openai.com")))

(setq chatgpt-shell-openai-key (getenv "OPENAI_API_KEY"))

(provide 'ai)
