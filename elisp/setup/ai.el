(use-package chatgpt-shell
  :commands (chatgpt-shell)
  :custom
  (chatgpt-shell-openai-key (auth-source-pick-first-password :host "api.openai.com")))

(provide 'ai)
