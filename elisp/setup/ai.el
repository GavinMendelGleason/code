(use-package chatgpt-shell
  :ensure chatgpt-shell
  :commands (chatgpt-shell)
  )

(setq chatgpt-shell-openai-key
      (string-trim (shell-command-to-string "pass show Profile/default/OPENAI_API_KEY")))

(setq chatgpt-shell-anthropic-key
      (string-trim (shell-command-to-string "pass show Profile/default/ANTHROPIC_API_KEY")))

(provide 'ai)
