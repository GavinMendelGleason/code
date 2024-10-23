(add-hook 'markdown-mode-hook
          (lambda ()
            (prettier-js-mode)
            (visual-line-mode 1)
            (visual-fill-column-mode 1)
            (setq visual-fill-column-width 80)))

(provide 'markdownhacks)
