(use-package proof-general
  :defer t
  :mode ("\\.v\\'" . coq-mode)  ; open .v files in Coq mode
  :init
  ;; Optional: point Proof General at your Coq/Rocq binary if needed.
  ;; Usually not necessary if coqc is on PATH.
  ;; (setq coq-prog-name "coqtop")    ; or "rocq" / "rocqtop" if you prefer
  :ensure proof-general
  )

(provide 'proof)
