
;; cua-mode allows you to use windows shortcuts such as Ctrl-c, Ctrl-v, Ctrl-x, and Ctrl-z
(cua-mode t)

;; show-paren-mode is useful to find matching parenthesis
(show-paren-mode)

;; the default monospace font on Ubuntu doesn't display unicode characters correctly,
;; this one is much better. 
(set-face-attribute 'default t :font "DejaVu Sans Mono Book")
