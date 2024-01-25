((coq-mode
  . ((eval . 
	   (progn
	     (make-local-variable 'coq-prog-args)
	     (setq coq-prog-args `("-emacs" "-noinit" "-indices-matter" "-type-in-type"
"-R" "/home/matthes/Documents/Work/Research/Projects/UniMath/Githubbereich/UniMath/_build/default/UniMath" "UniMath" "-R"  "/home/matthes/Documents/Work/Research/Projects/UniMath/Githubbereich/UniMath/_build/default/largecatmodules" "largecatmodules" )))))))
