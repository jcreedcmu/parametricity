# thanks to
# https://stackoverflow.com/questions/58339725/literate-agda-in-markdown-format-to-latex-via-pandoc
# https://jesper.sikanda.be/posts/literate-agda.html
# for explaining how to do this

html:
	agda --html --html-highlight=code --html-dir=/tmp/agda-html StrictEquiv.lagda.md
	pandoc -s --css=style.css --css=Agda.css /tmp/agda-html/StrictEquiv.md -o /tmp/agda-html/StrictEquiv.html
   cp style.css /tmp/agda-html/style.css
   # file is now viewable as /tmp/agda-html/StrictEquiv.html
