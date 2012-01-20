all: ecomp.html

ecomp.html: ecomp.v ecomp.glob Makefile
	coqdoc -o ecomp.html -g -t 'Expression compiler' \
		--coqlib http://www.lix.polytechnique.fr/coq/stdlib \
		--utf8 --charset UTF-8 --interpolate --parse-comments \
		ecomp.v
	sed -r -i 's/forall/∀/g' ecomp.html
	# sed -ir 's|_\([a-zA-Z0-9]*\)|<sub>\1</sub>|g' ecomp.html

ecomp.glob: ecomp.v
	coqc ecomp.v

clean:
	-rm -f ecomp.glob ecomp.html coqdoc.css *.crashcoqide ecomp.vo ecomp.vr
