all: ecomp.html

ecomp.html: ecomp.v ecomp.glob
	coqdoc -o ecomp.html -g -t 'Expression compiler' --utf8 --charset UTF-8 --interpolate --parse-comments ecomp.v

ecomp.glob: ecomp.v
	coqc ecomp.v

clean:
	-rm -f ecomp.glob ecomp.html coqdoc.css *.crashcoqide ecomp.vo ecomp.vr
