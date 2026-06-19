help:
	@just -l

build:
	dune build

clean:
	[ ! -f Makefile ] || make cleanall
	dune clean
	rm -rf docs

# Configure the build to use coq_makefile
setup-make:
	cp _CoqProject.make _CoqProject
	coq_makefile -f _CoqProject -o Makefile

# Undo setup-make: 'make clean' and remove generated Makefile
nuke-make: 
	[ ! -f Makefile ] || make cleanall
	rm -f Makefile Makefile.conf
	rm -f _CoqProject

# Generate alectryon html documentation in docs/
alectryon:
	find _build/default/theories -path '_build/default/theories/Test/Roms' -prune -o -name '*.v' -print0 \
		| xargs -0 alectryon -Q _build/default/theories GameBoy --output-directory docs/

