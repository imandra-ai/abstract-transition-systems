
all:
	@dune build @all

clean:
	@dune clean

test:
	@dune runtest --force --no-buffer

pin-deps:
	opam pin -y -n ./vendor/ocaml-vdom/

watch:
	@dune build @all -w

.PHONY: all clean test watch pin-deps
