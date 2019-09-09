
all:
	@dune build @all

clean:
	@dune clean

test:
	@dune runtest --force --no-buffer

watch:
	@dune build @all -w
