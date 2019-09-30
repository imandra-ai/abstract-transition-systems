
DUNE_OPTS ?= --profile=release
all:
	@dune build @all $(DUNE_OPTS)

clean:
	@dune clean

test:
	@dune runtest --force --no-buffer

pin-deps:
	opam pin -y -n ./vendor/ocaml-vdom/

watch:
	@dune build @all $(DUNE_OPTS) -w

.PHONY: all clean test watch pin-deps

BUILD_BASE=_build/default/src/web/
GBUCKET_BASE=https://storage.cloud.google.com/imandra-ats-demo/
gs-upload: all
	sed 's!./ats_web!$(GBUCKET_BASE)ats_web!g' $(BUILD_BASE)ats_web.html > $(BUILD_BASE)index.html
	gsutil cp '$(BUILD_BASE)*' gs://imandra-ats-demo/
	@echo "stored at https://storage.cloud.google.com/imandra-ats-demo/index.html"
