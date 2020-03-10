
all: index.html

%.html: %.md
	markdown $< > $@
