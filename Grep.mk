OCAML_FILES := $(patsubst %.mlti, %.ml, $(wildcard lib/**/*.mlti))

%.ml: %.mlti %.mlt 
	cat $+ > $@
	rm $+ 
make_ocaml: $(OCAML_FILES)