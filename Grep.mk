OCAML_FILES := $(patsubst %.mlti, %.ml, $(wildcard lib/**/*.mlti))

%.ml : %.mlt %.mlti
	cat $+ > $@ 
	rm $+

make_ocaml: $(OCAML_FILES)

check_ocaml:
	echo $(OCAML_FILES)
