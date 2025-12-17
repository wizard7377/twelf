FUN_FILES := $(basename $(wildcard src/**/*.fun))
SIG_FILES := $(basename $(wildcard src/**/*.sig))
SML_FILES := $(basename $(wildcard src/**/*.sml))

OML_FILES := $(patsubst src/, lib/, $(addsuffix .ml, $(SML_FILES) $(FUN_FILES)))
MLI_FILES := $(patsubst src/, lib/, $(addsuffix .mli, $(SIG_FILES)))

ML_FILES := $(OML_FILES) $(MLI_FILES)
CONVERTER_SCRIPT := ./grep/sr/sml_process.py
CONVERTER := python $(CONVERTER_SCRIPT)
%.ml: %.fun $(CONVERTER_SCRIPT)
	$(CONVERTER) $< $@
%.fun: %.sml $(CONVERTER_SCRIPT)
	cp $< $@
%.mli: %.sig $(CONVERTER_SCRIPT)
	$(CONVERTER) $< $@

make_ocaml: $(ML_FILES) $(MLI_FILES) 

