FUN_FILES := $(basename $(wildcard lib/**/*.fun))
SIG_FILES := $(basename $(wildcard lib/**/*.sig))
SML_FILES := $(basename $(wildcard lib/**/*.sml))

OML_FILES := $(patsubst src/, lib/, $(addsuffix .ml, $(SML_FILES) $(FUN_FILES)))
MLI_FILES := $(patsubst src/, lib/, $(addsuffix .mli, $(SIG_FILES)))

ML_FILES := $(OML_FILES) $(MLI_FILES)
CONVERTER_SCRIPT := ./grep/sr/src/main.py
CONVERTER_SOURCES := $(CONVERTER_SCRIPT) ./grep/sr/src/sml_process.py 
CONVERTER := pipenv run python $(CONVERTER_SCRIPT)
%.ml: %.fun $(CONVERTER_SOURCES)
	$(CONVERTER) $< $@
%.fun: %.sml $(CONVERTER_SOURCES)
	cp $< $@
%.mli: %.sig $(CONVERTER_SOURCES)
	$(CONVERTER) $< $@

make_ocaml: $(ML_FILES) $(MLI_FILES) 

