OCAMLOPT := ocamlopt
OCAMLDEP := ocamldep

MODULES := Types Hello Test

.PHONY : all
all : bin/test

.PHONY : clean
clean:
	rm -fr bin obj

bin/test : $(MODULES:%=obj/%.cmx) | bin
	$(OCAMLOPT) -I obj -o $@ $^

obj/%.ml : src/%.ml | obj
	cp $< $@

obj/%.mli : src/%.mli | obj
	cp $< $@

obj :
	mkdir -p obj

bin :
	mkdir -p bin

obj/%.cmi : obj/%.mli obj/%.mli.d
	$(OCAMLOPT) -I obj -c $<

obj/%.cmx : obj/%.ml obj/%.cmi obj/%.ml.d
	$(OCAMLOPT) -I obj -c $<

obj/%.cmx : obj/%.ml obj/%.ml.d
	$(OCAMLOPT) -I obj -c $<

obj/%.d : src/% | obj
	$(OCAMLDEP) -native -I src $< > $@

-include $(MODULES:%=obj/%.mli.d)
-include $(MODULES:%=obj/%.ml.d)
