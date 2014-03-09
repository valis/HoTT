.PHONY: all bnfc clean

FLAGS = -O2 -odir build/ -hidir build/ \
	-fwarn-incomplete-patterns \
	-fwarn-incomplete-uni-patterns \
	-fwarn-unused-imports \

all:
	ghc $(FLAGS) -o hott Main.hs

bnfc:
	bnfc -p Parser -haskell Grammar.cf
	alex Parser/LexGrammar.x
	happy Parser/ParGrammar.y

build/%.o: %.hs
	ghc -ibuild/ -c $(FLAGS) -o $@ $<

clean:
	-@rm -f hott build/*.o build/*.hi build/Parser/*.o build/Parser/*.hi build/Syntax/*.o build/Syntax/*.hi Parser/*.bak
