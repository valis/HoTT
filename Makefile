.PHONY: all bnfc clean

all:
	ghc -O2 -fwarn-incomplete-patterns -fwarn-incomplete-uni-patterns -fwarn-unused-imports -odir build/ -hidir build/ -o hott Main.hs
bnfc:
	bnfc -p Parser -haskell Grammar.cf
	alex Parser/LexGrammar.x
	happy Parser/ParGrammar.y

build/%.o: %.hs
	ghc -ibuild/ -c -O2 $< -odir build/ -hidir build/ -o $@

clean:
	-@rm -f hott build/*.o build/*.hi build/Parser/*.o build/Parser/*.hi Parser/*.bak
