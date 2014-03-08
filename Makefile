.PHONY: all bnfc clean

all: 
	ghc -O2 -o hott Main.hs
bnfc:
	bnfc -p Parser -haskell Grammar.cf
	alex Parser/LexGrammar.x
	happy Parser/ParGrammar.y

%.o: %.hs
	ghc -c -O2 $< -o $@

clean:
	-@rm -f hott *.o *.hi Parser/*.o Parser/*.hi Parser/*.bak
