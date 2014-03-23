.PHONY: hott runTests bnfc clean

FLAGS = -O2 -odir build/ -hidir build/ \
	-fwarn-incomplete-patterns \
	-fwarn-incomplete-uni-patterns \
	-fwarn-unused-imports \

hott:
	ghc $(FLAGS) -o hott Main.hs

runTests:
	ghc $(FLAGS) -o runTests Tests/Main.hs

bnfc:
	bnfc -p Parser -haskell Grammar.cf
	alex Parser/LexGrammar.x
	happy Parser/ParGrammar.y

build/%.o: %.hs
	ghc -ibuild/ -c $(FLAGS) -o $@ $<

clean:
	-@rm -f hott runTests build/*.o build/*.hi build/Parser/*.o build/Parser/*.hi build/Syntax/*.o build/Syntax/*.hi Parser/*.bak
