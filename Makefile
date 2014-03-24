.PHONY: hott runTests bnfc clean

FLAGS = -O2 -odir build/ -hidir build/ \
	-fwarn-incomplete-patterns \
	-fwarn-incomplete-uni-patterns \
	-fwarn-unused-imports \

hott:
	ghc $(FLAGS) -o hott Main.hs

runTests:
	ghc $(FLAGS) -fhpc -o runTests Tests/Main.hs
	-@rm runTests.tix

bnfc:
	bnfc -p Parser -haskell Grammar.cf
	alex Parser/LexGrammar.x
	happy Parser/ParGrammar.y

build/%.o: %.hs
	ghc -ibuild/ -c $(FLAGS) -o $@ $<

clean:
	-@rm -rf \
		.hpc *.html *.tix \
		hott runTests \
		Parser/*.bak \
		build/*.o build/*.hi \
		build/Parser/*.o build/Parser/*.hi \
		build/Syntax/*.o build/Syntax/*.hi \
		
