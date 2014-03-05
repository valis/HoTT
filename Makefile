all: 
	ghc -O2 -o HoTT Main.hs
bnfc:
	bnfc -p Parser -haskell Grammar.cf
	alex Parser/LexGrammar.x
	happy Parser/ParGrammar.y
