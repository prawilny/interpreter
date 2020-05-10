all:
	-mkdir build
	cd src && \
	bnfc --functor LattePlus.cf && \
	#sed -i '/fail/d' ErrM.hs && \
	happy -gca ParLattePlus.y && \
	alex -g LexLattePlus.x && \
	ghc --make Main.hs -odir ../build -hidir ../build -o ../interpreter
	
clean:
	-rm -rf build
	-rm -f src/{DocLattePlus,LexLattePlus,ParLattePlus,SkelLattePlus,PrintLattePlus,AbsLattePlus,ErrM,TestLattePlus}.*
	-rm -f interpreter
