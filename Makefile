all:
	happy -gca ParLattePlus.y
	alex -g LexLattePlus.x
	ghc --make Main.hs -o interpreter
	ghc --make TestLattePlus.hs -o TestLattePlus

clean:
	-rm -f *.log *.aux *.hi *.o *.dvi

distclean: clean
	-rm -f DocLattePlus.* LexLattePlus.* ParLattePlus.* LayoutLattePlus.* SkelLattePlus.* PrintLattePlus.* TestLattePlus.* AbsLattePlus.* TestLattePlus ErrM.* SharedString.* ComposOp.* LattePlus.dtd XMLLattePlus.* Makefile*
	
