all: ParLatte.hs
	alex -g LexLatte.x

debug: info.txt

ParLatte.y LexLatte.x: Latte.cf
	bnfc $<

ParLatte.hs: ParLatte.y
	happy -gca $<

info.txt: ParLatte.y
	happy -gca ParLatte.y
clean:
	-rm -f *.log *.aux *.hi *.o *.dvi
	-rm -f DocLatte.ps
distclean: clean
	-rm -f DocLatte.* LexLatte.* ParLatte.* LayoutLatte.* SkelLatte.* PrintLatte.* TestLatte.* AbsLatte.* TestLatte ErrM.* SharedString.* Latte.dtd XMLLatte.* info.txt

