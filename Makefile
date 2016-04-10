srcdir=src
parsefile=Parser.y
lexfile=Tokens.x

.PHONY: all
all:
	stack build

.PHONY : repl
repl :
	stack exec lambdapi

.PHONY : doc
doc:
	make -C doc/formal

.PHONY : clean
clean :
	rm -f $(srcdir)/Parser.hs
	make -C doc/formal clean

.PHONY : distclean
distclean : clean
	stack clean
	make -C doc/formal distclean
