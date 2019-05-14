# Executable aliases
CAMLC=ocamlc
CAMLYACC=ocamlyacc
CAMLLEX=ocamllex

# Assistant executable
assistant :  lexer.cmo parser.cmo interface.cmo  preuve.cmo assistant.cmo 
	$(CAMLC) -o assistant lexer.cmo parser.cmo interface.cmo preuve.cmo assistant.cmo


# ASSISTANT
assistant.cmo : assistant.ml preuve.cmo interface.cmo lexer.cmo parser.cmo parser.cmi 
	$(CAMLC) -c assistant.ml


# PREUVE
preuve.cmo : preuve.ml interface.cmo lexer.cmo parser.cmo  
	$(CAMLC) -c preuve.ml


# LEXER
lexer.ml: lexer.mll parser.cmo
	$(CAMLLEX) lexer.mll

lexer.cmo : lexer.ml
	$(CAMLC) -c lexer.ml


# PARSER
parser.mli parser.ml: parser.mly interface.cmo
	$(CAMLYACC) parser.mly

parser.cmi: parser.mli
	$(CAMLC) -c parser.mli

parser.cmo: parser.ml parser.cmi
	$(CAMLC) -c parser.ml


# INTERFACE
interface.cmo : interface.ml
	$(CAMLC) -c interface.ml


# make clean
clean:
	rm -f lexer.ml parser.ml parser.mli *.cmi *.cmo assistant



