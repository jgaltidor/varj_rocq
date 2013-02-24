
all:
	coqc AdditionalTactics.v
	coqc Atom.v
	coqc Metatheory.v
	coqc VarJ_Syntax.v
	coqc VarJ_Substitution.v
	coqc VarJ_Lookup.v
	coqc VarJ_Subtyping.v
	coqc VarJ_Wellform.v
	coqc VarJ_Typing.v
	coqc VarJ_Reduction.v

clean:
	rm *.glob *.vo
