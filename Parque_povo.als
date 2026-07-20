--O Parque do Povo existe e é único 
one sig ParqueDoPovo { 
	dias: some Dia 
}

sig Dia { 
	pista: one Pista, 
	camarote: one Camarote, 
	frontstage: one Frontstage,
	pessoa_no_dia : some Pessoa,
	ingresso_do_dia : set Ingresso
}

sig Pessoa {
}

sig Ingresso { 
	dono: one Pessoa
}

abstract sig Setor{} 

sig Pista extends Setor{ 
	acessos: set Pessoa 
}

abstract sig SetorRestrito extends Setor{
	ingressos: set Ingresso
}

sig Camarote, Frontstage extends SetorRestrito{}

fact { 
	-- Cada dia está associado ao Parque do Povo 
	ParqueDoPovo.dias = Dia

	-- Cada Setor está vinculado a exatamente um Dia 
	all s: Setor | one d:Dia | s in setoresDoDia[d]

	-- Cada dia tem seus Setores únicos 
	all disj d1, d2: Dia | no (setoresDoDia[d1] & setoresDoDia[d2])

	-- Cada Ingresso pertence a exatamente um setor restrito 
	all i: Ingresso | one s: SetorRestrito | i in s.ingressos

	--Toda pessoa pertence a algum dia.
	all p : Pessoa | some d: Dia | p in d.pessoa_no_dia
	
	-- Toda pessoa tem acesso a pista do dia que esta.
	all d : Dia | all p : d.pessoa_no_dia | p in d.pista.acessos

	-- Uma pessoa nao pode ter ingresso do mesmo dia.
	all p : Pessoa | all disj i1, i2 : p.~dono | not mesmoDia[i1, i2]

	-- Um ingresso so tem um dia
	all i : Ingresso | one d : Dia | i in d.ingresso_do_dia
}

fun setoresDoDia[d: Dia]: set Setor { 
	d.pista + d.camarote + d.frontstage 
} 


pred mesmoDia[i1, i2 : Ingresso] {
    some d : Dia | i1 in d.ingresso_do_dia and i2 in d.ingresso_do_dia
}

run {} for 10 but exactly 4 Ingresso
