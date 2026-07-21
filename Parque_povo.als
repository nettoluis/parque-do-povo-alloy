--O Parque do Povo existe e é único 
one sig ParqueDoPovo { 
	dias: some Dia 
}

sig Dia { 
	pista: one Pista, 
	camarote: one Camarote, 
	frontstage: one Frontstage,
	pessoasNoDia: some Pessoa,
	ingressosDoDia : set Ingresso
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
	-- Cada dia está associado ao Parque do Povo.
	ParqueDoPovo.dias = Dia

	-- Cada Setor está vinculado a exatamente um Dia.
	all s: Setor | one d:Dia | s in setoresDoDia[d]

	-- Cada dia tem seus Setores únicos.
	all disj d1, d2: Dia | no (setoresDoDia[d1] & setoresDoDia[d2])

	-- Cada Ingresso pertence a exatamente um setor restrito.
	all i: Ingresso | one s: SetorRestrito | i in s.ingressos

	-- Uma pessoa não pode ter dois ingresso do mesmo dia.
	all p : Pessoa | all disj i1, i2 : p.~dono | not mesmoDia[i1, i2]

	--Toda pessoa pertence a algum dia.
	all p : Pessoa | some d: Dia | p in d.pessoasNoDia
	
	-- Toda pessoa que possui um ingresso do dia pertence ao dia.
	all d: Dia | all i: d.ingressosDoDia | i.dono in d.pessoasNoDia

	-- Toda pessoa tem acesso a pista do dia que está.
	all d: Dia | d.pessoasNoDia = d.pista.acessos
	
	-- Todo ingresso de um dia pertence ao Frontstage ou ao Camarote desse dia.
	all d: Dia | d.ingressosDoDia = d.frontstage.ingressos + d.camarote.ingressos

}

fun setoresDoDia[d: Dia]: set Setor { 
	d.pista + d.camarote + d.frontstage 
} 

pred mesmoDia[i1, i2 : Ingresso] {
    one d : Dia | i1 in d.ingressosDoDia and i2 in d.ingressosDoDia
}

run {} for 10