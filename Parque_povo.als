--O Parque do Povo existe e é único 
one sig ParqueDoPovo { 
	dias: some Dia 
}

sig Dia { 
	pista: one Pista, 
	camarote: one Camarote, 
	frontstage: one Frontstage,
	pessoaNoDia: some Pessoa,
	ingressoDoDia : set Ingresso
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

	-- Uma pessoa nao pode ter ingresso do mesmo dia.
	all p : Pessoa | all disj i1, i2 : p.~dono | not mesmoDia[i1, i2]

	--Toda pessoa pertence a algum dia.
	all p : Pessoa | some d: Dia | p in d.pessoaNoDia
	
	-- Toda pessoa que possui um ingresso do dia pertence ao dia.
	all d: Dia | all i: d.ingressoDoDia | i.dono in d.pessoaNoDia

	-- Toda pessoa tem acesso a pista do dia que esta.
	all d: Dia | d.pessoaNoDia = d.pista.acessos
	
	-- Se um ingresso está em um setor, ele também está no dia do setor.
	all d: Dia | ingressosDoDia[d] = d.ingressoDoDia

}

fun setoresDoDia[d: Dia]: set Setor { 
	d.pista + d.camarote + d.frontstage 
} 

fun ingressosDoDia[d: Dia]: set Ingresso {
    d.frontstage.ingressos + d.camarote.ingressos
}

pred mesmoDia[i1, i2 : Ingresso] {
    some d : Dia | i1 in d.ingressoDoDia and i2 in d.ingressoDoDia
}

run {} for 15 but exactly 5 Dia
