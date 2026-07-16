--O Parque do Povo existe e é único
one sig ParqueDoPovo {
	dias: some Dia
}

sig Dia {
	pista: one Pista,
	camarote: one Camarote,
	frontstage: one Frontstage
}

sig Pessoa {}

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

sig Camarote extends SetorRestrito{}
sig Frontstage extends SetorRestrito{}

fact {
	-- Cada dia está associado ao Parque do Povo
 	all d: Dia | d in ParqueDoPovo.dias

	-- Cada dia tem seus Setores únicos
	all disj d1, d2: Dia | d1.pista != d2.pista and d1.camarote != d2.camarote and d1.frontstage != d2.frontstage
	
	-- Cada Ingresso pertence a exatamente um SetorRestrito
	all i: Ingresso | one s: SetorRestrito | i in s.ingressos

	-- Cada Setor está vinculado a exatamente um Dia
	all s: Setor | one d:Dia | s = d.camarote or s = d.frontstage or s = d.pista

	-- Cada Pessoa não pode ter dois ingressos no mesmo dia
	all p: Pessoa, d: Dia | lone i: Ingresso | i.dono = p and i in d.camarote.ingressos + d.frontstage.ingressos

	--Cada Pessoa está em pelo menos um dia
	all p: Pessoa | some d: Dia | p in visitantesDoDia[d]

	-- Se a Pessoa está em um Setor Restrito naquele dia, então ele também está na Pista
	all d: Dia | all i: d.camarote.ingressos + d.frontstage.ingressos | i.dono in d.pista.acessos
    
}

fun visitantesDoDia[d: Dia]: set Pessoa {
    d.pista.acessos + d.camarote.ingressos.dono + d.frontstage.ingressos.dono
}

run {} for 5