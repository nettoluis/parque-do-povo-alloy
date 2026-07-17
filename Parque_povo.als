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

	--Toda Pessoa está em pelo menos um Dia
	all p: Pessoa | some d: Dia | p in d.pista.acessos

	-- Toda Pessoa que tem ingresso tem acesso a pista daquele Dia
	all d: Dia | ingressosDoDia[d].dono in d.pista.acessos

	-- Uma Pessoa não pode ter mais de um ingresso do mesmo Dia 
	all d: Dia, p: Pessoa | lone { i: ingressosDoDia[d] | i.dono = p }
}

fun setoresDoDia[d: Dia]: set Setor { 
	d.pista + d.camarote + d.frontstage 
} 
fun ingressosDoDia[d: Dia]: set Ingresso { 
	d.frontstage.ingressos + d.camarote.ingressos
}

run {} for 5