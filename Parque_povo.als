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

abstract sig SetorRestrito extends Setor{}

sig Camarote extends SetorRestrito{ 
	ingresso_camarote : set Ingresso 
}

sig Frontstage extends SetorRestrito{ 
	ingresso_front : set Ingresso 
}fact { 
	-- Cada dia está associado ao Parque do Povo 
	all d: Dia | d in ParqueDoPovo.dias
	-- Cada dia tem seus Setores únicos 
	all disj d1, d2: Dia | no (setoresDoDia[d1] & setoresDoDia[d2])
	-- Cada Setor está vinculado a exatamente um Dia 
	all s: Setor | one d:Dia | s in setoresDoDia[d]
	-- Toda Pessoa tem acesso a Pista 
	all p : Pista, g : Pessoa | g in p.acessos
	-- Uma Pessoa não pode ter mais de um ingresso do mesmo Dia 
	all d: Dia, p: Pessoa | lone { i: ingressosDia[d] | i.dono = p }
	-- Cada Ingresso pertence a exatamente um setor restrito 
	all i: Ingresso | one setoresRestritos[i]
}


fun setoresDoDia[d: Dia]: set Setor { 
	d.pista + d.camarote + d.frontstage 
} 
fun setoresRestritos[i: Ingresso]: set SetorRestrito { 
	ingresso_front.i + ingresso_camarote.i 
} 
fun ingressosDia[d: Dia]: set Ingresso { 
	d.frontstage.ingresso_front + d.camarote.ingresso_camarote 
}

run {} for 5 but
    exactly 5 Dia,
    exactly 5 Pista,
    exactly 5 Camarote,
    exactly 5 Frontstage,
    exactly 5 Pessoa,
    exactly 10 Ingresso

