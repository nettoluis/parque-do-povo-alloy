one sig ParqueDoPovo {
	dias: some Dia
}

sig Dia {
	setores: some Setor
}

sig Pessoa {}

sig Ingresso {
	dono: one Pessoa
}

abstract sig Setor {}

sig Pista extends Setor {
	acessos: set Pessoa
}

sig Camarote extends Setor {
	ingressos: set Ingresso
}

sig Frontstage extends Setor {
	ingressos: set Ingresso
}

fact ParqueDoPovoFact {
	-- Todo Dia pertence ao Parque do Povo.
	ParqueDoPovo.dias = Dia
}

fact DiasFact {
	-- Cada Setor pertence a exatamente um Dia.
	all s: Setor | one d: Dia | s in d.setores

	-- Os Setores de um Dia não pertencem a outro Dia.
	all disj d1, d2: Dia | no (d1.setores & d2.setores)

	-- Todo Dia possui exatamente uma Pista, um Camarote e um Fronstage.
	all d: Dia | possuiSetores[d]
}

fact IngressosFact {
	-- Cada Ingresso pertence a exatamente um setor.
	all i: Ingresso | (one c: Camarote | i in c.ingressos) or (one f: Frontstage | i in f.ingressos)

	-- Um Ingresso não pode pertencer ao Camarote e ao Frontstage ao mesmo tempo.
	no (Camarote.ingressos & Frontstage.ingressos)

	-- Uma Pessoa não pode ter mais de um Ingresso do mesmo Dia.
	all d: Dia, p: Pessoa | lone { i: ingressosDoDia[d] | i.dono = p }
}

fact PessoasFact {
	-- Toda Pessoa está em pelo menos um Dia.
	all p: Pessoa | some d: Dia | p in pistaDoDia[d].acessos

	-- Toda Pessoa que possui Ingresso tem acesso à Pista daquele Dia.
	all d: Dia | ingressosDoDia[d].dono in pistaDoDia[d].acessos
}

fun pistaDoDia[d: Dia]: one Pista {
	d.setores & Pista
}

fun ingressosDoDia[d: Dia]: set Ingresso {
	(d.setores & Camarote).ingressos +
	(d.setores & Frontstage).ingressos
}

pred possuiSetores[d: Dia] {
	one (d.setores & Pista)
	one (d.setores & Camarote)
	one (d.setores & Frontstage)
}

run {} for 15 but exactly 5 Dia, 5 Ingresso, 5 Pessoa
