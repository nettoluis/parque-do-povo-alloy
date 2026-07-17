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
	all p: Pessoa, d: Dia | lone i: Ingresso | i.dono = p and i in ingressosSetoresRestritosDoDia[d]

	--Cada Pessoa está em pelo menos um dia
	all p: Pessoa | some d: Dia | p in visitantesDoDia[d]

	-- Se a Pessoa está em um Setor Restrito naquele dia, então ele também está na Pista
	all d: Dia | all i: ingressosSetoresRestritosDoDia[d] | i.dono in d.pista.acessos
    
}

fun visitantesDoDia[d: Dia]: set Pessoa {
    d.pista.acessos + d.camarote.ingressos.dono + d.frontstage.ingressos.dono
}

fun ingressosSetoresRestritosDoDia[d : Dia]: set Ingresso{
	d.camarote.ingressos + d.frontstage.ingressos
}

-- Garantir que não existe um dia que não esteja no Parque do Povo
assert ppDias{
	one pp : ParqueDoPovo | pp.dias = Dia
}
-- Garantir que dois dias diferentes tem pistas/camarotes/frontstage diferentes
assert diasSetoresUnicos{
	all disj d1, d2 : Dia | no (d1.pista & d2.pista) 
	all disj d1, d2 : Dia | no (d1.camarote & d2.camarote)
	all disj d1, d2 : Dia | no (d1.frontstage & d2.frontstage)
}
-- Garantir que todo ingresso tem um único setor associado
assert ingressoUnicoSetorRestrito{
	all disj s1, s2 : SetorRestrito | no (s1.ingressos & s2.ingressos)
}
-- Garantir que toda pessoa está em um dia
assert pessoaPeloMenosUmDia{
	no (Pessoa - Dia.visitantesDoDia)
}
-- Garantir que uma pessoa não pode ter dois ingressos no mesmo dia
assert pessoaIngressosMesmoDia{
	all disj i1, i2 : Ingresso | all d : Dia | (i1 in ingressosSetoresRestritosDoDia[d] and i2 in ingressosSetoresRestritosDoDia[d]) implies i1.dono != i2.dono
}

check ppDias for 15 but exactly 5 Dia, 5 Pessoa
check diasSetoresUnicos for 15 but exactly 5 Dia, 5 Pessoa
check ingressoUnicoSetorRestrito for 15 but exactly 5 Dia, 5 Pessoa
check pessoaIngressosMesmoDia for 15 but exactly 5 Dia, 5 Pessoa
check pessoaPeloMenosUmDia for 15 but exactly 5 Dia, 5 Pessoa

run {} for 5