-- O Parque do Povo existe e é único
one sig ParqueDoPovo {
	ingressos: set Ingresso,
	pista : set Pista
}

sig Pista {
	acessos: set Pessoa
}

-- Dia se relaciona com Pista e Pessoa.
some sig Dia {
	pista: one Pista,
	setores: some SetorPrivado,
	pessoasNoDia: some Pessoa
}

sig Pessoa {}

abstract sig SetorPrivado {
	acesso : set Pessoa
}
sig Camarote, Frontstage extends SetorPrivado {
}

-- Ingresso aponta para Dia, Pessoa e SetorPrivado.
sig Ingresso {
	dia: one Dia,
	dono: one Pessoa,
	setor: one SetorPrivado
}

fact {
	
	-- Toda pista está associado ao Parque do Povo.
    	ParqueDoPovo.pista = Pista

	-- Cada Ingresso está associado ao Parque do Povo.
	ParqueDoPovo.ingressos = Ingresso

	-- Cada Setor Privado utilizado pertence a exatamente um dia (setores não são compartilhados entre dias).
	all sp: SetorPrivado | lone d: Dia | sp in setoresPrivadosDoDia[d]

	-- Uma pessoa não pode ter dois ingressos do mesmo dia.
	all p: Pessoa | all disj i1, i2: p.~dono | not mesmoDia[i1, i2]

	  -- Cada dia tem seus Setores e Pistas únicos.
    	all disj d1, d2: Dia | no (d1.setores & d2.setores) and no (d1.pista & d2.pista)

	 -- Cada dia possui exatamente uma Pista, um Camarote e um Frontstage.
    	all d: Dia {
        		one d.setores & Camarote
        		one d.setores & Frontstage
    		}

	-- Toda pessoa pertence a algum dia.
	all p: Pessoa | some d: Dia | p in d.pessoasNoDia
	
	-- Se a pessoa tem o ingresso, tem acesso ao setor do ingresso.
	all i : Ingresso | i.dono in i.setor.acesso

	-- Toda pessoa que tem acesso ao setor possui um ingresso daquele setor.
	all s : SetorPrivado | all p : s.acesso | some i : Ingresso | p = i.dono and i.setor = s

	-- Toda pessoa que possui um ingresso de um dia pertence a esse dia.
	all i: Ingresso | i.dono in i.dia.pessoasNoDia

	-- Toda pessoa tem acesso à pista do dia em que está.
	all d: Dia | d.pessoasNoDia = d.pista.acessos
}

-- Retorna todos os ingressos vinculados a um determinado dia.
fun ingressosDoDia[d: Dia]: set Ingresso {
	d.~dia
}

-- Retorna os setores privados usados nos ingressos de um determinado dia.
fun setoresPrivadosDoDia[d: Dia]: set SetorPrivado {
	ingressosDoDia[d].setor
}

-- Verifica se dois ingressos pertencem ao mesmo dia.
pred mesmoDia[i1, i2: Ingresso] {
	i1.dia = i2.dia
}

-- Garante que a quantidade de ingressos de uma pessoa nunca ultrapassa o número total de dias
assert qtdIngressosPessoaLimitadaAoNumeroDeDias {
	all p: Pessoa | #(p.~dono) <= #Dia
}


run {} for 5
