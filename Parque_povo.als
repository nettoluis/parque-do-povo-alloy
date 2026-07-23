-- O Parque do Povo existe e é único
one sig ParqueDoPovo {
	ingressos: set Ingresso,
	pistas: set Pista
}

sig Pista {
	acessos: set Pessoa
}

-- Dia se relaciona com Pista e Pessoa.
sig Dia {
	pista: one Pista,
	pessoasNoDia: some Pessoa
}

sig Pessoa {}

abstract sig SetorPrivado {}
sig Camarote, Frontstage extends SetorPrivado {}

-- Ingresso aponta para Dia, Pessoa e SetorPrivado.
sig Ingresso {
	dia: one Dia,
	dono: one Pessoa,
	setor: one SetorPrivado
}

fact {
	-- Cada Ingresso está associado ao Parque do Povo.
	ParqueDoPovo.ingressos = Ingresso

	-- Cada Pista está associada ao Parque do Povo, e cada dia tem sua Pista exclusiva.
	ParqueDoPovo.pistas = Dia.pista
	all disj d1, d2: Dia | d1.pista != d2.pista

	-- Cada Setor Privado utilizado pertence a exatamente um dia (setores não são compartilhados entre dias).
	all sp: SetorPrivado | lone d: Dia | sp in setoresPrivadosDoDia[d]

	-- Uma pessoa não pode ter dois ingressos do mesmo dia.
	all p: Pessoa | all disj i1, i2: p.~dono | not mesmoDia[i1, i2]

	-- Toda pessoa pertence a algum dia.
	all p: Pessoa | some d: Dia | p in d.pessoasNoDia

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
check qtdIngressosPessoaLimitadaAoNumeroDeDias for 10

-- Garante que quem possui ingresso também acessa a Pista do mesmo dia
assert donoDeIngressoAcessaPistaDoDia {
	all i: Ingresso | i.dono in i.dia.pista.acessos
}
check donoDeIngressoAcessaPistaDoDia for 10

run {} for 5
