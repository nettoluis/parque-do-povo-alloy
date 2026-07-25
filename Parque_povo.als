-- O Parque do Povo existe e é único
one sig ParqueDoPovo {
	dias: some Dia,
}

-- Dia se relaciona com Setores - SetorPrivado e Pista
some sig Dia {
	setores: some Setor,	
	pessoasNoDia: some Pessoa
}

some sig Pessoa {}

abstract sig Setor {}
sig Pista extends Setor {
	acessos: set Pessoa
}

abstract sig SetorPrivado extends Setor {}
sig Camarote, Frontstage extends SetorPrivado {}

-- Ingresso aponta para Dia, Pessoa e SetorPrivado.
sig Ingresso {
	dia: one Dia,
	dono: one Pessoa,
	setor: one SetorPrivado
}

fact ParqueDoPovo {
    -- Todo dia pertence ao Parque do Povo.
    ParqueDoPovo.dias = Dia
}

fact Setores {
    -- Todo setor pertence a exatamente um dia.
    all s: Setor | one d: Dia | s in d.setores

    -- Dias não compartilham setores.
    all disj d1, d2: Dia | no (d1.setores & d2.setores)

    -- Cada dia possui exatamente uma pista, um camarote e um frontstage.
    all d: Dia {
        one pistaDoDia[d]
        one d.setores & Camarote
        one d.setores & Frontstage
    }
}

fact Ingressos {
    -- O setor do ingresso pertence ao dia do ingresso.
    all i: Ingresso | i.setor in i.dia.setores

    -- Uma pessoa não pode ter dois ingressos do mesmo dia.
    all p: Pessoa | all disj i1, i2: p.~dono | not mesmoDia[i1, i2]
}

fact Pessoas {
    -- Toda pessoa pertence a algum dia.
    all p: Pessoa | some d: Dia | p in d.pessoasNoDia

    -- Quem possui um ingresso de um dia pertence a esse dia.
    all i: Ingresso | i.dono in i.dia.pessoasNoDia

    -- Todas as pessoas presentes em um dia têm acesso à pista.
    all d: Dia | d.pessoasNoDia = pistaDoDia[d].acessos
}

-- Retorna a Pista associada a um determinado dia.
fun pistaDoDia[d: Dia]: one Pista {
	d.setores & Pista
}

-- Verifica se dois ingressos pertencem ao mesmo dia.
pred mesmoDia[i1, i2: Ingresso] {
	i1.dia = i2.dia
}

-- Garante que a quantidade de ingressos de uma pessoa nunca ultrapassa o número total de dias
assert qtdIngressosPessoaLimitadaAoNumeroDeDias {
	all p: Pessoa | #(p.~dono) <= #Dia
}

run {} for 10