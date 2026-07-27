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

-- Garante que quem possui um ingresso também tem acesso à Pista do mesmo dia do ingresso
assert donoDeIngressoAcessaPistaDoDia {
	all i: Ingresso | i.dono in pistaDoDia[i.dia].acessos
}
check donoDeIngressoAcessaPistaDoDia for 10

-- Garante que dois ingressos que apontam para o mesmo Setor Privado pertencem necessariamente ao mesmo Dia
assert ingressosMesmoSetorEstaoNoMesmoDia {
	all disj i1, i2: Ingresso | i1.setor = i2.setor => i1.dia = i2.dia
}
check ingressosMesmoSetorEstaoNoMesmoDia for 10

--Cenários exemplos

-- Cenário de dia único
pred diaUmDuasPessoasDoisIngressosFrontCamarote[] {
    #Dia = 1
    #Pessoa = 2
    #Ingresso = 2
    one i: Ingresso | i.setor in Frontstage
    one i: Ingresso | i.setor in Camarote
}
run diaUmDuasPessoasDoisIngressosFrontCamarote for 5 but exactly 1 Dia, exactly 2 Pessoa, exactly 2 Ingresso, exactly 1 Frontstage, exactly 1 Camarote

-- Cenário com dois dias
pred doisDiasDoisIngressosFrontCamaroteCada[] {
    #Dia = 2
    all d: Dia | #d.pessoasNoDia = 2
    #Ingresso = 4
    all d: Dia |
        (one i: Ingresso | i.dia = d and i.setor in Frontstage) and
        (one i: Ingresso | i.dia = d and i.setor in Camarote)
}
run doisDiasDoisIngressosFrontCamaroteCada for 10
    but exactly 2 Dia, exactly 4 Ingresso, exactly 2 Frontstage, exactly 2 Camarote

-- Cenário com três dias
pred tresDiasDoisIngressosFrontCamaroteCada[] {
    #Dia = 3
    all d: Dia | #d.pessoasNoDia = 2
    #Ingresso = 6
    all d: Dia |
        (one i: Ingresso | i.dia = d and i.setor in Frontstage) and
        (one i: Ingresso | i.dia = d and i.setor in Camarote)
}
run tresDiasDoisIngressosFrontCamaroteCada for 10
    but exactly 3 Dia, exactly 6 Ingresso, exactly 3 Frontstage, exactly 3 Camarote

-- Cenário com quatro dias
pred quatroDiasDoisIngressosFrontCamaroteCada[] {
    #Dia = 4
    all d: Dia | #d.pessoasNoDia = 2
    #Ingresso = 8
    all d: Dia |
        (one i: Ingresso | i.dia = d and i.setor in Frontstage) and
        (one i: Ingresso | i.dia = d and i.setor in Camarote)
}
run quatroDiasDoisIngressosFrontCamaroteCada for 10
    but exactly 4 Dia, exactly 8 Ingresso, exactly 4 Frontstage, exactly 4 Camarote

-- Cenário com cinco dias
pred cincoDiasDoisIngressosFrontCamaroteCada[] {
    #Dia = 5
    all d: Dia | #d.pessoasNoDia = 2
    #Ingresso = 10
    all d: Dia |
        (one i: Ingresso | i.dia = d and i.setor in Frontstage) and
        (one i: Ingresso | i.dia = d and i.setor in Camarote)
}
run cincoDiasDoisIngressosFrontCamaroteCada for 10
    but exactly 5 Dia, exactly 10 Ingresso, exactly 5 Frontstage, exactly 5 Camarote
