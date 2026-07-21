--O Parque do Povo existe e é único 
one sig ParqueDoPovo { 
    dias: some Dia 
}

sig Dia { 
    pista: one Pista, 
    camarote: one Camarote, 
    frontstage: one Frontstage,
    pessoasNoDia: some Pessoa,
    ingressosDoDia : set Ingresso
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
    -- Cada dia está associado ao Parque do Povo.
    ParqueDoPovo.dias = Dia

    -- Cada Setor está vinculado a exatamente um Dia.
    all s: Setor | one d:Dia | s in setoresDoDia[d]

    -- Cada dia tem seus Setores únicos.
    all disj d1, d2: Dia | no (setoresDoDia[d1] & setoresDoDia[d2])

    -- Cada Ingresso pertence a exatamente um setor restrito.
    all i: Ingresso | one s: SetorRestrito | i in s.ingressos

    -- Uma pessoa não pode ter dois ingresso do mesmo dia.
    all p : Pessoa | all disj i1, i2 : p.~dono | not mesmoDia[i1, i2]

    --Toda pessoa pertence a algum dia.
    all p : Pessoa | some d: Dia | p in d.pessoasNoDia
    
    -- Toda pessoa que possui um ingresso do dia pertence ao dia.
    all d: Dia | all i: d.ingressosDoDia | i.dono in d.pessoasNoDia

    -- Toda pessoa tem acesso a pista do dia que está.
    all d: Dia | d.pessoasNoDia = d.pista.acessos
    
    -- Todo ingresso de um dia pertence ao Frontstage ou ao Camarote desse dia.
    all d: Dia | d.ingressosDoDia = d.frontstage.ingressos + d.camarote.ingressos

}

fun setoresDoDia[d: Dia]: set Setor { 
    d.pista + d.camarote + d.frontstage 
} 

pred mesmoDia[i1, i2 : Ingresso] {
    one d : Dia | i1 in d.ingressosDoDia and i2 in d.ingressosDoDia
}

-- Garante que todo dia do modelo pertence ao Parque do Povo.
assert todoDiaPertenceAoParque {
    all d: Dia | d in ParqueDoPovo.dias
}
check todoDiaPertenceAoParque for 10

-- Garante que um mesmo setor nunca aparece em dois dias diferentes.
assert setorNuncaApareceEmDoisDias {
    all s: Setor, disj d1, d2: Dia | not (s in setoresDoDia[d1] and s in setoresDoDia[d2])
}
check setorNuncaApareceEmDoisDias for 10

-- Garante que todo ingresso pertence a exatamente um setor restrito (Camarote ou Frontstage).
assert ingressoEhDeExatamenteUmSetor {
    all i: Ingresso | not ((i in Camarote.ingressos) <=> (i in Frontstage.ingressos))
}
check ingressoEhDeExatamenteUmSetor for 10

-- Garante que dois ingressos distintos do mesmo dia nunca pertencem à mesma pessoa.
assert doisIngressosMesmoDiaTemDonosDistintos {
    all d: Dia | all disj i1, i2: d.ingressosDoDia | i1.dono != i2.dono
}
check doisIngressosMesmoDiaTemDonosDistintos for 10

-- Garante que ninguém possui ingresso de um dia sem pertencer a esse dia.
assert quemNaoEstaNoDiaNaoTemIngressoDoDia {
    all d: Dia, p: Pessoa | p not in d.pessoasNoDia => no (p.~dono & d.ingressosDoDia)
}
check quemNaoEstaNoDiaNaoTemIngressoDoDia for 10

-- Garante que ninguém acessa Camarote ou Frontstage sem possuir ingresso correspondente ao mesmo setor e dia.
assert acessoSetorRestritoExigeIngresso {
    all d: Dia, p: Pessoa, sr: (d.camarote + d.frontstage) |
    p in sr.ingressos.dono => some i: sr.ingressos | i.dono = p
}
check acessoSetorRestritoExigeIngresso for 10

run {} for 10

