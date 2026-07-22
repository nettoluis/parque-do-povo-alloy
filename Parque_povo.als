one sig ParqueDoPovo { 
    dias: some Dia 
}

sig Dia { 
    setores: some Setor,
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

fact ParqueDoPovo {
    -- Todo dia está associado ao Parque do Povo.
    ParqueDoPovo.dias = Dia
}

fact Setores {
    -- Cada Setor está vinculado a exatamente um Dia.
    all s: Setor | one d:Dia | s in d.setores

    -- Cada dia tem seus Setores únicos.
    all disj d1, d2: Dia | no (d1.setores & d2.setores)

    -- Cada dia possui exatamente uma Pista, um Camarote e um Frontstage.
    all d: Dia {
        one d.setores & Pista
        one d.setores & Camarote
        one d.setores & Frontstage
    }
}

fact Ingressos {
    -- Cada Ingresso pertence a exatamente um setor restrito.
    all i: Ingresso | one s: SetorRestrito | i in s.ingressos

    -- Uma pessoa não pode ter dois ingressos do mesmo dia.
    all p : Pessoa | all disj i1, i2 : p.~dono | not mesmoDia[i1, i2]

    -- Os ingressos de um dia correspondem aos ingressos dos setores restritos desse dia.
    all d: Dia | d.ingressosDoDia = setoresRestritos[d].ingressos
}

fact Pessoas {
    --Toda pessoa pertence a algum dia.
    all p : Pessoa | some d: Dia | p in d.pessoasNoDia
    
    -- Toda pessoa que possui um ingresso do dia pertence ao dia.
    all d: Dia | d.ingressosDoDia.dono in d.pessoasNoDia

    -- Toda pessoa tem acesso a pista do dia que está.
    all d: Dia | d.pessoasNoDia = pista[d].acessos
}

fun setoresRestritos[d: Dia]: set SetorRestrito {
    d.setores & SetorRestrito
}

fun pista[d: Dia]: one Pista {
    d.setores & Pista
}

pred mesmoDia[i1, i2 : Ingresso] {
    one d : Dia | i1 in d.ingressosDoDia and i2 in d.ingressosDoDia
}

run {} for 5