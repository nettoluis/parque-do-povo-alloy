one sig ParqueDoPovo { 
    dias: some Dia 
}

sig Dia { 
    setores: some Setor
}

sig Pessoa {
}

sig Ingresso { 
    dono: one Pessoa
}

abstract sig Setor{} 

sig Pista extends Setor{ 
    acessos: some Pessoa 
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
    all p : Pessoa | all disj i1, i2 : p.~dono | not ingressosMesmoDia[i1, i2]
}

fact Pessoas {
    -- Toda pessoa pertence a alguma pista.
    all p : Pessoa | some d: Dia | p in pista[d].acessos
    
    -- Toda pessoa que possui um ingresso do dia pertence a pista.
    all d: Dia | ingressosDoDia[d].dono in pista[d].acessos
}

-- Retorna os setores restritos de um dia.
fun setoresRestritos[d: Dia]: set SetorRestrito {
    d.setores & SetorRestrito
}

-- Retorna os ingressos de um dia.
fun ingressosDoDia[d: Dia]: set Ingresso {
    setoresRestritos[d].ingressos
}

-- Retorna a pista de um dia.
fun pista[d: Dia]: one Pista {
    d.setores & Pista
}

-- Verifica se dois ingressos pertencem ao mesmo dia.
pred ingressosMesmoDia[i1, i2 : Ingresso] {
    some d : Dia | i1 in ingressosDoDia[d] and i2 in ingressosDoDia[d]
}

-- Verifica se os setores de dois dias são diferentes.
assert setoresNaoSaoCompartilhados {
    all disj d1, d2: Dia | no (d1.setores & d2.setores)
}
check setoresNaoSaoCompartilhados for 10

-- Garante que nenhum ingresso é compartilhado entre dias diferentes
assert ingressoPertenceAUmUnicoDia {
	all i: Ingresso | one d: Dia | i in d.ingressosDoDia
}
check ingressoPertenceAUmUnicoDia for 10

run {} for 10 but exactly 3 Dia