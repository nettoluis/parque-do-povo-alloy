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

-- Garante que os setores de dois dias são diferentes.
assert setoresNaoSaoCompartilhados {
    all disj d1, d2: Dia | no (d1.setores & d2.setores)
}
check setoresNaoSaoCompartilhados for 10

-- Garante que um ingresso não pertença a dias diferentes.
assert ingressoNaoPertenceADiasDiferentes {
    all i: Ingresso | all disj d1, d2: Dia | i in ingressosDoDia[d1] implies i not in ingressosDoDia[d2]
}
check ingressoNaoPertenceADiasDiferentes for 10

-- Cenário exemplo com 2 Dias com perfis diferentes
pred diasComPerfisDiferentes {
    #Dia = 2

    some disj d1, d2: Dia {
        #pista[d1].acessos >= 3
        #pista[d2].acessos >= 3

        -- Existe pelo menos uma pessoa presente nos dois dias.
        some (pista[d1].acessos & pista[d2].acessos)

        -- Todos os presentes em d1 possuem ingresso.
        pista[d1].acessos = ingressosDoDia[d1].dono

        -- Os dois setores restritos são utilizados em d1.
        some (Camarote.ingressos & ingressosDoDia[d1])
        some (Frontstage.ingressos & ingressosDoDia[d1])

        -- Em d2 ninguém possui ingresso.
        no ingressosDoDia[d2]
    }
}

run diasComPerfisDiferentes for 6 but exactly 2 Dia, exactly 10 Pessoa

-- Cenário exemplo com 5 Dias com perfis diferentes
pred cincoDiasComPerfisDiferentes {
    #Dia = 5

    some disj d1, d2, d3, d4, d5: Dia {

        -- Dia 1: somente pessoas sem ingresso.
        no ingressosDoDia[d1]
        #pista[d1].acessos >= 3

        -- Dia 2: somente Camarote.
        some (Camarote.ingressos & ingressosDoDia[d2])
        no (Frontstage.ingressos & ingressosDoDia[d2])
	pista[d2].acessos = ingressosDoDia[d2].dono

        -- Dia 3: somente Frontstage.
        some (Frontstage.ingressos & ingressosDoDia[d3])
        no (Camarote.ingressos & ingressosDoDia[d3])
	pista[d3].acessos = ingressosDoDia[d3].dono

        -- Dia 4: ambos os setores restritos.
        some (Camarote.ingressos & ingressosDoDia[d4])
        some (Frontstage.ingressos & ingressosDoDia[d4])
	pista[d4].acessos = ingressosDoDia[d4].dono

	-- Dia 5: todas as pessoas já foram em outro dia.
	all p: pista[d5].acessos | some d: Dia - d5 | p in pista[d].acessos
    }
}

run cincoDiasComPerfisDiferentes for 15 but exactly 5 Dia

run {} for 10