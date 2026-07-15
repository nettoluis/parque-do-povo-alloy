sig Dia {}

sig Pessoa {
    ingressos_comprados: set Ingresso
}

sig Ingresso {
    dia: one Dia
    setor: one SetorRestrito
    dono: lone Pessoa
}

abstract sig Setor {}
sig Pista extends Setor {}

-- Todo setor que precisa de Ingresso deve FrontStage ou Camarote
abstract sig SetorRestrito extends Setor {}
sig FrontStage extends SetorRestrito {}
sig Camarote extends SetorRestrito{}



