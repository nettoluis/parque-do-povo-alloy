sig Visitante {
    ingressos: some Ingresso

}

abstract sig Setor{
    visitantes : set Visitante
}

sig Pista extends Setor{    
}

sig Camarote extends Setor{
}

sig Frontstage extends Setor{
}


abstract sig Ingresso{
    visitante : one Visitante
}

sig IngressoPista extends Ingresso{}
sig IngressoCamarote extends Ingresso{}
sig IngressoFrontStage extends Ingresso{}



fact {
    -- Cada visitante pode no máximo ter 1 ingresso
    all v:Visitante | lone ingressos.i
    -- Todo visitante tem acesso a Pista
    all v:Visitante | esta_presente[v, Pista]
}

pred esta_presente[v:Visitante, s:Setor]{
    v in s
}
