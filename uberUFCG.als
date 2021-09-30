module uberUFCG

-- Regiões
abstract sig Regiao {}

one sig CENTRO, LESTE, OESTE, NORTE, SUL extends Regiao {}
---

-- Horários
abstract sig HIda, HVolta {}

one sig SeteMeia, NoveMeia, TrezeMeia, QuinzeMeia extends HIda {}
one sig Dez, Doze, Dezesseis, Dezoito extends HVolta {}
---

-- Pessoas
sig Debito {}
sig Credito {}

abstract sig Pessoa {
    debitos: set Debito,
    creditos: set Credito
}

sig Aluno extends Pessoa {}
sig Professor extends Pessoa {}
sig Servidor extends Pessoa {}
---

-- Corridas
abstract sig Corrida {
    passageiros: some Pessoa,
    motorista: one Pessoa
}

sig Ida extends Corrida {
    horario: one HIda,
    regiao: one Regiao
}

sig Volta extends Corrida {
    horario: one HVolta,
    regiao: one Regiao
}
---

-- Fatos
fact RegrasUberUFCG {
    -- uma pessoa não pode ser motorista e passageiro ao mesmo tempo
    all c:Corrida | c.motorista !in c.passageiros

    -- qualquer corrida tem no máximo 3 passageiros
    all c:Corrida | #(c.passageiros) <= 3
    
    -- uma pessoa não pode estar em duas corridas de ida ou de volta no mesmo horário
    all c1:Ida | (all c2:Ida | ((c1.horario = c2.horario) and c1 != c2)  implies ((#(c1.passageiros & c2.passageiros) = 0) and (#(c1.motorista & c2.motorista) = 0)) and  (#(c1.motorista & c2.passageiros) = 0)  and  (#(c2.motorista & c1.passageiros) = 0))
    all c1:Volta | (all c2:Volta | ((c1.horario = c2.horario) and c1!=c2)  implies ((#(c1.passageiros & c2.passageiros) = 0) and (#(c1.motorista & c2.motorista) = 0) and  (#(c1.motorista & c2.passageiros) = 0)  and  (#(c2.motorista & c1.passageiros) = 0)))
        
   -- toda pessoa tem uma quantidade de créditos igual as corridas em que ele foi motorista, e uma quantidade de débitos igual as corridas em que ele foi passageiro 
    all p:Pessoa | #(p.creditos) = #(p.~motorista) 
    all p:Pessoa | #(p.debitos) = #(p.~passageiros) 
	
    -- toda pessoa tem que estar em pelo menos uma corrida, como passageiro ou como motorista
    all p:Pessoa | some c:Corrida | (p in c.passageiros) or (p in c.motorista)    
	
    -- todo crédito e débito está relacionado a uma pessoa
    all d:Debito | one p:Pessoa | (d in p.debitos)
    all c:Credito | one p:Pessoa | (c in p.creditos) 
}
---

--- executando 
pred show () {}

run show for 5
---