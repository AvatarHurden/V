# Definição da Sintaxe Parseável

Termo|Sintaxe
---|---
True|true
False|false
I(i)|i
OP(t1, op, t2)|t1 op t2
Cond(t1, t2, t3)|if t1 then t2 else t3
X(id)|id
Fn(id, Some typ, t)|fn(id: typ) { t }
Fn(id, None, t)|fn(id) { t }
Let(id, Some typ, t1, t2)|let id: typ = t1; t2
Let(id, None, t1, t2)|let id = t1; t2
LetRec(id1, Some typ1, Some typ2, id2, t1, t2)|let rec id1(id2: typ1): typ2 { t1 }; t2
LetRec(id1, None, None, id2, t1, t2)|let rec id1(id2) { t1 }; t2
Nil|nil
IsEmpty(t)|empty? t
Head(t)|head t
Tail(t)|tail t
Raise|raise
Try(t1, t2)|try t1 except t2

Tipo|Sintaxe
---|---
Int|Int
Bool|Bool
Function(t1, t2)|t1 -> t2
List(t)|[t]

Operação|Símbolo
---|---
Add|+
Subtract|-
Multiply|*
Divide|/
Cons|::
Application| (espaço)
LessThan|<
LessOrEqual|<=
Equal|=
Different|!=
GreaterOrEqual|>=
Greater|>

## Prioridade de operadores

A seguinte ordem de prioridade foi escolhida, baseada no comportamento de F#:

- Multiplicação, Divisão
- Soma, Subtração
- Cons
- Aplicação
- Testes (<, >, =, etc)

É possível forçar a ordem desejada de avaliação com o uso de parênteses entre operações.

## Associatividade

Existem 2 tipos de associativade. Eles são:

- Associatividade à esquerda, onde "a b c" é o mesmo que "(a b) c"
	- Fazem parte desse grupo todas as operações, com exceção de **Cons**

- Associatividade à direita, onde "a b c" é o mesmo que "a (b c)"
	- Fazem parte deste grupo a operação **Cons** e o tipo **Function**, além dos termos **head**, **tail** e **empty?**.

É possível alterar a associativade de qualquer termo com o uso de parênteses.



## Açúcar Sintático

### Listas

É possível definir listas com a seguinte sintaxe:

	[e1, e2, (...), en]

Ao fazer isso, cada elemento separado por vírgula será o primeiro termo de uma **Cons**, e o último elemento estará unido com **Nil**. 

Dessa forma, a expressão 
	
    [1,2,3]
    
É equivalente a

	Cons(1, Cons(2, Cons(3, Nil)))

### Funções nomeadas

É possível condensar uma expressão **let** seguida de uma expressão **fn** com a seguinte sintaxe: 

	let id1(id2: typ1): typ2 {
    	t
    };
    t2
    
O resultado dessa expressão é o mesmo que:

	let id1: typ1 -> typ2 = fn(id2: typ1) {
    	t
    }; 
    t2

### Funções lambda

	\id: typ => t
    
É o mesmo que:

	fn(id: typ) {
    	t
    }

### Compreensão de listas

	[t for id in t2]

É o mesmo que:

	let rec map(l) {
    	let f = fn(id) {
        	t
        };
    	if empty? l then
        	nil
        else
        	(f head l)::(map tail l)	
    }; map t2

## Variáveis

O nome de uma variável é uma string de tamanho arbitrário composto de qualquer caractere com exceção dos seguintes:

||||||
---|---|---|:---|---
.|,|;|:|\
+|-|/|*|<
=|>|!|(|)
{|}|[|]|?

Além disso, variáveis não podem ser nomeadas com os seguintes termos reservados:

||||
---|---|---|---
fn|let|rec
head|tail|nil
try|except|raise
if|then|else
true|false|
