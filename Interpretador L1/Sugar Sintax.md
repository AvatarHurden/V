# Definição da Sintaxe Parseável

Termo|Sintaxe
---|---
True|true
False|false
I(i)|i
OP(t1, op, t2)|t1 op t2
Cond(t1, t2, t3)|if t1 then t2 else t3
X(id)|id
Fn(id, typ, t)|fn(id: typ) { t }
App(t1, t2)|t1 t2
Let(id, typ, t1, t2)|let id: typ = t1; t2
LetRec(id1, typ1, typ2, id2, t1, t2)|let rec id1(id2: typ1): typ2 { t1 }; t2
Nil|nil
Cons(t1, t2)|t1::t2
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
LessThan|<
LessOrEqual|<=
Equal|=
Different|!=
GreaterOrEqual|>=
Greater|>

## Variáveis

O nome de uma variável é uma string de tamanho arbitrário com o seguinte conjunto de caracteres restritos:

|||||
---|---|---|:---|---
.|,|;|:
+|-|/|*
<|=|>|!
(|)|{|}
[|]|?| (espaço)

Além disso, variáveis não podem ser nomeadas com os seguintes termos reservados:

||||
---|---|---|---
fn|let|rec
head|tail|nil
try|except|raise
if|then|else
true|false|

## Associatividade

Existem 2 tipos de associativade. Eles são:

- Associatividade à esquerda, onde "a b c" é o mesmo que "(a b) c"
	- Fazem parte desse grupo os termos **OP** e **App**

- Associatividade à direita, onde "a b c" é o mesmo que "a (b c)"
	- Fazem parte deste grupo o termo **Cons** e o tipo **Function**

É possível alterar a associativade de qualquer termo com o uso de parênteses.

