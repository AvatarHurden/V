# Definição da Sintaxe Parseável

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

Termo|Sintaxe
---|---
True|true
False|false
I(i)|i
OP(t1, op, t2)|(t1 op t2)
Cond(t1, t2, t3)|if t1 then <br>*tab* t2 <br>else<br>*tab* t3
X(id)|id
Fn(id, typ, t)|fn(id: typ):<br>*tab* return t<br>// Deve terminar em nova linha
App(t1, t2)|<ul><li>Caso t1 termine em nova linha: t1t2 </li><li>t1 t2</li></ul>
Let(id, typ, t1, t2)|let id: typ = t1 in<br>t2
LetRec(id1, typ1, typ2, id2, t1, t2)|let rec id1(id2: typ1): typ2<br>*tab* t1<br>in t2
Nil|nil
Cons(t1, t2)|t1::t2
IsEmpty(t)|empty? t
Head(t)|head t
Tail(t)|tail t
Raise|raise
Try(t1, t2)|try<br>*tab* t1<br>except<br>*tab* t2
