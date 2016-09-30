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
Cond(t1, t2, t3)|if t1 then t2 else t3
X(id)|id
Fn(id, typ, t)|fn(id: typ) { t }
App(t1, t2)|t1 t2
Let(id, typ, t1, t2)|let id: typ = t1; t2
LetRec(id1, typ1, typ2, id2, t1, t2)|letrec id1(id2: typ1): typ2 { t1 } in t2
Nil|nil
Cons(t1, t2)|t1::t2
IsEmpty(t)|empty? t
Head(t)|head t
Tail(t)|tail t
Raise|raise
Try(t1, t2)|try t1 except t2
