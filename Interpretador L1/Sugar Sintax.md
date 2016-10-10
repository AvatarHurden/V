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
Resto| %
Cons|::
Concat|@
Application| (espaço)
Pipe| &#124;>
BackwardsPipe| <&#124;
LessThan|<
LessOrEqual|<=
Equal|=
Different|!=
GreaterOrEqual|>=
Greater|>

## Prioridade de operadores

A seguinte ordem de prioridade foi escolhida, baseada no comportamento de F#:

- Aplicação
- Multiplicação, Divisão
- Soma, Subtração, Resto
- Cons
- Concat
- Testes (<, >, =, etc), Pipe, BackwardsPipe

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

## Funções com múltiplos parâmetros

É possível especificar mais de um parâmetro para todas as construções que definem funções (**Fn**, **let rec**, **funções lambda** e **funções nomeadas**). São suportadas tanto as versões tipadas explicitamente quanto as implicitamente, mas é preciso que todos os parâmetros tenham a mesma tipagem (ou seja, se um tipo é especificado, todos devem ser).

Cada parâmetro é separado com uma vírgula.

	let rec sum2(x:Int, y:Int): Int {
		x+y
    };
    
    (\x, y => x + y)
    
    let sum3(x: Int, y: Int, z: Int): Int { 
    	x + y + z 
    };
    
Cada uma dessas construções é transformada em uma cadeia de **Fn** internamente. Os exemplos acima se transformam em:

	let rec sum2(x: Int): Int -> Int {
        fn(y: Int) {
        	x + y
        }
	};
    
    fn(x) {
        fn(y) {
        	x + y
        }
	}
    
    let sum3: Int -> Int -> Int -> Int = fn(x: Int) {
        fn(y: Int) {
            fn(z: Int) {
                x + y + z
            }
        }
	};
    
Como é possível ver, a informação de tipo é criada corretamente, e o tipo de tipagem (implícita ou explícita) é mantido.

### Pipe

Passa o valor da esquerda para a função da direita. Seu funcionamento é exatamente como um **Application**, porém com os termos invertidos. Dessa forma,

	e1 |> e2
    
É igual a

	e2 e1
    
O seu uso permite a eliminação de parênteses e uma leitura mais natural de expressões.

	let soma1(x) {
    	x+1
    };
    let mult2(y) {
    	y*2
    };
    
    soma1 (mult2 3) // Requer parênteses
    
    mult2 3 |> soma1
    
    3 |> mult2 |> soma1 // Leitura da esquerda para a direita
    
### Backwards Pipe

Funciona como a aplicação normal, porém possui uma prioridade menor do que a mesma.

### Resto

Retorna o resto da divisão do primeiro elemento pelo segundo.

Requer a presença da stdlib para funcionar.

### Concat

Concatena duas listas, retornando uma nova lista composta dos elementos da primeira seguidos pelos elementos da segunda.

Requer a presença da stdlib para funcionar.

## Variáveis

O nome de uma variável é uma string de tamanho arbitrário composto de qualquer caractere com exceção dos seguintes:

||||||
---|---|---|:---|---
.|,|;|:|\
+|-|/|*|<
=|>|!|(|)
{|}|[|]|%
@||||

* Apesar de ser permitido o uso da interrogação (?) em qualquer posição de um nome, é um padrão colocá-la apenas no final de nomes de funções que retornam um booleano.
* É permitido colocar dígitos no nome de uma varíavel, porém não é permitido começar o nome de uma variável com um dígito.

Além disso, variáveis não podem ser nomeadas com os seguintes termos reservados:

|||||
---|---|---|---|
fn|let|rec|for
in|head|tail|nil
try|except|raise|true
false|if|then|else
empty?|||

# Standard Library

Como em muitas linguagens de programação, o nosso "compilador" de L1 acompanha uma biblioteca com funções comuns a muitos programas.

As funções implementadas são as seguintes:

- remainder(x,y)
 	- Retorna o resto da divisão de x por y
- negate(x)
	- Retorna o oposto de x (ou seja, -x)
- abs(x)
	- Retorna o valor absoluto de x


- not(x)
 	- Operador lógico de Negação
- and(x,y)
	- Operador lógico E
- or(x,y)
	- Operador lógico Ou
- xor(x,y)
	- Operador lógico Ou Exclusivo


- length(ls) 
	- Retorna o tamanho da lista
- reverse(ls) 
	- Retorna uma nova lista com os elementos de ls em ordem invertida


- last(ls) 
 	- Retorna o último elemento de uma lista
- init(ls) 
	- Retorna toda a lista exceto o último elemento
- append(x, ls) 
	- Adiciona o elemento x no final da lista
- concat(ls1, ls2) 
	- Retorna uma lista composta pelos elementos de ls1 seguidos pelos elementos de ls2


- map(f, ls) 
	- Retorna uma nova lista com a aplicação da função f a cada elemento de ls
- fold(f, acc, ls)
	- Processa cada elemento de ls, da esquerda para a direita, acumulando o valor em acc. Retorna acc
- reduce(f, ls)
	- Exatamente igual a fold, porém acc é iniciado com o primeiro elemento de ls e o processamento começa a partir do segundo elemento


- take(x, ls) 
	- Retorna os primeiros x elementos de ls
- takeWhile(pred, ls)
	- Retorna todos os elementos de ls que satisfazem *pred* até o primeiro que não satisfaz *pred*
- filter(pred, ls)
	- Retorna todos os elementos de ls que satisfazem *pred*


- all(pred, ls)
	- Retorna true se todos os elementos de ls satisfazem *pred*
- any(pred, ls)
	- Retorna true se qualquer elemento de ls satisfaz *pred*


- range(start, finish, inc)
	- Retorna uma lista com os elementos [start, start+inc, start+2*inc, ..., n], sendo que n é menor ou igual a finish.

Para fazer uso da biblioteca, é necessário colocar o arquivo "stdlib.l1" no mesmo diretório do executável.