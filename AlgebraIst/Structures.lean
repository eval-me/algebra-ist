
universe u

-- α é um Type u, ou seja um elemento de um conjunto de coisas.
class binop (α : Type u) where
  mul : α → α → α -- define a operação binária.
-- Usa-se '*' como o operador de 'binop.mul a b' 
infixl:70 "*" => binop.mul -- 'infix' significa que é usado entre dois elementos e 'l' tem associatividade à esquerda como default (Não implica associatividade à direita!)

-- Define o que é um monóide como uma classe.
class monoid (M : Type u) extends binop M where
  mul_assoc (a b c : M) : (a * b) * c = a * (b * c) -- Define associatividade para esta classe
  id : M -- Existe um elemento chamado id no monóide
  id_lmul (a : M) : id * a = a -- define a operação binária identidade à esquerda
  id_rmul (a : M) : a * id = a -- define a operação binária identidade à direita

attribute [simp] monoid.id_lmul monoid.id_rmul

-- Define o que é um grupo como uma classe.
class group (G : Type u) extends monoid G where
  inv (a : G) : G -- Existe um elemento inverso para qualquer elemento do grupo.
  inv_lmul (a : G) : inv a * a = id -- define a operação binária inversa à esquerda
  inv_rmul (a : G) : a * inv a = id -- define a operação binária inversa à direita
-- Usa-se '⁻¹' como alias para 'group.inv' 
postfix:max "⁻¹" => group.inv -- 'postfix' significa que é usado após um elemento

attribute [simp] group.inv_lmul group.inv_rmul group.inv

-- Define o que é um grupo abeliano como uma classe.
class abelianGroup (G : Type u) extends group G where
  mul_comm (a b: G) : a * b = b * a -- Define comutatividade para esta classe

class subgroup (G : Type u) extends group G where
  sub : G -> Prop
  submul {a b : G} : sub a → sub b → sub (a * b)
  subid : sub id
  subinv {x : G} : sub x → sub x⁻¹ 

class cyclicGroup (G : Type u) extends group G where
  gen : G     
  cyclic : ∀ (x : G), ∃ (n : Int), x = zpow gen n
