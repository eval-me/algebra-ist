import AlgebraIst.Structures

-- Um teorema que diz que um monóide tem apenas um elemento identidade. (Por definição isto aplica-se a todas as classes que extendem os monóides como por exemplo o grupo)
theorem unique_id {α : Type u} {M : monoid α} (e : α) (h : ∀ a : α, e * a = a) : e = M.id := by
  have h1 := M.id_rmul e -- define h1 como 'id * e = e'
  rw [h M.id] at h1 -- aplica h com id ou seja 'e * monoid.id' transforma-se em  'e'
  exact h1.symm -- temos agora que monoid.id = e, mas queremos e = monoid.id, ou seja queremos o simétrico!

-- Um teorema que diz que se a, b, c são elementos de um grupo e a * b = a * c ∨ b * a = c * a, então b = c.
@[simp] -- usa-se simp tactic para termos acesso automático a esta regra!
theorem cancellation_law {α : Type u} {G : group α} (a b c : α) : (a * b = a * c ∨ b * a = c * a) -> b = c := by
  intro h -- introduz h como hipótese
  cases h with -- h é uma disjunção, logo verifica-se caso a caso
  | inl hl => replace hl := congrArg (λ x => a⁻¹ * x) hl -- se a esquerda for verdade
              simp [<-G.mul_assoc, G.inv_lmul, G.id_lmul] at hl
              exact hl
  | inr hr => replace hr := congrArg (λ x => x * a⁻¹) hr -- se a direita for verdade
              simp [G.mul_assoc, G.inv_rmul, G.id_rmul] at hr
              exact hr
