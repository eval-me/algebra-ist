import AlgebraIst.Structures

theorem ex_2_3_a {A : Type u} {G : group A} (x y z w : A) : 
  x * y * (G.inv z) * w = G.id → y = (G.inv x) * (G.inv w) * z := by
  intro h -- h turns into this x * y * (G.inv z) * w = G.id
  
  replace h := congrArg (fun a => a * G.inv w) h -- apply inverse w
  dsimp at h -- remove the fun stuff!
  rw [G.id_lmul, G.mul_assoc, G.inv_rmul, G.mul_assoc, G.id_rmul] at h -- turns x y z^-1 w w^-1 = id * w^-1 into x y z^-1 = w^-1                

  replace h := congrArg (fun a => G.inv x * a) h -- apply inverse w
  dsimp at h -- remove the fun stuff!
  rw [<-G.mul_assoc, <-G.mul_assoc, G.inv_lmul, G.id_lmul] at h 

  replace h := congrArg (fun a => a * z) h -- apply inverse z
  dsimp at h -- remove the fun stuff!
  rw [G.mul_assoc, G.inv_lmul, G.id_rmul] at h
  
  trivial -- schiappa moment

theorem ex_2_3_b_1 {A : Type u} {G : group A} (x y z : A) :
  x * y * z = G.id -> y * z * x = G.id := by
  -- lean stuff simplified
  intro h

  have h1 := congrArg (fun a => G.inv x * a) h
  simp [<-G.mul_assoc, G.id_rmul, G.inv_lmul, G.id_lmul] at h1
  
  have h2 := congrArg (fun a => a *  x) h1
  simp [G.inv_lmul] at h2
  trivial

-- This theorem says that if we assume that x * y * z = G.id -> y * x * z = G.id then x * y = y * x. As we know this only works for Abelian Groups. An example of this not working for groups is matrix multiplication {0, 0, 1, 1} * {1, 1, 0, 0} != {1, 1, 0, 0} * {0, 0, 1, 1}
theorem ex_2_4_b_2 {A : Type u} {G : group A} (x y z : A) 
  (h_rule : x * y * z = G.id → y * x * z = G.id) (h_assume : x * y * z = G.id) :
  x * y = y * x := by
  have h_result := h_rule h_assume
  have h1 := congrArg (fun a => a * G.inv z) h_result
  simp [G.mul_assoc, G.inv_rmul, G.id_lmul, G.id_rmul] at h1
  have h2 := congrArg (fun a => a * G.inv z) h_assume
  simp [G.mul_assoc, G.inv_rmul, G.id_lmul, G.id_rmul] at h2
  rw [<-h2] at h1
  exact h1.symm

