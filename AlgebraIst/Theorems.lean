import AlgebraIst.Structures

theorem unique_id {α : Type u} {M : monoid α} (e : α) (h : ∀ a : α, e * a = a) : e = M.id := by
  have h1 := M.id_rmul e
  rw [h M.id] at h1
  exact h1.symm
