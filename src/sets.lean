import tactic.basic
import data.set.basic

namespace set

variables {α : Type*} {β : Type*}

lemma union_of_sub (s: set α) (f : α → set α) (hf : ∀ x ∈ s, x ∈ f x ∧ f x ⊆ s) :
     s = ⋃₀ (f '' s) :=
begin
    ext,
    split,
    simp at *,
    {
        intros xs,
        exact ⟨ x, xs, (hf x xs).1 ⟩ 
    },
    {
        simp,
        intros x' xs' xfx',
        exact (hf x' xs').2 xfx',
    }
end

end set