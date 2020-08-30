import topology.basic

variables {α : Type*} {β : Type*}
variables [t: topological_space α]

include t

-- page 5
def neighborhood (s : set α) (x : α) := ∃ V, t.is_open V ∧ (x ∈ V) ∧ (V ⊆ s)

def interior_point (x : α) (s : set α) := neighborhood s x 

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

-- page 6

theorem open_iff_all_int {s: set α} : t.is_open s ↔ ∀ x ∈ s, interior_point x s :=
begin
    split,
    {   intros op x hx,
        exact ⟨ s, op, hx, by refl ⟩ },
    {
        intros h,
        choose! V isOpen xinV Vins using h,
        rw union_of_sub s V (λ x xin, ⟨ xinV x xin , Vins x xin⟩),
        apply is_open_sUnion,

        intros s',
        intros hs',
        simp at hs',
        rcases hs' with ⟨ x, hx, vxs⟩ ,
        rw ← vxs,
        exact isOpen x hx,
    }
end