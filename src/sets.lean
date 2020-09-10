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

lemma preimage_nonempty_of_inter_range {s : set β} (f : α → β) :
    (s ∩ range f).nonempty → (f⁻¹' s).nonempty :=
begin
    intros hi,
    cases hi with b hb,
    have : b ∈ range f := mem_of_mem_inter_right hb,
    cases mem_range.mp this with a ha,
    have : f a ∈ s := mem_of_eq_of_mem ha (mem_of_mem_inter_left hb),
    exact ⟨ a,  mem_preimage.mpr this⟩, 
end

lemma nonempty_inter_iff_nonempty {s t : set α} :
    (s ∩ t).nonempty → s.nonempty ∧ t.nonempty :=
begin
    intros h,
    cases h with a ha,
    have h1: a ∈ s := mem_of_mem_inter_left ha,
    have h2: a ∈ t := mem_of_mem_inter_right ha,
    exact ⟨ ⟨ a, h1 ⟩ , ⟨ a, h2 ⟩ ⟩ ,
end


lemma inter_of_subtype (s t: set α) : t ∩ s = subtype.val '' {a : ↥s | ↑a ∈ t} :=
begin
    ext,
    simp at *,
    split,
    {
        intros h,
        exact ⟨ h.2, h.1 ⟩ ,
    },
    {
        rintros ⟨yins, yint ⟩,
        exact ⟨ yint, yins ⟩, 
    }
end

end set