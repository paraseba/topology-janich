import tactic.basic
import tactic.linarith
import data.set.basic
import data.set.lattice
import data.real.basic

--import topology.basic

namespace topology

open set

universes u

structure topological_space (α : Type u) :=
(is_open        : set α → Prop)
(is_open_univ   : is_open set.univ)
(is_open_inter  : ∀s t, is_open s → is_open t → is_open (s ∩ t))
(is_open_sUnion : ∀s, (∀t∈s, is_open t) → is_open (⋃₀ s))

attribute [class] topological_space

variables {α : Type*} {β : Type*}
variables [topo: topological_space α]

include topo

def is_open (s : set α) : Prop := topological_space.is_open topo s
def is_closed (s : set α) : Prop := is_open sᶜ

lemma is_open_sUnion {s : set (set α)} (h : ∀t ∈ s, is_open t) : is_open (⋃₀ s) :=
topological_space.is_open_sUnion topo s h


-- page 5
def neighborhood (s : set α) (x : α) := ∃ V, is_open V ∧ (x ∈ V) ∧ (V ⊆ s)

def interior_point (x : α) (s : set α) := neighborhood s x 
def exterior_point (x : α) (s : set α) := neighborhood sᶜ x

def interior (s : set α) := {x | interior_point x s}
def closure (s : set α) := {x | ¬ exterior_point x s}


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

-- a set is open iff all its points are interior
theorem open_iff_all_int (s: set α) : is_open s ↔ ∀ x ∈ s, interior_point x s :=
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

theorem interior_is_union_of_open (s : set α) :
    interior s = ⋃₀ {s' | is_open s' ∧ s' ⊆ s} :=
begin
    ext,
    simp,
    split,
    {   intros xint,
        rcases xint with ⟨ V, isOpen, xin, Vin⟩,
        exact ⟨ V, ⟨isOpen, Vin⟩, xin⟩,
    },

    {
        simp,
        intros s' isOpen sin' xin,
        exact ⟨ s', isOpen, xin, sin' ⟩,
    }
end

lemma interior_is_open (s : set α) : is_open (interior s) :=
begin
    rw interior_is_union_of_open _,
    apply is_open_sUnion,
    simp,
    intros t topen _,
    exact topen
end


lemma mem_of_not_mem_compl {x : α } {s: set α}: x ∉ sᶜ → x ∈ s := 
begin
    exact set.not_not_mem.mp,
end 

lemma closed_inter_of_closed (ss: set (set α)) (h: ∀ s ∈ ss, is_closed s)
    : is_closed ⋂₀ ss :=
begin
    unfold is_closed,
    rw compl_sInter,
    apply is_open_sUnion,
    intros s hs,
    simp at hs,
    rcases hs  with ⟨t, tinss, scomp ⟩,
    have tis_closed : is_closed t := h t tinss,
    rw ← scomp,
    exact tis_closed,
end

@[simp]
lemma open_iff_closed_compl {s: set α} : is_open s ↔ is_closed sᶜ :=
begin
    unfold is_closed,
    rw compl_compl,
end

theorem closure_is_intersection (s : set α) :
    closure s = ⋂₀ {t | is_closed t ∧ s ⊆ t} :=
begin
    ext,
    split,
    {
        intros xincl,
        unfold closure at xincl,
        unfold exterior_point at xincl,
        unfold neighborhood at xincl,
        simp at xincl,

        let U := ⋂₀ {t | is_closed t ∧ s ⊆ t},
        change x ∈ U,

        have closed_u : is_closed U, {
            apply closed_inter_of_closed,
            intros t tinU, 
            rw mem_set_of_eq at tinU,
            exact tinU.1
        },

        have inSC : Uᶜ ⊆ sᶜ, {
            rw compl_subset_compl,
            intros a ha,
            rw mem_sInter,
            intros t tinU,
            rw mem_set_of_eq at tinU,
            exact tinU.2 ha,
        },

        rw ← compl_compl U at closed_u,
        have baz := mt (xincl Uᶜ closed_u) (not_not.mpr inSC),
        have baz' : x ∈ U := mem_of_not_mem_compl baz,
        exact baz',
    },
    {
        simp,
        intros H,
        unfold closure, 
        unfold exterior_point,
        unfold neighborhood,
        simp,
        intros t t_open x_in_t, 
        rw not_subset,
        have := mt(H tᶜ t_open) (not_not.mpr x_in_t),

        cases (nonempty_of_not_subset this) with a ain,
        use a,
        simp,
        exact ⟨ mem_of_not_mem_compl (not_mem_of_mem_diff ain),  mem_of_mem_diff ain ⟩, 
    }
end

lemma closed_iff_equal_to_closure (s : set α) : 
    is_closed s ↔ s = closure s :=
begin
    rw closure_is_intersection,
    split,
    {   intros closed,
        ext,
        split,
        {
            intros xin t tin,
            exact tin.2 xin,
        },
        {
            intros xin,
            simp at xin,
            exact xin s closed subset.rfl,
        },
    },
    {
        intros sint,
        rw sint,
        apply closed_inter_of_closed,
        intros t tin,
        exact tin.1,
    }

end

lemma open_iff_compl_eq_closure (s : set α) :
    is_open s ↔ sᶜ = closure sᶜ :=
begin
    rw ← closed_iff_equal_to_closure,
    simp,
end

omit topo

structure metric_space (α : Type u) :=
(metric : α → α → ℝ)
(positive : ∀ x y, x ≠ y → metric x y > 0)
(zero_self : ∀ x, metric x x = 0)
(symm : ∀ x y, metric x y = metric y x)
(triangle : ∀ x y z, metric x z ≤ metric x y + metric y z)

attribute [class] metric_space

variable [ms : metric_space α]

def εBall (x : α) (ε : ℝ) := { y : α | ms.metric x y < ε}

include ms

lemma smaller_ball_subset {x : α} (a b : ℝ) (h : a ≤ b)
    : εBall x a ⊆  εBall x b :=
begin
    intros y yina,
    unfold εBall,
    have H : ms.metric x y < b :=
        calc ms.metric x y < a : yina
            ... ≤ b : h,
    simp [H],
end

def metric_topology (ms : metric_space α) : topological_space α :=
{
    is_open := λ s, ∀ x ∈ s, ∃ ε > 0, εBall x ε ⊆ s,
    is_open_univ := λ _ _, ⟨ 1, by linarith, by simp ⟩,

    is_open_inter := by {
        intros s t sball tball x xin,
        rcases sball x xin.1 with ⟨εs,εspos,hεs⟩, 
        rcases tball x xin.2 with ⟨εt,εtpos,hεt⟩, 
        use min εs εt,
        split,

        {exact lt_min εspos εtpos,},

        {
            apply subset_inter,
            {
                have : εBall x (min εs εt) ⊆ εBall x εs, {
                    apply smaller_ball_subset,
                    apply min_le_left
                },
                exact subset.trans this hεs,
            },
            {
                have : εBall x (min εs εt) ⊆ εBall x εt, {
                    apply smaller_ball_subset,
                    apply min_le_right
                },
                exact subset.trans this hεt,
            }
        }
    },

    is_open_sUnion := by {
        intros ss h x xin,
        rw mem_sUnion at xin,
        rcases xin with ⟨ t, tinss, xint ⟩,
        rcases h t tinss x xint with ⟨ ε, εpos, ball_in_t ⟩, 
        exact ⟨ ε, εpos, subset_sUnion_of_subset ss t ball_in_t tinss ⟩
    }
}


end topology