import tactic.basic
import tactic.linarith
import data.set.basic
import data.set.lattice
import data.real.basic
import data.set.finite

--import topology.basic

namespace topology

open set

universes u w

-- Copied from mathlib
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

lemma is_open_Union {ι : Sort w} {f : ι → set α} (h : ∀i, is_open (f i)) : is_open (⋃i, f i) :=
is_open_sUnion $ by rintro _ ⟨i, rfl⟩; exact h i

lemma is_open_bUnion {s : set β} {f : β → set α} (h : ∀i∈s, is_open (f i)) :
  is_open (⋃i∈s, f i) :=
is_open_Union $ assume i, is_open_Union $ assume hi, h i hi

@[simp]
lemma is_open_empty : topo.is_open ∅ :=
begin
    have h : is_open (⋃₀ ∅) := topo.is_open_sUnion _ (ball_empty_iff.mpr true.intro),
    rw sUnion_empty at h,
    exact h,
end

@[simp]
lemma open_iff_closed_compl {s: set α} : is_open s ↔ is_closed sᶜ :=
begin
    unfold is_closed,
    rw compl_compl,
end

lemma mem_of_not_mem_compl {x : α } {s: set α}: x ∉ sᶜ → x ∈ s := 
begin
    exact set.not_not_mem.mp,
end 


-- page 5
def neighborhood (s : set α) (x : α) := ∃ V, is_open V ∧ (x ∈ V) ∧ (V ⊆ s)

def interior_point (x : α) (s : set α) := neighborhood s x 
def exterior_point (x : α) (s : set α) := neighborhood sᶜ x

def interior (s : set α) := {x | interior_point x s}
def closure (s : set α) := {x | ¬ exterior_point x s}

lemma nhb_of_open {x:α} {s : set α} (o : is_open s) (h : x ∈ s) :
    neighborhood s x  :=
⟨ s, o, h, subset.rfl ⟩ 


lemma set_in_closure (s : set α) : s ⊆ closure s :=
begin
    intros x xin,
    unfold closure, unfold exterior_point, unfold neighborhood,
    intros ex,
    rcases ex with ⟨ _, _, xint, tincomp⟩,
    have contra : x ∈ sᶜ := tincomp xint,
    contradiction,
end

lemma closure_mono {s t : set α} (h : s ⊆ t) : closure s ⊆ closure t :=
begin
    unfold closure exterior_point neighborhood,
    simp,
    intros x hx O Oopen xinO Ointc,
    rw ← compl_subset_compl at h,
    exact (hx O Oopen xinO) (subset.trans Ointc h)
end

lemma closure_idempotent {s : set α} : closure (closure s) = closure s :=
begin
    sorry
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

lemma closure_closed {s : set α} : is_closed (closure s) :=
begin
    rw closure_is_intersection,
    apply closed_inter_of_closed,
    intros _ h,
    exact h.1
end


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
        exact ⟨ V, ⟨open_iff_closed_compl.mp isOpen, Vin⟩, xin⟩,
    },
    {
        simp,
        intros s' isOpen sin' xin,
        exact ⟨ s', open_iff_closed_compl.mpr isOpen, xin, sin' ⟩,
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


lemma closed_iff_equal_to_closure {s : set α} : 
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

omit ms

def subspace (U : set α) (ts : topological_space α) : topological_space U :=
{
    is_open := λ s, ∃ (V : set α), is_open V ∧ (V ∩ U) = subtype.val '' s,

    is_open_univ := ⟨univ, ts.is_open_univ, by {simp [univ_inter]}⟩,

    is_open_inter := by {
        rintros s t ⟨V,OV,VU⟩ ⟨W,OW,WU⟩,
        use V ∩ W,
        split,
        {exact ts.is_open_inter V W OV OW,},
        {
            rw ← image_inter,
            {
                suffices : V ∩ W ∩ U = V ∩ U ∩ W ∩ U,
                {   rw this,
                    rw VU,
                    rw inter_assoc,
                    rw WU,
                },
                show V ∩ W ∩ U = V ∩ U ∩ W ∩ U, tidy,
            },
            {exact subtype.val_injective}

        }
    },

    is_open_sUnion := by {
        intros ss h,
        choose! s op eq using h,
        use ⋃i:ss, s i,
        split,
        {
            refine is_open_Union _,
            finish,
        },
        {
            rw Union_inter,
            rw sUnion_eq_Union,
            finish [image_Union],
        }
    },
}


/-
def disjoint_union (s: topological_space α) (t: topological_space β) :
    topological_space (α ⊕ β) :=
{
    is_open := λ s:set (α ⊕ β), ∃ (u: set α) (v: set β), (u ⊕ v) = s, 

    is_open_univ := by {
        use univ,
        use univ,



    }
}
-/

structure basis [topological_space α]
(sets : set (set α))
(sets_open : ∀ s ∈ sets, is_open s)
(union_of_open : ∀ s, is_open s → ∃ ss ⊆ sets, ⋃₀ ss = s)


noncomputable def reals_metric_space : metric_space ℝ :=
{
    metric := λ x y, abs (x - y),

    positive := λ x y ne, by {
        apply abs_pos_of_ne_zero,
        exact sub_ne_zero_of_ne ne
    },

    zero_self := by simp,

    symm := λ x y, by {
        have arg : abs (x-y) = abs (y-x), by {
            calc abs (x-y) = abs (- (y - x)) : by simp
                ... = abs (y-x) : abs_neg _,
        },
        rw arg,
    },

    triangle := λ x y z, by apply abs_sub_le, 
}

structure is_subbasis (ts: topological_space α) :=
(sets : set (set α))
(sets_open : ∀ s ∈ sets, ts.is_open s)
-- infinite union of finite intersections of sets in sets
(union_of_fin_inter :
    ∀ (s:set α), is_open s →
        ∃ sss : set (set (set α)),
            (∀ (ss ∈ sss), set.finite ss ∧ ∀ s ∈ ss, s ∈ sets) ∧
            ⋃₀ ((λ i, ⋂₀ i) '' sss) = s )


section continuity
variables [ta: topological_space α] [tb: topological_space β]

include ta tb

def continuous (f: α → β) :=
    ∀ V, (is_open V) → is_open (f⁻¹' V)

lemma preimage_closed_iff_cont {f: α → β} :
    continuous f ↔ ∀ V, (is_closed V) → is_closed (f⁻¹' V) :=
begin
    split,
    {   intros fcont V Vclosed,
        rw ← compl_compl V,
        have vcomp_open : is_open Vᶜ, {unfold is_closed at Vclosed, exact Vclosed},
        rw preimage_compl,
        rw is_closed,
        rw compl_compl,
        exact fcont Vᶜ vcomp_open,
    },
    {
        intro h,
        intros V Vopen,
        rw ← compl_compl V,
        have vcomp_closed : is_closed Vᶜ, {unfold is_closed, rw compl_compl, exact Vopen},
        rw preimage_compl,
        exact h Vᶜ vcomp_closed, 
    }
end

lemma preimage_nhb_nhb_iff_cont (f : α → β) :
  continuous f ↔ ∀ (x: α) (N : set β), neighborhood N (f x) → neighborhood (f⁻¹' N) x :=
begin
    split,
    {
        intros cont x N Nfx,
        rcases Nfx with ⟨O, oOpen, fxin, OsubN⟩,
        have h1 : is_open (f⁻¹' O) := cont O oOpen,
        have h2 : (f⁻¹' O) ⊆ f⁻¹' N := preimage_mono OsubN,
        exact ⟨ f⁻¹' O, h1, fxin, h2 ⟩,
    },
    {
        intros h O Oopen,
        apply (open_iff_all_int (f⁻¹' O)).mpr,
        intros x xin,
        exact h x O (nhb_of_open Oopen xin),
    },
end 


lemma closure_preimage_sub_preimage_of_closure_iff_cont (f : α → β) :
  continuous f ↔ ∀ B, closure (f⁻¹' B) ⊆ f⁻¹' (closure B) :=
begin
    split,
    {
        intros cont B,

        have : B ⊆ closure B := set_in_closure B,
        have : f⁻¹' B ⊆ f⁻¹' (closure B) := preimage_mono this,

        have h : closure (f⁻¹' B) ⊆ closure (f⁻¹' (closure B)) :=
             closure_mono this,

        have : is_closed (f⁻¹' (closure B)) :=
             preimage_closed_iff_cont.mp cont (closure B) closure_closed,

        rw ← closed_iff_equal_to_closure.mp this at h, 
        exact h,
    },
    {
        intros h,
        apply preimage_closed_iff_cont.mpr,
        intros V Vclosed,
        have h1 : f⁻¹' V           ⊆ closure (f⁻¹' V) := set_in_closure _,
        have h2 : closure (f⁻¹' V) ⊆ f⁻¹' V, {
            have w : f⁻¹' V = f⁻¹' (closure V), {rw ← closed_iff_equal_to_closure.mp Vclosed,},
            have z := h V,
            rw w at z |-,
            exact z,
        },
        rw subset.antisymm h1 h2,
        apply closure_closed,
    }
end 


def subbasis_generated (basis : set (set α)) : topological_space α :=
{
    is_open := λ s, 
        ∃ sss : set (set (set α)),
            (∀ ss ∈ sss, set.finite ss ∧ ∀ s ∈ ss, s ∈ basis) ∧
            ⋃₀ ((λ i, ⋂₀ i) '' sss) = s,

    is_open_univ := ⟨ {{}}, by simp ⟩ ,

    is_open_inter := λ s t, by {
        intros os ot,
        choose! scomp scond sexp using os,
        choose! tcomp tcond texp using ot,
        have bar := (⋃p ∈ scomp.prod tcomp, (p : (set (set α)) × (set (set α ))).1 ∩ p.2),

        have baz := { ss | ss ∈ (scomp.prod tcomp) },

        have baz' := (λ (ss : (set (set α)) × (set (set α ))), (ss.1) ∩ (ss.2)) '' baz,

        --use baz',
        use (λ (ss : (set (set α)) × (set (set α ))), (ss.1) ∩ (ss.2)) '' { ss | ss ∈ (scomp.prod tcomp) },


        -- ((a ∩ b) ∪ (c ∩ d))  ∩  ((a' ∩ b') ∪ (c' ∩ d'))
        -- (a ∩ b) ∩ ( a' ∩ b') ∪ (a ∩ b) ∩ ( c' ∩ d')  ∪ ...
        --use scomp ∩ tcomp,

        split,
        {
            intros ss ssin,
            have caca : ss ∈ scomp, {sorry},
            exact scond ss caca,
        },
        {

            rw [← sexp, ← texp],
            simp ,



            rw ← sUnion_inter_sUnion,
            simp,
            rw sInter_image,


            ext,
            --simp at *,
            split,
            {
                intros h,
                choose! u uin uns using h,
                rw [← sexp, ← texp],
                rw image_union at uin,






            },
            {},


        }



--(∀ (ss : set (set α)), ss ∈ scomp ∪ tcomp → (ss.finite ∧ ∀ (s : set α), s ∈ ss → s ∈ basis)) ∧ 

--⋃₀((λ (i : set (set α)), ⋂₀i) '' (scomp ∪ tcomp)) = s ∩ t

    },

}

example (ss: set (set α)) (sb: is_subbasis (subbasis_generated ss)) : sb.sets = ss

def generated_has_subbasis
    {ss : set (set α)}
    (sb: is_subbasis (subbasis_generated ss)) :
    sb.sets = ss :=
begin
sorry
end


--{ u1 u2 u3}
--{ {i1 i2 i3} U {...} U {....}}

/-
metric : α → α → ℝ)
(positive : ∀ x y, x ≠ y → metric x y > 0)
(zero_self : ∀ x, metric x x = 0)
(symm : ∀ x y, metric x y = metric y x)
(triangle : ∀ x y z, metric x z ≤ metric x y + metric y z)
-/

--theorem ratio_balls_basis : basis []


end topology