import tactic.basic
import tactic.linarith
import data.set.basic
import data.set.lattice
import data.real.basic
import data.set.finite
import .sets

--import topology.basic

namespace topology

open set

universes u w

-- Copied from mathlib
structure topological_space (α : Type u) :=
(is_open        : set α → Prop)
(is_open_univ   : is_open set.univ)
(is_open_inter  : ∀s t, is_open s → is_open t → is_open (s ∩ t))
(is_open_sUnion : ∀s:(set (set α)), (∀t∈s, is_open t) → is_open (⋃₀ s))

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
    have : x ∈ sᶜ := tincomp xint,
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

lemma closed_inter_of_closed (ss: set (set α)) (h: ∀ s ∈ ss, is_closed s)
    : is_closed ⋂₀ ss :=
begin
    unfold is_closed,
    rw compl_sInter,
    apply is_open_sUnion,
    intros s hs,
    simp at hs,
    rcases hs  with ⟨t, tinss, scomp ⟩,
    have : is_closed t := h t tinss,
    rw ← scomp,
    exact this,
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
        have baz' : x ∈ U := set.not_not_mem.mp baz,
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
        exact ⟨ set.not_not_mem.mp (not_mem_of_mem_diff ain),  mem_of_mem_diff ain ⟩, 
    }
end

lemma closure_closed {s : set α} : is_closed (closure s) :=
begin
    rw closure_is_intersection,
    apply closed_inter_of_closed,
    intros _ h,
    exact h.1
end

-- page 6

-- a set is open iff all its points are interior
theorem open_iff_all_int (s: set α) : is_open s ↔ ∀ x ∈ s, interior_point x s :=
begin
    split,
    {   show is_open s → ∀ x ∈ s, interior_point x s,
        intros op x hx,
        exact ⟨ s, op, hx, by refl ⟩ },
    {
        show (∀ x ∈ s, interior_point x s) → is_open s, 
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
    {
        show x ∈ interior s → ∃ t, (is_closed tᶜ ∧ t ⊆ s) ∧ x ∈ t,
        intros xint,
        rcases xint with ⟨ V, isOpen, xin, Vin⟩,
        exact ⟨ V, ⟨open_iff_closed_compl.mp isOpen, Vin⟩, xin⟩,
    },
    {
        show (∃ t, (is_closed tᶜ ∧ t ⊆ s) ∧ x ∈ t) → x ∈ interior s,
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
    {   show is_closed s → s = ⋂₀{t | is_closed t ∧ s ⊆ t},
        intros closed,
        ext,
        split,
        {
            show x ∈ s → x ∈ ⋂₀{t | is_closed t ∧ s ⊆ t},
            intros xin t tin,
            exact tin.2 xin,
        },
        {
            show x ∈ ⋂₀{t | is_closed t ∧ s ⊆ t} → x ∈ s,
            intros xin,
            simp at xin,
            exact xin s closed subset.rfl,
        },
    },
    {   show s = ⋂₀{t | is_closed t ∧ s ⊆ t} → is_closed s,
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


lemma closure_idempotent {s : set α} :
closure (closure s) = closure s :=
    (closed_iff_equal_to_closure.mp closure_closed).symm


omit topo

structure metric_space (α : Type u) :=
(metric : α → α → ℝ)
(positive : ∀ x y, x ≠ y → metric x y > 0)
(zero_self : ∀ x, metric x x = 0)
(symm : ∀ x y, metric x y = metric y x)
(triangle : ∀ x y z, metric x z ≤ metric x y + metric y z)

attribute [class] metric_space

variable [ms : metric_space α]
include ms

def εBall (x : α) (ε : ℝ) := { y : α | ms.metric x y < ε}

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

instance metric_topology : topological_space α :=
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

lemma εBall_open {ε : ℝ} (x : α) (h: ε > 0) : is_open (εBall x ε) :=
begin
    intros y xinball,

    use ε - ms.metric x y, 
    split,
    {
        show 0 < ε - ms.metric x y,
        exact sub_pos.mpr xinball,
    },
    {
        show εBall y (ε - ms.metric x y) ⊆ εBall x ε,
        intros z zin,
        exact
          calc ms.metric x z ≤ ms.metric x y + ms.metric y z : by apply ms.triangle
          ... <  ms.metric x y + (ε - ms.metric x y) : add_lt_add_left zin _
          ... = ε : by {ring},
    }
end

lemma center_in_ball {ε : ℝ} (x : α) (h: ε > 0) : x ∈ εBall x ε :=
begin
    change ms.metric x x < ε,
    rw ms.zero_self,
    exact h
end

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


def disjoint_union (s: topological_space α) (t: topological_space β) :
    topological_space (α ⊕ β) :=
{
    is_open := λ s:set (α ⊕ β), ∃ (u: set α) (v: set β), (u ⊕ v) = s, 

    is_open_univ := sorry,
    is_open_inter := sorry,
    is_open_sUnion := sorry,
}

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

noncomputable instance : metric_space ℝ := reals_metric_space

--noncomputable def reals_metric_topology : topological_space ℝ :=  metric_topology 
--noncomputable instance : topological_space ℝ := reals_metric_topology

structure basis [topological_space α]
(sets : set (set α))
(sets_open : ∀ s ∈ sets, is_open s)
(union_of_open : ∀ s, is_open s → ∃ ss ⊆ sets, ⋃₀ ss = s)


structure is_subbasis (ts: topological_space α) :=
(sets : set (set α))
(sets_open : ∀ s ∈ sets, ts.is_open s)
-- infinite union of finite intersections of sets in sets
(union_of_fin_inter :
    ∀ (s:set α), is_open s →
        ∃ sss : set (set (set α)),
            (∀ (ss ∈ sss), set.finite ss ∧ ∀ s ∈ ss, s ∈ sets) ∧
            ⋃₀ ((λ i, ⋂₀ i) '' sss) = s )


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

        sorry

    },

    is_open_sUnion := sorry
}

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

-- page 13

example
 (f : ℝ → ℝ)
 (cont: continuous f) :
    ∀ (x0 : ℝ) (ε > 0), ∃ δ > 0, ∀ (x : ℝ), abs(x - x0) < δ → abs (f x - f x0)  < ε :=
begin
    intros x0 e epos,
    have open_x := cont (εBall (f x0) e) (εBall_open (f x0) epos),

    have : ∃ (ε > 0),  εBall x0 ε ⊆ f ⁻¹' εBall (f x0) e :=
        open_x x0 (center_in_ball (f x0) epos),

    rcases this with ⟨ δ, δpos, ball_in ⟩,
    use δ,
    split,
    {exact δpos,},
    {
        intros x xin,
        have : x ∈ @εBall ℝ reals_metric_space x0 δ := by {rw abs_sub at xin, exact xin},
        have : x ∈ f ⁻¹' @εBall ℝ reals_metric_space (f x0) e := ball_in this,
        simp at this,
        rw ← neg_sub,
        rw abs_neg,
        exact this,
    }
end

class homeomorphism (f : α → β) :=
(inv : β → α)
(left_inv : inv ∘ f = id)
(right_inv : f ∘ inv = id)
(cont: continuous f)
(invcont: continuous inv)

def has_homeomorphism (f : α → β) := nonempty (homeomorphism f)

@[simp]
lemma left_inverse_hom (f : α → β) (h: homeomorphism f) :
    function.left_inverse h.inv f :=
begin
    intros x,
    change (h.inv ∘ f) x = x,
    rw h.left_inv,
    refl
end

@[simp]
lemma right_inverse_hom (f : α → β) (h: homeomorphism f) :
    function.right_inverse h.inv f :=
begin
    intros x,
    change (f ∘ h.inv) x = x,
    rw h.right_inv,
    refl
end

lemma homeo_of_open_iff_to_open (f : α → β) (b: function.bijective f) :
    has_homeomorphism f ↔ (∀ U, is_open U ↔ is_open (f '' U)) :=
begin
    split,
    {
        intros has,
        have h := has.some,
        intros U,
        split,
        {
            show is_open U → is_open (f '' U),
            intro Uopen,

            have : f '' U = (h.inv)⁻¹' U, {
                rw image_eq_preimage_of_inverse,
                simp, simp,
            },

            have bar := h.invcont,
            have baz := bar U Uopen,
            rw ← this at baz,
            exact baz,
        },
        {
            show is_open (f '' U) → is_open U,
            intros imgopen,

            have : U = f⁻¹' (f '' U), {
                rw preimage_image_eq,
                apply function.left_inverse.injective,
                exact left_inverse_hom f h,
            },

            have bar := h.cont,
            have baz := bar (f '' U) imgopen,
            rw ← this at baz,
            exact baz,
        }
    },
    {
        intros h,
        exact nonempty.intro {
            inv := sorry,
            left_inv := sorry,
            right_inv := sorry,
            cont := sorry,
            invcont := sorry,
        }, 
    }
end
end continuity

section caracterization

def connected (ts: topological_space α) :=
    ¬ ∃ U V, ts.is_open U ∧ ts.is_open V ∧ U ∩ V = ∅ ∧ U.nonempty ∧ V.nonempty

include topo

lemma connected_no_open_close (h: connected topo) :
    ∀ (s: set α), is_open s →  is_closed s → s = univ ∨ s = ∅ :=
begin
    intros s opens closeds,
    have h1 : is_open sᶜ := closeds,
    have h2 : s ∩ sᶜ = ∅ := inter_compl_self _,
    have := forall_not_of_not_exists h s ,
    push_neg at this,

    have : s.nonempty → ¬ sᶜ.nonempty := this sᶜ opens h1 h2, 
    rw not_nonempty_iff_eq_empty at this,
    rw compl_empty_iff at this,
    by_cases H : s.nonempty,
    {exact or.inl (this H)},
    {exact or.inr (not_nonempty_iff_eq_empty.mp H)}
end


end caracterization

end topology