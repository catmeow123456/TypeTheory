-- https://softwarefoundations.cis.upenn.edu/plf-current/StlcProp.html

import TypeTheory.Stlc
import Mathlib.Data.Finmap

open STLC Finmap

namespace STLC

section destruct_has_type

theorem var_type_in_context: ∀ {Γ x T},
    (Γ ⊢ tm.tm_var x : T) → Γ.lookup x = some T :=
  fun hx => by cases hx with | T_Var _ _ _ h => exact h

theorem app_type_in_context: ∀ {Γ t1 t2 T2},
    (Γ ⊢ tm.tm_app t1 t2 : T2) →
      ∃ T1, (Γ ⊢ t1 : T1 → T2) ∧  (Γ ⊢ t2 : T1) :=
  fun happ => by cases happ with | T_app _ _ _ _ _ h1 h2 => exact ⟨_, h1, h2⟩

theorem if_type_in_context: ∀ {Γ t1 t2 t3 T},
    (Γ ⊢ tm.tm_if t1 t2 t3 : T) →
      (Γ ⊢ t1 : BOOL) ∧ (Γ ⊢ t2 : T) ∧ (Γ ⊢ t3 : T) :=
  fun hif => by cases hif with | T_If _ _ _ _ _ h1 h2 h3 => exact ⟨h1, h2, h3⟩

theorem abs_type_in_context: ∀ {Γ x Tx t T},
    (Γ ⊢ tm.tm_abs x Tx t : T) →
      (∃ Tt, T = (Tx → Tt) ∧ (Γ.insert x Tx ⊢ t : Tt)) :=
  fun habs => by cases habs with | T_Abs _ _ _ Tt _ h => use Tt

theorem true_type_in_context: ∀ {Γ T}, (Γ ⊢ tm.tm_true : T) → T = BOOL :=
  fun h => by cases h with | T_True => rfl

theorem false_type_in_context: ∀ {Γ T}, (Γ ⊢ tm.tm_false : T) → T = BOOL :=
  fun h => by cases h with | T_False => rfl

end destruct_has_type

#check has_type.T_Var
#check has_type.T_app
theorem canonical_forms_bool :
    ∀ t, (∅ ⊢ t : BOOL) → value t → (t = <{TRUE}>) ∨ (t = <{FALSE}>) := by
  intro t ht vt
  cases vt with
  | v_true => left; rfl
  | v_false => right; rfl
  | v_abs x T t' => cases ht

theorem canonical_forms_fun :
    ∀ t T1 T2, (∅ ⊢ t : T1 → T2) → value t →
      ∃ x u, t = <{λ x : T1, u}> := by
  intro t T1 T2 h vt
  cases vt with
  | v_true => cases h
  | v_false => cases h
  | v_abs x _ t' =>
    use x, t'
    cases h; rfl

#check has_type.T_app
#check step.ST_AppAbs

theorem progress:
    ∀ t T, (∅ ⊢ t : T) → value t ∨ ∃ t', t ->- t' := by
  intro t
  induction t with
  | tm_var s => intro T h; contradiction
  | tm_app s1 s2 ih1 ih2 =>
    intro T h
    let ⟨T1, h1, h2⟩ := app_type_in_context h
    specialize ih1 (T1 → T) h1
    specialize ih2 T1 h2
    rcases ih1 with (hl | hr)
    · let s1abs := canonical_forms_fun s1 T1 T h1 hl
      rcases s1abs with ⟨x, u, rfl⟩
      right
      rcases ih2 with (h2l | ⟨s2', hs2'⟩)
      · exact ⟨u [x:=s2], step.ST_AppAbs x T1 u s2 h2l⟩
      · use λ x: T1, u ↠ s2'
        apply step.ST_App2
        · exact value.v_abs x T1 u
        exact hs2'
    · right
      rcases hr with ⟨s1', hs1'⟩
      use s1' ↠ s2
      apply step.ST_App1
      exact hs1'
  | tm_abs x T t _ => exact fun T1 _ => Or.inl (value.v_abs x T t)
  | tm_true => exact fun T _ => Or.inl value.v_true
  | tm_false => exact fun T _ => Or.inl value.v_false
  | tm_if x t1 t2 ihx _ _ =>
    intro T h
    right
    let ⟨hx, _, _⟩ := if_type_in_context h
    let hif := ihx BOOL hx
    rcases hif with (hvaluex | ⟨x', hx'⟩)
    · let xbool := canonical_forms_bool x hx hvaluex
      rcases xbool with (rfl | rfl)
      · exact ⟨t1, step.ST_IfTrue t1 t2⟩
      · exact ⟨t2, step.ST_IfFalse t1 t2⟩
    · use <{If x' Then t1 Else t2}>
      exact step.ST_If x x' t1 t2 hx'

open partialmap

count_heartbeats in
theorem weakening : ∀ {Γ Γ' t T},
    includedin Γ Γ' → (Γ ⊢ t : T) → (Γ' ⊢ t : T) := by
  intro Γ Γ' t T h ht
  induction ht generalizing Γ' with
  | T_Var Γ'' x T1 h1 =>
    apply has_type.T_Var
    exact h.property h1
  | T_Abs Γ'' x T1 T2 t2 _ a_ih =>
    apply has_type.T_Abs
    let insertincluded := includedin_insert h x T1
    exact (a_ih insertincluded)
  | T_app Γ'' t1 t2 T1 T2 _ _ a_iht1 a_iht2 =>
    refine has_type.T_app ?_ t1 t2 T1 T2 ?_1 ?_2
    · exact a_iht1 h
    · exact a_iht2 h
  | T_True => exact has_type.T_True _
  | T_False => exact has_type.T_False _
  | T_If Γ'' x t2 t3 T _ _ _ a_ihx a_iht2 a_iht3 =>
    refine has_type.T_If Γ' x t2 t3 T ?_ ?_ ?_3
    · exact a_ihx h
    · exact a_iht2 h
    · exact a_iht3 h

theorem weakening_empty : ∀ {Γ t T},
    (∅ ⊢ t : T) → (Γ ⊢ t : T) := by
  intro Γ t T ht
  exact weakening (includedin_empty _) ht

theorem substitution_preserves_typing :
  ∀ {Γ x U t v T},
    (Γ.insert x U ⊢ t : T) →
    (∅ ⊢ v : U) →
    (Γ ⊢ t [x := v] : T) := by
  intro Γ x U t v T
  intro ht
  intro hv
  induction t generalizing Γ T with
  | tm_var y =>
    dsimp [subst]
    by_cases h: x=y
    · subst_vars; rw [if_pos rfl]
      apply var_type_in_context at ht
      rw [lookup_insert] at ht
      apply weakening_empty
      injection ht; subst_vars; exact hv
    · rw [if_neg h]
      apply has_type.T_Var
      apply var_type_in_context at ht
      rw [lookup_insert_of_ne Γ (Ne.symm h)] at ht
      exact ht
  | tm_app t1 t2 ih1 ih2 =>
    dsimp [subst]
    let ⟨T1, ht1, ht2⟩ := app_type_in_context ht
    apply has_type.T_app
    · exact ih1 ht1
    · exact ih2 ht2
  | tm_abs y U' t' ih =>
    dsimp [subst]
    rcases abs_type_in_context ht with ⟨Tt', rfl, ht'⟩
    by_cases h: x=y
    · subst_vars; rw [if_pos rfl]
      apply has_type.T_Abs
      rw [insert_insert] at ht'
      exact ht'
    · rw [if_neg h]
      apply has_type.T_Abs
      apply ih
      rw [insert_insert_of_ne _ (Ne.symm h)]
      exact ht'
  | tm_true =>
    exact (true_type_in_context ht) ▸ has_type.T_True _
  | tm_false =>
    exact (false_type_in_context ht) ▸ has_type.T_False _
  | tm_if y t1 t2 ih1 ih2 ih3 =>
    dsimp [subst]
    rcases if_type_in_context ht with ⟨ht1, ht2, ht3⟩
    apply has_type.T_If _ _ _ _ _ (ih1 ht1) (ih2 ht2) (ih3 ht3)

theorem preservation :
  ∀ {t t' T},
    (∅ ⊢ t : T) →
    t ->- t' →
    (∅ ⊢ t' : T) := by
  intro t t' T ht hr
  induction hr generalizing T with
  | ST_AppAbs x T2 t1 v2 _ =>
    rcases app_type_in_context ht with ⟨T1, ht1, ht2⟩
    rcases abs_type_in_context ht1 with ⟨Tt, hTt, ht1'⟩
    injection hTt; subst_vars
    exact substitution_preserves_typing ht1' ht2
  | ST_App1 t1 t1' t2 _ a_ih =>
    rcases app_type_in_context ht with ⟨T1, ht1, ht2⟩
    exact has_type.T_app _ _ _ _ _ (a_ih ht1) ht2
  | ST_App2 v1 t2 t2' _ _ a_ih =>
    rcases app_type_in_context ht with ⟨T1, ht1, ht2⟩
    exact has_type.T_app _ _ _ _ _ ht1 (a_ih ht2)
  | ST_IfTrue t1 t2 => exact (if_type_in_context ht).2.1
  | ST_IfFalse t1 t2 => exact (if_type_in_context ht).2.2
  | ST_If t1 t1' t2 t3 _ a_ih =>
    rcases if_type_in_context ht with ⟨ht1, ht2, ht3⟩
    exact has_type.T_If _ _ _ _ _ (a_ih ht1) ht2 ht3

theorem preservation' :
  ∀ t t' T,
    (∅ ⊢ t : T) →
    t ->* t' →
    (∅ ⊢ t' : T) := by
  intro t t' T ht htt'
  induction htt' generalizing T with
  | multi_refl t => exact ht
  | multi_step x y _ rxy _ a_ih =>
    apply a_ih
    exact preservation ht rxy

theorem not_subject_expansion :
  ∃ t t' T,
    t ->- t' ∧ (∅ ⊢ t' : T) ∧ ¬ (∅ ⊢ t : T) := by
  let t := <{λ x: (BOOL → BOOL), x ↠ TRUE}>
  use t, <{TRUE}>, BOOL
  constructor
  · apply step.ST_AppAbs
    apply value.v_true
  constructor
  · apply has_type.T_True
  intro h
  apply app_type_in_context at h
  rcases h with ⟨T1, ht1, ht2⟩
  apply abs_type_in_context at ht1
  rcases ht1 with ⟨Tt, hTt, ht1'⟩
  injection hTt; subst_vars
  cases ht2

def stuck (t : tm) : Prop :=
  (normal_form step) t ∧ ¬ value t

theorem type_soundness :
  ∀ t t' T,
    (∅ ⊢ t : T) → t ->* t' → ¬ stuck t' := by
  intro t t' T ht multi
  let ht' : (∅ ⊢ t' : T) := preservation' t t' T ht multi
  intro ⟨h1, h2⟩
  rcases (progress t' T ht') with (hl | hr)
  · exact h2 hl
  · exact h1 hr

theorem unique_types :
  ∀ Γ e T T',
    (Γ ⊢ e : T) → (Γ ⊢ e : T') → T = T' := by
  intro Γ e T T'
  intro hT hT'
  induction e generalizing T T' Γ with
  | tm_var x =>
    apply var_type_in_context at hT
    apply var_type_in_context at hT'
    rw [hT] at hT'
    exact Option.noConfusion hT' id
  | tm_app t1 t2 a_ih1 _a_ih2 =>
    rcases app_type_in_context hT with ⟨_, hT1, _⟩
    rcases app_type_in_context hT' with ⟨_, hT1', _⟩
    specialize a_ih1 _ _ _ hT1 hT1'
    injection a_ih1
  | tm_abs x T1 t2 a_ih =>
    rcases abs_type_in_context hT with ⟨_, rfl, hT1⟩
    rcases abs_type_in_context hT' with ⟨_, rfl, hT1'⟩
    specialize a_ih _ _ _ hT1 hT1'
    rw [a_ih]
  | tm_true =>
    apply true_type_in_context at hT
    apply true_type_in_context at hT'
    rw [hT, hT']
  | tm_false =>
    apply false_type_in_context at hT
    apply false_type_in_context at hT'
    rw [hT, hT']
  | tm_if t1 t2 t3 _a_ih1 _a_ih2 a_ih3 =>
    rcases if_type_in_context hT with ⟨_, _, hT3⟩
    rcases if_type_in_context hT' with ⟨_, _, hT3'⟩
    exact a_ih3 _ _ _ hT3 hT3'

inductive appears_free_in (x : String) : tm → Prop :=
  | afi_var : appears_free_in x <{x}>
  | afi_app1 : ∀ t1 t2, appears_free_in x t1 → appears_free_in x <{t1 ↠ t2}>
  | afi_app2 : ∀ t1 t2, appears_free_in x t2 → appears_free_in x <{t1 ↠ t2}>
  | afi_abs : ∀ y T t, x ≠ y → appears_free_in x t → appears_free_in x <{λ y : T, t}>
  | afi_if1 : ∀ t1 t2 t3, appears_free_in x t1 → appears_free_in x <{If t1 Then t2 Else t3}>
  | afi_if2 : ∀ t1 t2 t3, appears_free_in x t2 → appears_free_in x <{If t1 Then t2 Else t3}>
  | afi_if3 : ∀ t1 t2 t3, appears_free_in x t3 → appears_free_in x <{If t1 Then t2 Else t3}>

def closed (t : tm) : Prop := ∀ x, ¬ appears_free_in x t

theorem free_in_context :
  ∀ {x t T Γ},
    (appears_free_in x t) → (Γ ⊢ t : T) → (∃ U, Γ.lookup x = some U) := by
  intro x t T Γ
  intro h ht
  induction h generalizing Γ T with
  | afi_var => apply var_type_in_context at ht; use T
  | afi_app1 t1 t2 _a a_ih =>
    rcases app_type_in_context ht with ⟨T1, ht1, _ht2⟩
    exact a_ih ht1
  | afi_app2 t1 t2 _a a_ih =>
    rcases app_type_in_context ht with ⟨T1, _ht1, ht2⟩
    exact a_ih ht2
  | afi_abs y Ty t h _h' a_ih =>
    rcases abs_type_in_context ht with ⟨Tt, _hTt, ht'⟩
    specialize a_ih ht'
    exact (lookup_insert_of_ne _ h) ▸ a_ih
  | afi_if1 t1 t2 t3 _a a_ih =>
    rcases if_type_in_context ht with ⟨ht1, _ht2, _ht3⟩
    exact a_ih ht1
  | afi_if2 t1 t2 t3 _a a_ih =>
    rcases if_type_in_context ht with ⟨_ht1, ht2, _ht3⟩
    exact a_ih ht2
  | afi_if3 t1 t2 t3 _a a_ih =>
    rcases if_type_in_context ht with ⟨_ht1, _ht2, ht3⟩
    exact a_ih ht3

theorem typable_empty_closed :
  ∀ t T,
    (∅ ⊢ t : T) → closed t := by
  intro t T ht
  intro x h
  let ⟨u, hu⟩ := free_in_context h ht
  exact Option.noConfusion hu

open appears_free_in

theorem context_invariance :
  ∀ {Γ Γ' t T},
    (Γ ⊢ t : T) → (∀ x, appears_free_in x t → Γ.lookup x = Γ'.lookup x) → (Γ' ⊢ t : T) := by
  intro Γ Γ' t T ht h
  induction t generalizing Γ Γ' T with
  | tm_var x =>
    apply var_type_in_context at ht
    apply has_type.T_Var
    exact (h x (@afi_var x)) ▸ ht
  | tm_app t1 t2 a_ih1 a_ih2 =>
    rcases app_type_in_context ht with ⟨T1, ht1, ht2⟩
    have sg1 : Γ' ⊢ t1 : T1 → T :=
      a_ih1 ht1 fun x hafi => h x (afi_app1 t1 t2 hafi)
    have sg2 : Γ' ⊢ t2 : T1 :=
      a_ih2 ht2 fun x hafi => h x (afi_app2 t1 t2 hafi)
    exact has_type.T_app _ _ _ _ _ sg1 sg2
  | tm_abs x Tx t a_ih =>
    rcases abs_type_in_context ht with ⟨Tt, rfl, ht'⟩
    have sg1 : Finmap.insert x Tx Γ' ⊢ t : Tt := a_ih ht' fun y hafi => by
      by_cases hxy : x = y
      · subst_vars
        repeat rw [lookup_insert]
      · repeat rw [lookup_insert_of_ne _ (Ne.symm hxy)]
        exact h y (afi_abs x Tx t (Ne.symm hxy) hafi)
    exact has_type.T_Abs Γ' x Tx Tt t sg1
  | tm_true => exact (true_type_in_context ht) ▸ has_type.T_True _
  | tm_false => exact (false_type_in_context ht) ▸ has_type.T_False _
  | tm_if t1 t2 t3 a_ih1 a_ih2 a_ih3 =>
    rcases if_type_in_context ht with ⟨ht1, ht2, ht3⟩
    have sg1 : Γ' ⊢ t1 : BOOL := a_ih1 ht1 fun x hafi => h x (afi_if1 t1 t2 t3 hafi)
    have sg2 : Γ' ⊢ t2 : T := a_ih2 ht2 fun x hafi => h x (afi_if2 t1 t2 t3 hafi)
    have sg3 : Γ' ⊢ t3 : T := a_ih3 ht3 fun x hafi => h x (afi_if3 t1 t2 t3 hafi)
    exact has_type.T_If _ _ _ _ _ sg1 sg2 sg3

end STLC

namespace STLCArith

inductive ty : Type :=
  | Ty_Arrow : ty → ty → ty
  | Ty_Nat : ty

inductive tm : Type :=
  | tm_var : String → tm
  | tm_app : tm → tm → tm
  | tm_abs : String → ty → tm → tm
  | tm_const : Nat → tm
  | tm_succ : tm → tm
  | tm_pred : tm → tm
  | tm_mult : tm → tm → tm
  | tm_if₀ : tm → tm → tm → tm

-- TODO !

end STLCArith


#check Finmap
