import TypeTheory.Stlc
import Mathlib.Data.Finmap

open STLC Finmap

namespace STLC

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
    cases h with
    | T_app _ s1 s2 T1 T2 h1 h2 =>
      specialize ih1 (T1 → T) h1
      specialize ih2 T1 h2
      rcases ih1 with (hl | hr)
      · let s1abs := canonical_forms_fun s1 T1 T h1 hl
        rcases s1abs with ⟨x, u, rfl⟩
        right
        rcases ih2 with (h2l | ⟨s2', hs2'⟩)
        · use u [x := s2]
          apply step.ST_AppAbs
          exact h2l
        · use λ x: T1, u ↠ s2'
          apply step.ST_App2
          · exact value.v_abs x T1 u
          assumption
      · right
        rcases hr with ⟨s1', hs1'⟩
        use s1' ↠ s2
        apply step.ST_App1
        · exact hs1'
  | tm_abs x T t _ => exact fun T1 _ => Or.inl (value.v_abs x T t)
  | tm_true => exact fun T _ => Or.inl value.v_true
  | tm_false => exact fun T _ => Or.inl value.v_false
  | tm_if x t1 t2 ihx _ _ =>
    intro T h
    right
    cases h with
    | T_If _ x t1 t2 T hx ht1 ht2 =>
      let hif := ihx BOOL hx
      rcases hif with (hvaluex | ⟨x', hx'⟩)
      · let xbool := canonical_forms_bool x hx hvaluex
        rcases xbool with (xv | xv) <;> rw [xv]
        · use t1
          apply step.ST_IfTrue
        · use t2
          apply step.ST_IfFalse
      · use <{If x' Then t1 Else t2}>
        apply step.ST_If
        exact hx'

open partialmap

count_heartbeats in
theorem weakening : ∀ Γ Γ' t T,
    includedin Γ Γ' → (Γ ⊢ t : T) → (Γ' ⊢ t : T) := by
  intro Γ Γ' t T h ht
  induction ht generalizing Γ' with
  | T_Var Γ'' x T1 h1 =>
    apply has_type.T_Var
    exact h.property h1
  | T_Abs Γ'' x T1 T2 t2 _ a_ih =>
    apply has_type.T_Abs
    let insertincluded := includedin_insert h x T1
    exact (a_ih _ insertincluded)
  | T_app Γ'' t1 t2 T1 T2 _ _ a_iht1 a_iht2 =>
    refine has_type.T_app ?_ t1 t2 T1 T2 ?_1 ?_2
    · exact a_iht1 _ h
    · exact a_iht2 _ h
  | T_True => exact has_type.T_True _
  | T_False => exact has_type.T_False _
  | T_If Γ'' x t2 t3 T _ _ _ a_ihx a_iht2 a_iht3 =>
    refine has_type.T_If Γ' x t2 t3 T ?_ ?_ ?_3
    · exact a_ihx _ h
    · exact a_iht2 _ h
    · exact a_iht3 _ h

theorem weakening_empty : ∀ Γ t T,
    (∅ ⊢ t : T) → (Γ ⊢ t : T) := by
  intro Γ t T ht
  exact weakening _ _ _ _ (includedin_empty _) ht

theorem substitution_preserves_typing :
  ∀ Γ x U t v T,
    (Γ.insert x U ⊢ t : T) →
    (∅ ⊢ v : U) →
    (Γ ⊢ t [x := v] : T) := by
  sorry

theorem preservation :
  ∀ t t' T,
    (∅ ⊢ t : T) →
    t ->- t' →
    (∅ ⊢ t' : T) := by
  sorry

theorem preservation' :
  ∀ t t' T,
    (∅ ⊢ t : T) →
    t ->* t' →
    (∅ ⊢ t' : T) := by
  intro t t' T ht htt'
  induction htt' generalizing T with
  | multi_refl t => exact ht
  | multi_step x y z rxy syz a_ih =>
    apply a_ih
    exact preservation x y T ht rxy

  sorry

theorem not_subject_expansion :
  ∃ t t' T,
    t ->- t' ∧ (∅ ⊢ t' : T) ∧ ¬ (∅ ⊢ t : T) := by
  sorry

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
  sorry

class inductive appears_free_in (x : String) : tm → Prop :=
  | afi_var : appears_free_in x <{x}>
  | afi_app1 : ∀ t1 t2, appears_free_in x t1 → appears_free_in x <{t1 ↠ t2}>
  | afi_app2 : ∀ t1 t2, appears_free_in x t2 → appears_free_in x <{t1 ↠ t2}>
  | afi_abs : ∀ y T t, x ≠ y → appears_free_in x t → appears_free_in x <{λ y : T, t}>
  | afi_if1 : ∀ t1 t2 t3, appears_free_in x t1 → appears_free_in x <{If t1 Then t2 Else t3}>
  | afi_if2 : ∀ t1 t2 t3, appears_free_in x t2 → appears_free_in x <{If t1 Then t2 Else t3}>
  | afi_if3 : ∀ t1 t2 t3, appears_free_in x t3 → appears_free_in x <{If t1 Then t2 Else t3}>

def closed (t : tm) : Prop :=
  ∀ x, ¬ appears_free_in x t

theorem free_in_context :
  ∀ x t T Γ,
    (appears_free_in x t) → (Γ ⊢ t : T) → (∃ U, Γ.lookup x = some U) := by
  sorry

theorem typable_empty_closed :
  ∀ t T,
    (∅ ⊢ t : T) → closed t := by
  sorry

theorem context_invariance :
  ∀ Γ Γ' t T,
    (Γ ⊢ t : T) → (∀ x, appears_free_in x t → Γ.lookup x = Γ'.lookup x) → (Γ' ⊢ t : T) := by
  sorry

end STLC

#check Finmap
