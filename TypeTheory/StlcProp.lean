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

count_heartbeats in
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
    ∀ t T, (∅ ⊢ t : T) → value t ∨ ∃ t', t -> t' := by
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
        · use <{u [x := s2]}>
          apply step.ST_AppAbs
          exact h2l
        · use <{<{λ x: T1, u}> ↠ s2'}>
          apply step.ST_App2
          · exact value.v_abs x T1 u
          assumption
      · right
        rcases hr with ⟨s1', hs1'⟩
        use <{s1' ↠ s2}>
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
end STLC

#check Finmap
