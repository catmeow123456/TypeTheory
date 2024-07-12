-- https://softwarefoundations.cis.upenn.edu/plf-current/Stlc.html
import Mathlib.Data.Finmap

set_option diagnostics.threshold 500

namespace STLC

section term
inductive ty : Type :=
  | Ty_Bool : ty
  | Ty_Arrow : ty → ty → ty

inductive tm : Type :=
  | tm_var : String → tm
  | tm_app : tm → tm → tm
  | tm_abs : String → ty → tm → tm
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm → tm → tm → tm

notation " <{" e "}> " => (e : tm)
infixr:50  " → " => ty.Ty_Arrow
infixl:1   " ↠ " => tm.tm_app
notation "BOOL" => ty.Ty_Bool
notation:90 " λ " x:99 ": " t:99 ", " y:99 => tm.tm_abs x t y
notation "If" x "Then" y "Else" z => tm.tm_if x y z
notation "TRUE" => tm.tm_true
notation "FALSE" => tm.tm_false

instance : Coe String tm := ⟨tm.tm_var⟩
instance : Coe Bool tm := ⟨
  fun b => match b with
  | true => tm.tm_true
  | false => tm.tm_false
⟩

example : <{true}> = TRUE := rfl
example : <{false}> = FALSE := rfl

def x : String := "x"
def y : String := "y"
def z : String := "z"

#check (x : tm)
#check <{x}>
#check λ x: BOOL, x
#check λ x: BOOL, x ↠ y ↠ z
#check λ x: (BOOL → BOOL → BOOL), x ↠ x
#check TRUE

def subst (x : String) (s : tm) (t : tm) : tm :=
  match t with
  | tm.tm_var y =>
    if x = y then s else t
  | tm.tm_app t1 t2 =>
    (subst x s t1) ↠ (subst x s t2)
  | λ y: T, t1 =>
    if x = y then t else λ y: T, (subst x s t1)
  | If t1 Then t2 Else t3 =>
    If <{subst x s t1}> Then <{subst x s t2}>
    Else <{subst x s t3}>
  | TRUE => TRUE
  | FALSE => FALSE

notation t " [" x ":=" s "] " => subst x s t

#check <{λ x: BOOL, x}> [x := TRUE]

example: <{λ x: BOOL, y}> [x := TRUE] = λ x: BOOL, y :=
  rfl
example: <{λ x: BOOL, y}> [y := TRUE] = λ x: BOOL, TRUE :=
  rfl
example: <{If x Then TRUE Else FALSE}> [x := TRUE] =
          <{If true Then true Else false}> := rfl
example: <{x ↠ x}> [x := (λ x: BOOL, x ↠ x)] =
        <{(λ x: BOOL, x ↠ x) ↠ (λ x: BOOL, x ↠ x)}> := by
  rfl

inductive substi (s : tm) (x : String) : tm → tm → Prop :=
  | s_var1 :
    substi s x <{x}> s
  | s_var2 (y : String) :
    x ≠ y → substi s x <{y}> <{y}>
  | s_app (t1 t2 t1' t2' : tm) :
    substi s x t1 t1' → substi s x t2 t2' →
    substi s x (t1 ↠ t2) (t1' ↠ t2')
  | s_abs1 (T : ty) (t : tm) :
    substi s x (λ x: T, t) (λ x: T, t)
  | s_abs2 (y : String) (T : ty) (t t' : tm) :
    x ≠ y → substi s x t t' →
    substi s x (λ y: T, t) (λ y: T, t')
  | s_true : substi s x TRUE TRUE
  | s_false : substi s x FALSE FALSE
  | s_if (t1 t2 t3 t1' t2' t3' : tm) :
    substi s x t1 t1' → substi s x t2 t2' → substi s x t3 t3' →
    substi s x (If t1 Then t2 Else t3) (If t1' Then t2' Else t3')

open substi

theorem substi_correct: ∀ s x t t', substi s x t t' ↔ t [x := s] = t' := by
  intro s x t t'
  constructor
  · intro h
    induction h with
    | s_var1 =>
      unfold subst
      rw [if_pos rfl]
    | s_var2 y h1 =>
      unfold subst
      rw [if_neg h1]
    | s_app t1 t2 t1' t2' h1 h2 ih1 ih2 =>
      unfold subst
      rw [ih1, ih2]
    | s_abs1 T t =>
      unfold subst
      rw [if_pos rfl]
    | s_abs2 y T t t' h1 h2 ih =>
      unfold subst
      rw [if_neg h1, ih]
    | s_true => rfl
    | s_false => rfl
    | s_if t1 t2 t3 t1' t2' t3' h1 h2 h3 ih1 ih2 ih3 =>
      unfold subst
      rw [ih1, ih2, ih3]
  . intro h
    induction t generalizing x s t' with
    | tm_var y =>
      rw [← h]; unfold subst
      cases (decEq x y) with
      | isTrue h => rw [if_pos h]; exact h ▸ s_var1
      | isFalse h => rw [if_neg h]; exact s_var2 y h
    | tm_app t1 t2 ih1 ih2 =>
      rw [← h]; unfold subst
      apply s_app
      · apply ih1; rfl
      · apply ih2; rfl
    | tm_abs y T t ih =>
      rw [← h]; unfold subst
      cases (decEq x y) with
      | isTrue h => rw [if_pos h]; exact h ▸ s_abs1 T t
      | isFalse h =>
        rw [if_neg h]
        apply s_abs2 y T t
        · exact h
        · apply ih; rfl
    | tm_true => exact h ▸ s_true
    | tm_false => exact h ▸ s_false
    | tm_if t1 t2 t3 ih1 ih2 ih3 =>
      rw [← h]; unfold subst
      apply s_if
      · apply ih1; rfl
      · apply ih2; rfl
      · apply ih3; rfl
end term

section step
inductive value : tm → Prop
  | v_abs (x : String) (T : ty) (t : tm) :
      value <{ λ x:T,t }>
  | v_true : value <{ TRUE }>
  | v_false : value <{ FALSE }>

inductive step : tm → tm → Prop :=
  | ST_AppAbs : ∀ x T2 t1 v2,
    value v2 → step <{(λ x: T2, t1) ↠ v2}> <{t1 [x := v2]}>
  | ST_App1 : ∀ t1 t1' t2,
    step t1 t1' → step <{t1 ↠ t2}> <{t1' ↠ t2}>
  | ST_App2 : ∀ v1 t2 t2',
    value v1 → step t2 t2' → step <{v1 ↠ t2}> <{v1 ↠ t2'}>
  | ST_IfTrue : ∀ t1 t2,
    step <{If TRUE Then t1 Else t2}> t1
  | ST_IfFalse : ∀ t1 t2,
    step <{If FALSE Then t1 Else t2}> t2
  | ST_If : ∀ t1 t1' t2 t3,
    step t1 t1' → step <{If t1 Then t2 Else t3}> <{If t1' Then t2 Else t3}>

notation:80 x:90 " ->- " y:90 => step x y
#check λ x: BOOL, (x ↠ x) ->- λ x: BOOL, (x ↠ x)

inductive multi {X : Type} (R : X → X → Prop) : X → X → Prop
  | multi_refl : ∀ x, multi R x x
  | multi_step : ∀ x y z, R x y → multi R y z → multi R x z
open multi
notation "multistep" => multi step
notation:99 x:99 " ->* " y:99 => multistep x y

def idBB := <{λ x: (BOOL → BOOL), x}>
def idB := <{λ x: BOOL, x}>
def idBBBB := <{λ x: ((BOOL → BOOL) → (BOOL → BOOL)), x}>
def K := <{λ x: BOOL, <{λ y: BOOL, x}> }>
def notB := <{λ x: BOOL, If x Then FALSE Else TRUE}>


#check (idBB ↠ idB)
#check idB

example : <{idBB ↠ idB}> ->* idB := by
  apply multi_step
  · apply step.ST_AppAbs
    apply value.v_abs
  apply multi_refl

example : <{ idBB ↠ <{idBB ↠ idB}>}> ->* idB := by
  apply multi_step
  --  <{ idBB ↠ <{idBB ↠ idB}>}>  ->-  <{idBB ↠ idB}>
  · apply step.ST_App2
    · apply value.v_abs
    · apply step.ST_AppAbs
      apply value.v_abs
  -- <{idBB ↠ idB}>  ->*  idB
  apply multi_step
  · apply step.ST_AppAbs
    apply value.v_abs
  apply multi_refl

example : <{ idBB ↠ notB ↠ TRUE}> ->* FALSE := by
  apply multi_step
  · apply step.ST_App1
    apply step.ST_AppAbs
    apply value.v_abs
  apply multi_step
  · apply step.ST_AppAbs
    apply value.v_true
  dsimp [subst]
  apply multi_step
  · apply step.ST_IfTrue
  apply multi_refl

example : <{ idBB ↠ (notB ↠ TRUE) }> ->* <{FALSE}> := by
  apply multi_step
  apply step.ST_App2
  apply value.v_abs
  apply step.ST_AppAbs
  apply value.v_true
  apply multi_step
  apply step.ST_App2
  apply value.v_abs
  exact step.ST_IfTrue FALSE TRUE
  refine multi_step (idBB ↠ FALSE) FALSE FALSE ?_ ?_
  apply step.ST_AppAbs
  exact value.v_false
  apply multi_refl

example : <{ idBBBB ↠ idBB ↠ idB }> ->* idB := by
  apply multi_step
  apply step.ST_App1
  apply step.ST_AppAbs
  apply value.v_abs
  apply multi_step
  apply step.ST_AppAbs
  apply value.v_abs
  apply multi_refl

def normal_form {X : Type*} (R : X → X → Prop) (t : X) : Prop :=
  ¬ ∃ t', R t t'

end step

section type
notation "context" => Finmap (fun _:String => ty)

open Finmap
inductive has_type : context → tm → ty → Prop :=
  | T_Var : ∀ Γ x T1,
    (Finmap.lookup x Γ) = some T1 →
      has_type Γ <{x}> T1
  | T_Abs : ∀ Γ x T1 T2 t1,
    has_type (Γ.insert x T1) t1 T2 →
      has_type Γ <{λ x: T1, t1}> (T1 → T2)
  | T_app : ∀ Γ t1 t2 T1 T2,
    has_type Γ t1 (T1 → T2) →
    has_type Γ t2 T1 →
    has_type Γ <{t1 ↠ t2}> T2
  | T_True : ∀ Γ,
    has_type Γ <{TRUE}> BOOL
  | T_False : ∀ Γ,
    has_type Γ <{FALSE}> BOOL
  | T_If : ∀ Γ t1 t2 t3 T,
    has_type Γ t1 BOOL →
    has_type Γ t2 T →
    has_type Γ t3 T →
    has_type Γ <{If t1 Then t2 Else t3}> T
open has_type

notation Γ " ⊢ " t " : " T => has_type Γ t T
set_option diagnostics true
#check ∅ ⊢ x : BOOL
#check  ∅ ⊢ (λ x: BOOL, x) : BOOL → BOOL
example : ∅ ⊢ λ x: BOOL, x : BOOL → BOOL := by
  apply T_Abs
  apply T_Var
  rfl

example : ∅ ⊢ λ x: BOOL, <{λ y : (BOOL → BOOL), (y ↠ (y ↠ x))}> : BOOL → (BOOL → BOOL) → BOOL := by
  apply T_Abs
  apply T_Abs
  apply T_app
  · apply T_Var
    rfl
  apply T_app
  · apply T_Var
    rfl
  apply T_Var
  rfl

example : ∃ T, ∅ ⊢ λ x : (BOOL → BOOL), <{λ y : (BOOL → BOOL), <{λ z : BOOL, (y ↠ (x ↠ z))}>}> : T := by
  use (BOOL → BOOL) → (BOOL → BOOL) → BOOL → BOOL
  apply T_Abs
  apply T_Abs
  apply T_Abs
  apply T_app
  exact
    T_Var (Finmap.insert z BOOL (Finmap.insert y (BOOL → BOOL) (Finmap.insert x (BOOL → BOOL) ∅))) y
      (BOOL → BOOL) rfl
  apply T_app
  exact
    T_Var (Finmap.insert z BOOL (Finmap.insert y (BOOL → BOOL) (Finmap.insert x (BOOL → BOOL) ∅))) x
      (BOOL → BOOL) rfl
  exact
    T_Var (Finmap.insert z BOOL (Finmap.insert y (BOOL → BOOL) (Finmap.insert x (BOOL → BOOL) ∅))) z
      BOOL rfl

example : ¬ ∃ T, ∅ ⊢ λ x : BOOL, <{λ y : BOOL, (x ↠ y)}> : T := by
  rintro ⟨T, h⟩
  cases h with
  | T_Abs _ _ _ T2 _ h2 =>
    cases h2 with
    | T_Abs _ _ _ T2' _ h2' =>
      cases h2' with
      | T_app _ _ _ T1' _ h2'' h3'' =>
        cases h2'' with
        | T_Var _ _ _ h2''' =>
          by_cases hxy: x = y
          · rw [hxy, lookup_insert] at h2'''
            injection h2'''
            contradiction
          rw [lookup_insert_of_ne _ hxy, lookup_insert] at h2'''
          injection h2'''
          contradiction

example : ¬ (∃ S T, ∅ ⊢ λ x : S, <{y ↠ y}> : T) := by
  rintro ⟨_, _, p⟩
  cases p with
  | T_Abs _ _ _ _ _ h₁ =>
  cases h₁ with
  | T_app _ _ _ _ _ h₂ _ =>
  cases h₂ with
  | T_Var _ _ _ h₃ =>
  by_cases hxy: x = y
  rw [hxy, lookup_insert] at h₃
  injection h₃
  contradiction
  rw [lookup_insert_of_ne _ (fun a => hxy (id (Eq.symm a)))] at h₃
  simp only [lookup_empty] at h₃

end type

end STLC


namespace partialmap
open STLC Finmap

class includedin (a b : context) : Prop :=
  property : ∀ {x T}, a.lookup x = some T → b.lookup x = some T

@[simp]
def includedin_refl (a : context) : includedin a a where
  property := fun h => h

@[simp]
def includedin_empty (a : context) : includedin ∅ a where
  property := fun h => by simp only [lookup_empty] at h

#check lookup_insert
def includedin_insert {a b : context} (h1: includedin a b) (x : String) (T : ty):
    includedin (a.insert x T) (b.insert x T) where
  property := fun {x' T'} hx' => by
    by_cases h: x' = x
    · rw [h, lookup_insert] at hx'
      rw [h, lookup_insert]
      exact hx'
    · rw [lookup_insert_of_ne _ h] at hx'
      rw [lookup_insert_of_ne _ h]
      exact h1.property hx'
end partialmap
