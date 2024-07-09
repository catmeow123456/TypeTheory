namespace STLC

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

notation "≪" e "≫" => e
infixr:50  "→" => fun S T => ty.Ty_Arrow S T
infixl:1   "↠" => fun S T => tm.tm_app S T
notation "λ" x ":" T "," t => tm.tm_abs x T t
notation "If" x "Then" y "Else" z => tm.tm_if x y z

#check ≪ tm.tm_var "x" ≫ ↠ ≪ tm.tm_abs "x" ty.Ty_Bool ≪tm.tm_var "x"≫ ≫
#check ≪ tm.tm_var "x" ≫
#check ≪ tm.tm_abs "x" ty.Ty_Bool ≪tm.tm_var "x"≫ ≫
#check ≪ λ "x" : ty.Ty_Bool , tm.tm_var "x" ≫

inductive value : tm → Prop
  | v_abs (x : String) (T : ty) (t : tm) :
      value ≪ tm.tm_abs x T t ≫
  | v_true : value ≪ tm.tm_true ≫
  | v_false : value ≪ tm.tm_false ≫

def subst (x : String) (s : tm) (t : tm) : tm :=
  match t with
  | tm.tm_var y =>
    if x == y then s else t
  | tm.tm_app t1 t2 =>
    (subst x s t1) ↠ (subst x s t2)
  | tm.tm_abs y T t1 =>
    if x == y then t else λ y: T, (subst x s t1)
  | tm.tm_if t1 t2 t3 =>
    If ≪subst x s t1≫ Then
      ≪subst x s t2≫
    Else
      ≪subst x s t3≫
  | tm.tm_true => tm.tm_true
  | tm.tm_false => tm.tm_false

notation t "[" x ":=" s "]" => subst x s t



end STLC
