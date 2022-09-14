meta def my_first_tactic : tactic unit := tactic.trace "Hello, World."

example : true :=
begin
  my_first_tactic,
  trivial,
end

meta def my_second_tactic' : tactic unit :=
do
  tactic.trace "Hello,",
  tactic.trace "World."

example : true :=
begin
  my_second_tactic',
  trivial,
end

meta def my_failing_tactic  : tactic unit := tactic.failed

meta def my_failing_tactic' : tactic unit :=
tactic.fail "This tactic failed, we apologize for the inconvenience."

example: true:=
begin
  my_failing_tactic',
end

meta def my_orelse_tactic : tactic unit :=
my_failing_tactic <|> my_first_tactic

example : true:=
begin
  my_orelse_tactic,
  trivial
end

meta def trace_goal : tactic unit :=
 tactic.target >>= tactic.trace

example : true:=
begin
  trace_goal,
  trivial
end

meta def trace_goal' : tactic unit :=
do
 goal ← tactic.target,
 tactic.trace goal

example : true:=
begin
  trace_goal',
  trivial
end

meta def let_example : tactic unit :=
do
 let message := "Hello, World.",
 tactic.trace message

example : true:=
begin
  let_example,
  trivial
end

meta def is_done : tactic bool :=
(tactic.target >> return ff) <|> return tt

meta def trace_is_done : tactic unit :=
is_done >>= tactic.trace

example : true:=
begin
  trace_is_done,
  trivial,
  trace_is_done,
end

meta def trace_goal_is_eq : tactic unit :=
do t ← tactic.target,
   match t with
   | `(%%l = %%r) := tactic.trace $ "Goal is equality between " ++ (to_string l) ++ " and " ++ (to_string r)
   | _ := tactic.trace "Goal is not an equality"
   end

meta def trace_goal_is_eq' : tactic unit :=
do `(%%l = %%r) ← tactic.target | tactic.trace "Goal is not an equality",
   tactic.trace $ "Goal is equality between " ++ (to_string l) ++ " and " ++ (to_string r)

example : 0=0:=
begin
  trace_goal_is_eq',
  trivial,
  trace_is_done,
end

meta def trace_goal_is_eq'' : tactic unit :=
(do  `(%%l = %%r) ← tactic.target,
     tactic.trace $ "Goal is equality between " ++ (to_string l) ++ " and " ++ (to_string r),
     trace_goal_is_eq)
   <|> tactic.trace "Goal is not an equality, or `some_other_tactic` failed"

example : true:=
begin
  trace_goal_is_eq'',
  trivial,
  trace_is_done,
end

meta def trace_goal_is_eq0 : tactic unit :=
do { `(%%l = %%r) ← tactic.target,
     tactic.trace $ "Goal is equality between " ++ (to_string l) ++ " and " ++ (to_string r) }
   <|> tactic.trace "Goal is not an equality"

example : 0=0:=
begin
  trace_goal_is_eq0,
  trivial,
  trace_is_done,
end

meta def find_matching_type (e : expr) : list expr → tactic expr
| []         := tactic.failed
| (H :: Hs)  := do t ← tactic.infer_type H,
                   (tactic.unify e t >> return H) <|> find_matching_type Hs

example : 0=0:=
begin
  --find_matching_type true,--?? what to feed
  trivial,
  trace_is_done,
end

meta def my_assumption : tactic unit :=
do { ctx ← tactic.local_context,
     t   ← tactic.target,
     find_matching_type t ctx >>= tactic.exact }
<|> tactic.fail "my_assumption tactic failed"

example (h: 0=0): 0=0:=
begin
  my_assumption,
  trivial,
  trace_is_done,
end

meta def list_types : tactic unit :=
do
  l ← tactic.local_context,
  l.mmap (λ h, tactic.infer_type h >>= tactic.trace),
  return ()

example (h: 1=0) (h1: 2=2): 0=0:=
begin
  list_types,
  trivial,
  trace_is_done,
end

example (a b j k : ℤ) (h₁ : a = b) (h₂ : j = k) :
  a + j = b + k :=
begin
  have := congr (congr_arg has_add.add h₁) h₂,
  exact this
end

open tactic.interactive («have»)
open tactic (get_local infer_type)

open interactive (parse)
open lean.parser (ident)

meta def tactic.interactive.add_eq (h1 : parse ident) (h2 : parse ident) : tactic unit :=
do e1 ← get_local h1,
   e2 ← get_local h2,
   «have» none none ``(_root_.congr (congr_arg has_add.add %%e1) %%e2)

example (a b j k : ℤ) (h2 : a = b) (h₂ : j = k) :
  a + j = b + k :=
begin
  add_eq h2 h₂,
  exact this,
end

meta example : (parse ident) = name := rfl

open lean.parser (tk)
meta def tactic.interactive.add_eq' (h1 : parse ident) (h2 : parse ident)
  (h : parse (optional (tk "with" *> ident))) : tactic unit :=
do e1 ← get_local h1,
   e2 ← get_local h2,
   «have» h none ``(_root_.congr (congr_arg has_add.add %%e1) %%e2)

example (m a b c j k : ℤ) (Hj : a = b) (Hk : j = k) :
  a + j = b + k :=
begin
  add_eq' Hj Hk with new,
  exact new,
end



open interactive (loc.ns)
open interactive.types (texpr location)


meta def tactic.interactive.mul_left_bis (clear_hyp : parse (optional $ tk "!")) (q : parse texpr) :
parse location → tactic unit
| (loc.ns [some h]) := do
   e ← tactic.i_to_expr q,
   H ← get_local h,
   `(%%l = %%r) ← infer_type H,
   «have» (H.local_pp_name ++ "mul" : name) ``(%%e*%%l = %%e*%%r) ``(congr_arg (λ x, %%e*x) %%H),
   when clear_hyp.is_some (tactic.clear H)
| _ := tactic.fail "mul_left_bis takes exactly one location"

example (a b c : ℤ) (hyp : a = b) : c*a = c*b :=
begin
  mul_left_bis c at hyp,
  exact hyp.mul,
end

meta def tactic.interactive.mul_left (q : parse texpr) : parse location → tactic unit
| (loc.ns [some h]) := do
   e ← tactic.i_to_expr q,
   H ← get_local h,
   `(%%l = %%r) ← infer_type H,
   «have» h ``(%%e*%%l = %%e*%%r) ``(congr_arg (λ x, %%e*x) %%H),
   tactic.clear H
| _ := tactic.fail "mul_left takes exactly one location"

meta def tactic.interactive.mul_right (q : parse texpr) : parse location → tactic unit
| (loc.ns [some h]) := do
   e ← tactic.i_to_expr q,
   H ← get_local h,
   `(%%l = %%r) ← infer_type H,
   «have» h ``(%%l*%%e = %%r*%%e) ``(congr_arg (λ x, x*%%e) %%H),
   tactic.clear H
| (loc.ns [some h]) := do
   e ← tactic.i_to_expr q,
   H ← get_local h,
   `(%%l = %%r) ← infer_type H,
   «have» h ``(%%e*%%l = %%e*%%r) ``(congr_arg (λ x, %%e*x) %%H),
   tactic.clear H
| _ := tactic.fail "mul_left takes exactly one location"
example (a b c : ℤ) (hyp : a = b) : c*a = c*b :=
begin
  --mul_left c at hyp,
  mul_right c at hyp,
  exact hyp,
end

example (a b c : ℤ) (hyp : a = b) : c*a = c*b :=
begin
  have hyp := congr_arg (λ x, c*x) hyp,
  exact hyp,
end
