import group_theory.free_group 
  group_theory.group_action
  logic.relation

noncomputable theory
open free_group mul_action classical
local attribute [instance] prop_decidable

section 

parameters {α : Type}
@[reducible] private def G := free_group α 

parameters (Q : Type) [mul_action G Q] (r : Q) (trans_act : orbit G r = set.univ)

@[simp] lemma nil_is_id : (mk [] : G) = 1 := rfl
lemma id_is_id (x : Q) : (mk [] : G) • x = x := by simp

lemma invinv (a : α) (b : bool) : mk [(a,b)] * mk [(a,!b)] = 1
:= mul_inv_self _

@[simp] lemma inv_is_inv (x : Q) (a : α) (b : bool)
: mk [(a,b)] • mk [(a,!b)] • x = x
:= by {rw [smul_smul, invinv _ _], simp}

@[simp] lemma is_inv_inv (x : Q) (a : α) (b : bool)
: mk [(a,!b)] • mk [(a,b)] • x = x := begin
  have h : mk [(a,!b)] • mk [(a,!!b)] • x = x,
  exact inv_is_inv x a (!b),
  rwa bnot_bnot at h,
end

lemma cons_smul (p : α × bool) (l : list (α × bool)) (x : Q)
: mk [p] • mk l • x = (mk (p::l):G) • x := by {rwa smul_smul, refl}

inductive edge (s : Q) : Q → Type
| intro (p : α × bool) : edge (mk [p] • s)

variables {s t : Q}
@[simp] def proj : Π {s t}, edge s t → α × bool
| _ _ ⟨_, p⟩ := p

def change_end {s t t'} (h : t = t') : edge s t → edge s t' := λ p, eq.rec p h

@[simp] lemma change_proj : Π {s t t'} (h : t = t') (e : edge s t),
proj (change_end h e) = proj e
| _ _ _ rfl _ := rfl

@[reducible] def pbnot {β : Type} : β × bool → β × bool
| (a, b) := (a, !b)

lemma pbnot_pbnot : ∀ p : α × bool, pbnot (pbnot p) = p
| (a, b) := by simp

@[reducible] def rev : Π {s t}, edge s t → edge t s
| _ _ ⟨s, (a,b)⟩ := change_end (is_inv_inv s a b) ⟨mk [(a,b)] • s, (a,!b)⟩

@[simp] lemma rev_proj : Π {s t} (e : edge s t), proj (rev e) = pbnot (proj e)
| _ _ ⟨s, (a,b)⟩ := by {rw change_proj, refl}

lemma edge_hext : Π {s t t'} {e : edge s t} {e' : edge s t'} (h : proj e = proj e'), e == e'
| _ _ _ ⟨_, _⟩ ⟨_, _⟩ rfl := heq.rfl

lemma edge_ext {s t} {e e' : edge s t} (h : proj e = proj e') : e = e'
:= eq_of_heq $ edge_hext h

@[simp] lemma rev_rev : Π {s t} (e : edge s t), rev (rev e) = e
| _ _ ⟨s, (a,b)⟩ := by {apply edge_ext, simp}

inductive path : Q → Q → Type
| nil (s : Q) : path s s
| cons {s t t' : Q} (p : path s t) (e : edge t t') : path s t' 

instance e_to_p {s t : Q} : has_coe (edge s t) (path s t) := ⟨λ e, path.cons (path.nil _) e⟩

def path_length : Π {s t : Q} (p : path s t), ℕ
| _ _ (path.nil _) := 0
| _ _ (path.cons p _) := path_length p + 1

@[simp] def pconcat : Π {a b c : Q}, path a b → path b c → path a c
| _ _ _ p (path.nil _) := p
| _ _ _ p (path.cons q e) := path.cons (pconcat p q) e

@[simp] def prev : Π {a b : Q}, path a b → path b a
| _ _ (path.nil _) := path.nil _
| _ _ (path.cons q e) := pconcat ↑(rev e) (prev q)

@[simp] def pmul : Π {a b : Q}, path a b → G
| _ _ (path.nil _) := 1
| _ _ (path.cons q e) := mk [proj e] * pmul q

@[simp] lemma pconcat_mul : ∀ {a b c : Q} (p : path a b) (q : path b c),
pmul (pconcat p q) = pmul q * pmul p
| _ _ _ _ (path.nil _) := by simp
| _ _ _ _ (path.cons _ _) := by {simp, rw [pconcat_mul, mul_assoc]}

@[simp] lemma pmul_smul : ∀ {a b : Q} (p : path a b), pmul p • a = b
| _ _ (path.nil _) := by simp
| s _ (path.cons p ⟨t, x⟩) := by {simp, rw [←smul_smul, pmul_smul]}

@[simp] def path_from_list (s : Q) : Π (l : list (α × bool)), Σ t, path s t
| [] := ⟨s, path.nil s⟩
| (p :: l) := ⟨_, path.cons (path_from_list l).2 ⟨_, p⟩⟩

lemma pfl_cons (s : Q) (l : list (α × bool)) (p : α × bool) :
  (path_from_list s (p::l)).2 = path.cons (path_from_list s l).2 ⟨_, p⟩ := rfl

lemma pfl_cons' (s : Q) (l : list (α × bool)) (p : α × bool) :
  path_from_list s (p::l) = ⟨_, path.cons (path_from_list s l).2 ⟨_, p⟩⟩ := rfl

@[simp] lemma pfl_concat : Π (s : Q) (l : list (α × bool)) (l' : list (α × bool)),
  path_from_list s (l' ++ l) = ⟨_, pconcat (path_from_list s l).2
                                (path_from_list _ l').2⟩
| s l [] := sigma.eq rfl rfl
| s l (p::l') := begin
  have hh : (p::l') ++ l = p::(l'++l), from rfl,
  rw [hh, pfl_cons', pfl_concat, pfl_cons],
  simp,
end

lemma pfl_end (s : Q) : Π (l : list (α × bool)), (path_from_list s l).1 = mk l • s
| [] := by simp
| (p :: l) := by {simp, rw pfl_end, apply cons_smul}

@[reducible] def list_from_path : Π {s t : Q} (p : path s t), list (α × bool)
| _ _ (path.nil _) := []
| _ _ (path.cons p e) := (proj e) :: list_from_path p

lemma lfp_cons {s t t' : Q} {p : path s t} {e : edge t t'}
  : list_from_path (path.cons p e) = (proj e) :: list_from_path p := rfl

lemma path_cons_ext : Π {s t t' : Q} (p : path s t) (e : edge t t'),
  (⟨mk [proj e] • t, path.cons p ⟨t, proj e⟩⟩ : Σ x, path s x) = ⟨t', path.cons p e⟩
| s _ _ p ⟨t, a⟩ := rfl

lemma path_from_path : Π {s t : Q} (p : path s t), path_from_list s (list_from_path p) = ⟨t, p⟩ 
| _ _ (path.nil _) := by simp
| s t' (path.cons p (e:edge t _)) := begin
  have h : list_from_path (path.cons p e) = (proj e) :: list_from_path p, from rfl,
  rw [h, pfl_cons', path_from_path],
  exact path_cons_ext p e,
end

lemma list_from_list (s : Q) : Π (l : list (α × bool)), list_from_path (path_from_list s l).2 = l
| [] := rfl
| (x::l) := begin
  rw pfl_cons,
  rw lfp_cons,
  simp, 
  apply list_from_list,
end

lemma pmul_list : Π {a b : Q} (p : path a b), pmul p = mk (list_from_path p)
| _ _ (path.nil _) := by simp
| _ _ (path.cons _ _) := by {simp, rw pmul_list, simp}

@[simp] lemma path_length_nil {s : Q} : path_length (path.nil s) = 0 := rfl

@[simp] lemma path_length_cons {s t t' : Q} (p : path s t) (e : edge t t')
: path_length (path.cons p e) = path_length p + 1 := rfl

lemma path_length_zero : Π {s t : Q} (p : path s t), path_length p = 0 → t = s
| _ _ (path.nil _) _ := rfl
| s t (path.cons p e) h := begin
  exfalso,
  rw path_length_cons at h,
  exact (nat.succ_ne_zero _) h
end

def dist_ub (t : Q) (n : ℕ) : Prop := ∃ p : path r t, path_length p = n

lemma dist_ub_from_path {t : Q} (p : path r t) : dist_ub t (path_length p) := ⟨p, rfl⟩ 

include trans_act
lemma connected (x : Q) : nonempty (path r x) := begin
  have hx : x ∈ orbit G r,
  rw trans_act,
  trivial,
  cases hx with g hg,
  simp at hg,
  induction g with l,
  apply nonempty.intro,
  rw ←hg,
  have p : path r (mk l • r),
  rw ←pfl_end,
  exact (path_from_list r l).2,
  exact p,
  simp,
end

lemma dist_is_bounded (t : Q) : ∃ n : ℕ, dist_ub t n := begin
  cases (connected t) with p,
  use path_length p,
  exact dist_ub_from_path p
end

def dist (t : Q) : ℕ := nat.find $ dist_is_bounded t
lemma dist_is_attained (t : Q) : ∃ p : path r t, path_length p = dist t
:= nat.find_spec $ dist_is_bounded t
lemma dist_is_dist (t : Q) (p : path r t) : dist t ≤ path_length p :=
nat.find_min' _ $ dist_ub_from_path p

lemma dist_zero_iff {t : Q} : dist t = 0 ↔ t = r := begin
  split,
  intro h,
  cases dist_is_attained t with p hp,
  rw h at hp,
  exact path_length_zero p hp,
  intro h,
  rw h,
  rw le_antisymm_iff,
  split,
  exact dist_is_dist r (path.nil r),
  simp,
end

@[simp] lemma dist_root : dist r = 0 := dist_zero_iff.mpr rfl

def inbhd (x : Q) : Type := Σ y : Q, edge y x
def onbhd (x : Q) : Type := Σ y : Q, edge x y

lemma dist_is_lipschitz (x : Q) (q : onbhd x) : dist q.1 ≤ dist x + 1 := begin
  cases dist_is_attained x with p hp,
  rw ←hp,
  exact dist_is_dist q.1 (path.cons p q.2),
end

lemma ex_closer_nbr (x : Q) (hx : x ≠ r) : ∃ p : inbhd x, dist x = dist p.1 + 1 := begin
  cases dist_is_attained x with p hp,
  cases p with p e,
  exfalso,
  apply hx,
  refl,
  use p_t,
  use p_e,
  rw le_antisymm_iff,
  split,
  exact dist_is_lipschitz p_t ⟨x, p_e⟩,
  rw ←hp,
  simp,
  exact dist_is_dist _ _
end

def my_closer_nbr (x : Q) (hx : x ≠ r) : {p : inbhd x // dist x = dist p.1 + 1} :=
  subtype_of_exists $ ex_closer_nbr x hx

def nb (t : Q) (hn : t ≠ r) : Q := (my_closer_nbr t hn).1.1
def nb_is_nb (t : Q) (hn : t ≠ r) : dist t = dist (nb t hn) + 1 := (my_closer_nbr t hn).2
def nb_edge (t : Q) (hn : t ≠ r) : edge (nb t hn) t := (my_closer_nbr t hn).1.2

section bar
universe v
@[simp] def rec_aux {P : ℕ → Sort v} (f : Π n, (Π m, n = m+1 → P m) → P n) : Π n, P n
| 0 := f 0 (λ m h, false.elim $ nat.succ_ne_zero m h.symm)
| (n+1) := f (n+1) (λ m h, eq.rec (rec_aux n) (nat.succ_inj h))
end bar

section tree_recursion
universe u
parameters {pt : Q → Sort u} (ptr : pt r) (pt_succ : Π t (hn : t ≠ r), pt (nb t hn) → pt t)

@[simp] def helper (n) (f : Π m : ℕ, n = m+1 → (Π x, dist x = m → pt x)) (t) (h : dist t = n) : pt t :=
dite (t=r) (λ hr, eq.rec ptr hr.symm) $ λ hnr,
pt_succ t hnr (f (dist $ nb t hnr) (eq.rec (nb_is_nb t hnr) h) _ rfl)

def tree_recursion (t : Q) : pt t := rec_aux helper (dist t) t rfl

lemma my_ext {t : Q} : Π n (h : dist t = n),
rec_aux helper n t h = rec_aux helper (dist t) t rfl | _ rfl := rfl

lemma recursion_at_root : tree_recursion r = ptr := begin
  have hh : tree_recursion r = rec_aux helper 0 r dist_root,
  exact (my_ext 0 dist_root).symm,
  rw hh,
  simp,
end

lemma recursion_away (t : Q) (h : t ≠ r) : tree_recursion t
= pt_succ t h (tree_recursion (nb t h)) := begin
  have hh : tree_recursion t = rec_aux helper (dist (nb t h) + 1) t (nb_is_nb t h),
  exact (my_ext _ (nb_is_nb t h)).symm,
  rw hh,
  simp,
  apply dif_neg,
end
end tree_recursion

def tree_path : Π t, path r t := tree_recursion (path.nil r)
(λ t hn p, path.cons p (nb_edge t hn))

def is_in_dir_tree {s t : Q} (e : edge s t) : Prop :=
  ∃ (hn : t ≠ r), (my_closer_nbr t hn).1 = ⟨s, e⟩

def is_in_tree {s t : Q} (e : edge s t) : Prop :=
  is_in_dir_tree e ∨ is_in_dir_tree (rev e)

lemma is_in_tree_unfold {s t : Q} (e : edge s t)
: is_in_tree e ↔ is_in_dir_tree e ∨ is_in_dir_tree (rev e) := by refl

lemma is_in_tree_rev {s t : Q} {e : edge s t} : is_in_tree (rev e) ↔ is_in_tree e := 
  by {repeat {rw is_in_tree_unfold}, simp, tauto}

lemma not_in_tree_rev {s t : Q} {e : edge s t} : ¬is_in_tree (rev e) ↔ ¬is_in_tree e
:= by {rw is_in_tree_rev}

def R : Type := {p : Σ s t, edge s t // ¬is_in_tree p.2.2 ∧ (proj p.2.2).2}
def to_s (x : R) : Q := x.1.1
def to_t (x : R) : Q := x.1.2.1
def to_edge (x : R) : edge (to_s x) (to_t x) := x.1.2.2
def rmk (s t : Q) (e : edge s t) (h : ¬ is_in_tree e) (hh : (proj e).2)
  : R := ⟨⟨s, t, e⟩, h, hh⟩

def rmk_ext : Π {s t : Q} {e e' : edge s t} {h : ¬is_in_tree e} {hh : (proj e).2}
  {h' : ¬is_in_tree e'} {hh' : (proj e').2} (he : e = e'), rmk s t e h hh = rmk s t e' h' hh'
| _ _ _ _ _ _ _ _ rfl := rfl

lemma rev_ori : Π {s t} {e : edge s t}, (proj (rev e)).2 ↔ ¬(proj e).2
| _ _ ⟨s, (a,tt)⟩ := by simp
| _ _ ⟨s, (a,ff)⟩ := by simp

def from_edge {s t : Q} (e : edge s t) (h : ¬is_in_tree e) : R × bool :=
dite (proj e).2 (λ hh, (rmk s t e h hh, tt))
                (λ hh, (rmk t s (rev e) (not_in_tree_rev.mpr h) (rev_ori.mpr hh), ff))

lemma from_edge_unfold {s t : Q} (e : edge s t) (h : ¬is_in_tree e) :
from_edge e h = dite (proj e).2 (λ hh, (rmk s t e h hh, tt))
       (λ hh, (rmk t s (rev e) (not_in_tree_rev.mpr h) (rev_ori.mpr hh), ff)) := rfl

lemma r_from_r : Π x : R, from_edge (to_edge x) x.2.1 = (x, tt)
| ⟨⟨s, ⟨t, e⟩⟩, ⟨h, hh⟩⟩ := begin
  rw [from_edge_unfold, dif_pos],
  refl,
  assumption,
end

lemma from_edge_rev : Π {s t : Q} (e : edge s t) (h : ¬ is_in_tree e)
  (h' : ¬ is_in_tree (rev e)), from_edge (rev e) h' = pbnot (from_edge e h)
| _ _ ⟨s, (a,tt)⟩ h h' := begin
  repeat {rw from_edge_unfold},
  rw [dif_neg, dif_pos, rmk_ext (rev_rev _)],
  refl,
  simp,
  simp,
end
| _ _ ⟨s, (a,ff)⟩ h h' :=
by {repeat {rw from_edge_unfold}, rw [dif_pos, dif_neg], refl, simp}

def from_edge_maybe {s t} (e : edge s t) : list (R × bool) :=
  dite (is_in_tree e) (λ _, []) (list.ret ∘ from_edge e)

lemma fem_unfold {s t} {e : edge s t} :
  from_edge_maybe e = dite (is_in_tree e) (λ _, []) (λ h, [from_edge e h]) := rfl

def to_loop (x : R) : path r r :=
  pconcat (path.cons (tree_path (to_s x)) (to_edge x)) $ prev $ tree_path (to_t x)

def F := free_group R
@[simp] private def H := stabilizer G r

instance H_is_subgroup : is_subgroup H := mul_action.is_subgroup r

@[simp] noncomputable def plist : Π {a b : Q}, path a b → list (R × bool)
| _ _ (path.nil _) := []
| _ _ (path.cons p e) := from_edge_maybe e ++ plist p

lemma plist_wd : Π {s s' : Q} (h : s = s') (l : list (α × bool)),
  plist (path_from_list s l).snd = plist (path_from_list s' l).snd
| _ _ rfl _ := rfl

lemma plist_concat : Π {a b c : Q} (p : path a b) (p' : path b c),
  plist (pconcat p p') = plist p' ++ plist p
| a _ _ p (path.nil b) := by simp
| a b c' p (path.cons p' e) := by {simp, rw plist_concat}

lemma tree_path_root : tree_path r = path.nil r
  := recursion_at_root _ _

lemma tree_path_away {x : Q} (hn : x ≠ r)
  : tree_path x = path.cons (tree_path (nb x hn)) (nb_edge x hn)
  := recursion_away _ _ _ _

@[reducible] def rlist : Q → list (α × bool) → list (R × bool)
  := λ s l, plist (path_from_list s l).2

@[simp] lemma rlist_concat (s : Q) (l l' : list (α × bool)) :
rlist s (l' ++ l) = rlist (mk l • s) l' ++ rlist s l := begin
  have h : rlist s (l' ++ l) = plist (path_from_list s (l' ++ l)).2, from rfl,
  rw [h, pfl_concat],
  simp,
  rw [plist_concat, plist_wd (pfl_end s l) l'],
end

@[simp] def rmul : Q → list (α × bool) → F := λ s l, mk (rlist s l)

lemma concat_to_mul {l l' : list (R × bool)} :
  mk (l++l') = mk l * mk l' := rfl

lemma rlist_singleton {t : Q} {p : α × bool} :
  rlist t [p] = plist (path.cons (path.nil t) (edge.intro t p)) := rfl

lemma plist_singleton {s t : Q} {e : edge s t} : plist (path.cons (path.nil s) e)
  = from_edge_maybe e := by simp

lemma change_fem : Π {s t t'} {e : edge s t} (h : t = t'),
  from_edge_maybe e = from_edge_maybe (change_end h e)
| _ _ _ _ rfl := rfl

lemma plist_tp : Π {x : Q}, plist (tree_path x) = []
  := tree_recursion (by {rw tree_path_root, simp}) begin
  intros x hn h,
  rw tree_path_away hn,
  simp,
  split,
  rw fem_unfold,
  rw dif_pos,
  apply or.inl,
  use hn,
  exact sigma.eq rfl rfl,
  assumption,
end

lemma plist_rev_tp : Π {x : Q}, plist (prev $ tree_path x) = []
  := tree_recursion (by {rw tree_path_root, simp}) begin
  intros x hn h,
  rw tree_path_away hn,
  simp,
  rw plist_concat,
  simp,
  split,
  assumption,
  have p : ↑(rev (nb_edge x hn)) = path.cons (path.nil _) (rev (nb_edge x hn)),
  refl,
  rw p,
  rw plist_singleton,
  rw fem_unfold,
  rw dif_pos,
  apply or.inr,
  rw rev_rev,
  use hn,
  exact sigma.eq rfl rfl,
end

lemma pbnot_inv {β : Type} : Π (p : β × bool), mk [pbnot p] * mk [p] = 1
| (a, b) := inv_mul_self $ mk [(a,b)]

lemma inv_pbnot {β : Type} : Π (p : β × bool), mk [p] * mk [pbnot p] = 1
| (a, b) := mul_inv_self $ mk [(a,b)]

lemma red_smul : ∀ {s l l'}, red.step l l' → rmul s l = rmul s l'
| s _ _ (@red.step.bnot _ L1 L2 a b) := begin
  simp,
  have h : (mk ((a,b)::(a,!b)::L2) : G) = mk L2,
  from quot.sound (@red.step.bnot _ [] L2 a b),
  rw h,
  suffices g : mk (rlist s ((a,b)::(a,!b)::L2)) = mk (rlist s L2),
  by {repeat {rw concat_to_mul}, cc},
  have h : (((a,b)::(a,!b)::L2):list(α×bool)) = [(a,b)] ++ [(a,!b)] ++ L2,
  from rfl,
  rw h,
  repeat {rw rlist_concat},
  repeat {rw concat_to_mul},
  set t := mk L2 • s,
  suffices g : mk (rlist (mk [(a,!b)] • t) [(a,b)]) * mk (rlist t [(a,!b)]) = 1,
  by {rw g, simp},
  repeat {rw rlist_singleton},
  repeat {rw plist_singleton},
  set e := edge.intro t (a,!b),
  have h : from_edge_maybe (edge.intro (mk [(a,!b)] • t) (a,!!b)) = from_edge_maybe (rev e),
  apply change_fem,
  rw bnot_bnot at h,
  rw h,
  repeat {rw fem_unfold},
  cases (em $ is_in_tree e) with pos neg,
  rw [dif_pos, dif_pos],
  simp,
  assumption, 
  rwa is_in_tree_rev,
  rw [dif_neg, dif_neg, from_edge_rev],
  apply pbnot_inv,
  assumption,
  rwa is_in_tree_rev,
end

instance f_is_group : group F := free_group.group

def f_of_g : G → F := quot.lift (rmul r) (@red_smul r)
def f_of_h : H → F := f_of_g ∘ coe
def h_of_f : F → H := to_group $ λ a, ⟨pmul (to_loop a), by simp⟩

lemma f_of_g.mk (l : list (α × bool)) : f_of_g (mk l) = rmul r l := rfl
lemma f_of_h_mul : ∀ (x : G) (y : H), f_of_g (x*y) = f_of_g x * f_of_g y
| x ⟨y, h⟩ := begin
  induction x with l,
  induction y with l',
  simp,
  simp at h,
  repeat {rw f_of_g.mk},
  simp,
  rw h,
  simp,
  simp,
end

instance f_of_h.is_hom : is_group_hom f_of_h := {map_mul := λ x y, f_of_h_mul x y}
instance h_of_f.is_hom : is_group_hom h_of_f := to_group.is_group_hom

lemma coe_mul {a b : H} : ↑(a*b) = (↑a * ↑b:G) := rfl

lemma pmul_tp_change : Π {s t : Q} {e : edge s t} (h : is_in_dir_tree e),
  mk [proj e] * pmul (tree_path s) = pmul (tree_path t)
| s t e ⟨hn, he⟩ := begin
  have p : s = (my_closer_nbr t hn).1.1,
  rw he,  
  have q : proj e = proj ((my_closer_nbr t hn).1.2),
  rw he,
  rw q,
  rw p,
  suffices g : mk [proj (nb_edge t hn)] * pmul (tree_path (nb t hn))
                = pmul (tree_path t),
  exact g,
  rw tree_path_away hn,
  simp,
end

lemma pmul_prev : Π {s t} (p : path s t), pmul (prev p) = (pmul p)⁻¹ 
| _ _ (path.nil s) := by simp
| s t' (path.cons p (e:edge t _)) := begin
  simp,
  rw pmul_prev,
  simp,
  have h : ↑(rev e) = path.cons (path.nil t') (rev e), from rfl,
  rw h,
  simp,
  cases proj e with a b,
  refl,
end

lemma h_of_f.from_edge {s t} {e : edge s t} (hn : ¬is_in_tree e) (h : (proj e).2) :
  ↑(h_of_f (mk [from_edge e hn])) = (pmul (tree_path t))⁻¹ * mk [proj e] *
                                    pmul (tree_path s) := begin
  rw from_edge_unfold,
  rw dif_pos h,
  have p : ∀ x, h_of_f x = to_group (λ a, ⟨pmul (to_loop a), by simp⟩) x,
  intro x,
  refl,
  rw p,
  have q : mk [(rmk s t e hn h, tt)] = of (rmk s t e hn h), from rfl,
  rw q,
  rw to_group.of,
  simp,
  have p' : to_loop (rmk s t e hn h) = pconcat (path.cons (tree_path s) e) (prev (tree_path t)),
  refl,
  rw p',
  simp,
  rw mul_assoc,
  simp,
  apply pmul_prev,
  exact r, -- TODO: where does this goal come from???
end

lemma pbnot_is_inv {β : Type} : Π (p : β × bool), mk [pbnot p] = (mk [p])⁻¹
| (x, b) := rfl

lemma coe_inv {x : H} : (↑x⁻¹ : G) = (↑x)⁻¹ := rfl

lemma h_of_f.from_edge' {s t} {e : edge s t} (hn : ¬is_in_tree e) (h : ¬(proj e).2) :
  ↑(h_of_f (mk [from_edge e hn])) = (pmul (tree_path t))⁻¹ * mk [proj e] *
                                    pmul (tree_path s) := begin
  have p : from_edge e hn = pbnot (from_edge (rev e) (not_in_tree_rev.mpr hn)),
  rw from_edge_unfold,
  rw from_edge_unfold,
  rw [dif_neg, dif_pos],
  refl,
  assumption,
  rw p,
  rw pbnot_is_inv,
  rw is_group_hom.map_inv h_of_f,
  have q : ↥(proj $ rev e).2,
  rw rev_ori,
  assumption,
  rw coe_inv,
  rw h_of_f.from_edge,
  repeat {rw mul_inv_rev},
  repeat {rw mul_assoc},
  rw mul_left_inj,
  rw inv_inv,
  rw mul_right_inj,
  rw rev_proj,
  rw pbnot_is_inv,
  simp,
  assumption,
end

lemma g_of_p : Π {s t} {p : path s t}, pmul p
  = pmul (tree_path t) * h_of_f (mk $ plist p) * (pmul (tree_path s))⁻¹ 
| _ _ (path.nil s) := begin
  have h : plist (path.nil s) = [], from rfl,
  rw h,
  have h' : h_of_f (mk []) = 1, from rfl,
  rw h',
  simp,
end
| s t' (path.cons p (e:edge t _)) := begin
  simp,
  rw g_of_p,
  rw ←mul_assoc,
  simp,
  have h : mk (from_edge_maybe e ++ plist p) = 
    mk (from_edge_maybe e) * mk (plist p), from rfl,
  rw h,
  rw is_mul_hom.map_mul h_of_f,
  rw coe_mul,
  repeat {rw ←mul_assoc},
  simp,
  cases (em $ is_in_tree e) with pos neg,
  rw [fem_unfold, dif_pos pos],
  have h' : h_of_f (mk []) = 1, from rfl,
  rw h',
  simp,
  cases pos with a b,
  exact pmul_tp_change a,
  rw ←pmul_tp_change b,
  rw ←mul_assoc,
  simp,
  exact inv_pbnot _,
  rw [fem_unfold, dif_neg neg],
  cases (em (proj e).2) with x y,
  rw h_of_f.from_edge neg x,
  repeat {rw ←mul_assoc},
  simp,
  rw h_of_f.from_edge' neg y,
  repeat {rw ←mul_assoc},
  simp,
end

instance f_of_f_is_hom : is_group_hom (f_of_h ∘ h_of_f) := is_group_hom.comp _ _

lemma f_of_f (f : F) : f_of_h (h_of_f f) = f := begin
  suffices g : f_of_h (h_of_f f) = to_group of f,
  rw g,
  exact to_group.of_eq _,
  apply to_group.unique (f_of_h ∘ h_of_f),
  intro x,
  simp,
  have p : h_of_f (of x) = ⟨pmul (to_loop x), by simp⟩, from to_group.of,
  rw p,
  have p : f_of_h ⟨pmul (to_loop x), by simp⟩ = f_of_g (pmul (to_loop x)), from rfl,
  rw [p, pmul_list, f_of_g.mk],
  have p : rmul r (list_from_path (to_loop x)) = mk (plist (path_from_list r (list_from_path (to_loop x))).2),
  refl,
  rw [p, path_from_path],
  simp,
  have p : to_loop x = pconcat (path.cons (tree_path (to_s x)) (to_edge x))
                        (prev $ tree_path (to_t x)),
  refl,
  rw [p, plist_concat, plist_rev_tp],
  simp,
  rw plist_tp,
  simp,
  rw [fem_unfold, dif_neg, r_from_r],
  refl,
  exact r,
end

lemma h_of_h : ∀ h : H, h_of_f (f_of_h h) = h
| ⟨x, hh⟩ := begin
  induction x with l,
  have p : f_of_h = f_of_g ∘ coe, from rfl, 
  rw p,
  rw subtype.ext,
  simp,
  rw f_of_g.mk,
  have h : rmul r l = mk (plist (path_from_list r l).2),
  refl,
  rw h,
  have q : mk l = mk (list_from_path (path_from_list r l).2),
  rw list_from_list r l,
  rw q,
  set pp := (path_from_list r l).2 with hpp,
  rw ←pmul_list,
  rw g_of_p,
  have h' : pmul (tree_path (path_from_list r l).1) = pmul (tree_path $ mk l • r),
  rw pfl_end r l,
  rw h',
  have hh' : mk l • r = r, from hh,
  rw hh',
  repeat {rw tree_path_root},
  simp,
  refl,
  exact r,
  simp, -- TODO: ???
end

def isom : stabilizer G r ≃* free_group R
  := ⟨f_of_h, h_of_f, h_of_h, f_of_f, is_mul_hom.map_mul _⟩

@[simp] def rhs_of_lhs : Q × α ⊕ unit → Q ⊕ R
| (sum.inl (s, a)) := dite (is_in_tree ⟨s, (a,tt)⟩) 
  (λ _, sum.inl $ ite (is_in_dir_tree ⟨s, (a,tt)⟩) (of a • s) s)
  (λ hn, sum.inr $ (from_edge ⟨s, (a,tt)⟩ hn).1)
| (sum.inr ()) := sum.inl r

@[simp] def lhs_of_rhs : Q ⊕ R → Q × α ⊕ unit
| (sum.inl s) := dite (s = r) (λ _, sum.inr ())
  (λ hn, sum.inl (ite (proj $ nb_edge s hn).2 (nb s hn) s, (proj $ nb_edge s hn).1))
| (sum.inr ⟨⟨_, _, s, (a,b)⟩, _⟩) := sum.inl (s, a)

def lhs_of_lhs : ∀ x, lhs_of_rhs (rhs_of_lhs x) = x
| (sum.inl (s,a)) := dite (is_in_tree ⟨s, (a,tt)⟩)
begin
  intro pos,
  simp,
  rw dif_pos pos,
  simp,
  set e := edge.intro s (a,tt),
  cases (em $ is_in_dir_tree e) with vr rv,
  rw if_pos vr,
  cases vr with hn he,
  have p : mk [(a,tt)] = of a, from rfl,
  rw p at hn,
  rw dif_neg hn,
  rw sum.inl.inj_iff,
  set t := (my_closer_nbr (of a • s) hn).val,
  have hne : nb_edge (of a • s) hn_1 = t.2, from rfl,
  repeat {rw hne},
  have hnb : nb (of a • s) hn_1 = t.1, from rfl,
  have hv : t = ⟨s, e⟩, from he,
  have hp : proj t.2 = proj (⟨s, e⟩:inbhd (of a • s)).2,
  exact congr_arg (λ x : inbhd (of a • s), proj x.2) hv,
  repeat {rw hp},
  simp,
  rw hnb,
  rw hv,

  rw if_neg rv,
  have h : is_in_dir_tree (rev e),
  cases pos with le ri,
  exact false.elim (rv le),
  assumption,
  cases h with hn he,
  rw dif_neg hn,
  rw sum.inl.inj_iff,
  set t := (my_closer_nbr s hn).val,
  have hne : nb_edge s hn = t.2, from rfl,
  repeat {rw hne},
  have hnb : nb s hn = t.1, from rfl,
  have hv : t = ⟨of a • s, rev e⟩, from he,
  have hp : proj t.2 = proj (⟨of a • s, rev e⟩ : inbhd s).2,
  exact congr_arg (λ x : inbhd s, proj x.2) hv,
  repeat {rw hp},
  simp,
end begin
  intro neg,
  simp,
  rw dif_neg neg,
  rw from_edge_unfold,
  rw dif_pos,
  swap,
  simp,
  simp,
  have h : rmk s (mk [(a,tt)] • s) ⟨s, (a,tt)⟩ neg (by simp) = ⟨⟨s, of a • s, s, (a,tt)⟩, neg, (by simp)⟩,
  refl,
  rw h,
  refl,
end
| (sum.inr ()) := by simp

def end_is_end : Π {s t} (e : edge s t), mk [proj e] • s = t
| _ _ ⟨_, _⟩ := rfl

def change_is_in_dir_tree : Π {s t t'} {e : edge s t}
  (h : t = t'), is_in_dir_tree (change_end h e) ↔ is_in_dir_tree e
| _ _ _ _ rfl := by refl

def change_is_in_tree : Π {s t t'} {e : edge s t}
  (h : t = t'), is_in_tree (change_end h e) ↔ is_in_tree e
| _ _ _ _ rfl := by refl

lemma nb.unique : Π {s s'} {h : s ≠ r} {h' : s' ≠ r} (he : s = s'), nb s h = nb s' h'
| _ _ _ _ rfl := rfl

def not_in_2_cycle (s) : Prop
  := ∀ (h : s ≠ r) (h' : nb s h ≠ r), s ≠ nb (nb s h) h'

lemma no_2_cycle : ∀ (s) (h : s ≠ r) (h' : nb s h ≠ r), s ≠ nb (nb s h) h'
  := @tree_recursion not_in_2_cycle (λ h, false.elim (h rfl)) begin
  intros t hn f hn' h' he,
  rw he at hn,
  apply f h' hn,
  apply nb.unique,
  cc,
end

def rhs_of_rhs : ∀ x, rhs_of_lhs (lhs_of_rhs x) = x
| (sum.inl s) := dite (s = r) (λ h, eq.rec (by simp) h.symm) begin
  intro hn,
  simp,
  rw dif_neg hn,
  cases (em $ (proj (nb_edge s hn)).2) with le ri,
  rw if_pos le,
  simp,
  have h : ((proj $ nb_edge s hn).1, tt) = proj (nb_edge s hn),
  ext,
  refl,
  simp,
  symmetry,
  assumption,
  rw h,
  set t := proj (nb_edge s hn),
  have p : mk [t] • (nb s hn) = s,
  exact end_is_end _,
  have he : edge.intro (nb s hn) t = change_end p.symm (nb_edge s hn),
  apply edge_ext,
  simp,
  have hd : is_in_dir_tree (edge.intro (nb s hn) t),
  rw he,
  rw change_is_in_dir_tree,
  use hn,
  exact sigma.eq rfl rfl,
  have ht : is_in_tree (edge.intro (nb s hn) t),
  exact or.inl hd,
  rw dif_pos ht,
  rw sum.inl.inj_iff,
  rw if_pos hd,
  rw ←h at p,
  exact p,

  rw if_neg ri,
  simp,
  have hp : ((proj $ nb_edge s hn).1, tt) = proj (rev $ nb_edge s hn),
    rw rev_proj,
    ext,
    have ha : ∀ x, (pbnot x).1 = x.1,
    intro x,
    cases x with a b,
    refl,
    rw ha,
    simp,
    symmetry,
    have ha : ∀ x, (pbnot x).2 = !x.2,
    intro x,
    cases x with a b,
    refl,
    rw ha,
    simp,
    exact bool_eq_false ri,
  have hm : mk [proj $ rev $ nb_edge s hn] • s = nb s hn,
  exact end_is_end _,
  rw hp,
  rw dif_pos,
  rw sum.inl.inj_iff,
  rw if_neg,
  intro h,
  cases h with hn' hh,
  have hs : nb (mk [proj $ rev $ nb_edge s hn] • s) hn' = s,
  exact congr_arg _ hh,
  rw nb.unique hm at hs,
  swap,
  rw ←hm,
  assumption,
  apply no_2_cycle s,
  exact hs.symm,
  have he : edge.intro s (proj $ rev $ nb_edge s hn) = change_end hm.symm (rev $ nb_edge s hn),
  apply edge_ext,
  simp,
  rw he,
  rw change_is_in_tree,
  rw is_in_tree_rev,
  apply or.inl,
  use hn,
  exact sigma.eq rfl rfl,
end
| (sum.inr ⟨⟨_, _, s, (a, b)⟩, h, hh⟩) := begin
  simp,
  have hh' : b = tt, from hh,
  rw hh' at h,
  have h' : ¬is_in_tree ⟨s, (a, tt)⟩, from h,
  rw dif_neg h',
  rw sum.inr.inj_iff,
  rw from_edge_unfold,
  rw dif_pos,
  swap,
  simp,
  rw subtype.ext,
  simp,
  rw hh',
  refl,
end

def index_equiv : Q × α ⊕ unit ≃ Q ⊕ R
  := ⟨rhs_of_lhs, lhs_of_rhs, lhs_of_lhs, rhs_of_rhs⟩

end 