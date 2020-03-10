import group_theory.free_group 

open free_group function

universe u
variables {α : Type u} (H : set (free_group α)) [is_subgroup H]
  (G : Type u) [group G]

def freely_generates (S : set G) : Prop := bijective $ to_group $ @subtype.val G S

def is_freely_generated : Prop := ∃ S : set G, freely_generates G S

/--
No group can be free until all subgroups are free.
--/
theorem nielsen_schreier : is_freely_generated H := sorry