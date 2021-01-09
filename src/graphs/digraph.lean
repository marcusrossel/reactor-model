import data.finset  

-- Associated discussion:
-- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Understanding.20Type.20Classes

-- Type `ε` is a `digraph.edge`-type over indices `ι`, if any instance of it can produce a `src`
-- and `dst` index.
class digraph.edge (ε ι : Type*) :=
  (src : ε → ι)
  (dst : ε → ι)

variables (ι δ : Type*) (ε : Π is : finset ι, ({ i // i ∈ is } → δ) → Type*)
variables [∀ i d, digraph.edge (ε i d) ι]

-- The vertices (of type `α`) have to have an associated index (of type `ι`), because otherwise it
-- wouldn't be possible to have multiple instances of the same reactor in a network.
-- Multisets are not enough, because then their edges can't be distinguished from one another.
--
-- A previous approach defined the nodes and indices together, as `ι → δ`. The nice thing about
-- this was that all indices of type `ι` were guaranteed to reference a vertex in the graph. The
-- problem with this though, is that you can't remove/add a vertex from/to the graph without
-- changing the underlying index-type `ι`. Hence the current approach which uses a `finset ι` is
-- used, so `ι` can stay the same. An inconvenience that arises as a result of this more flexible
-- approach is that functions over indices might have to require `(i : { x // x ∈ g.ids})` as
-- parameter instead of just `(i : ι)`.
structure digraph :=
  (ids : finset ι)
  (data : { i // i ∈ ids } → δ)
  (edges : finset (ε ids data))

variables {ι δ ε}

instance : has_mem δ (digraph ι δ ε) := {mem := λ d g, ∃ i, g.data i = d}

namespace digraph

  -- The proposition that a given digraph connects two given vertices with an edge.
  def has_edge_from_to (g : digraph ι δ ε) (i i' : ι) : Prop :=
    ∃ e ∈ g.edges, (edge.src e, edge.dst e) = (i, i')

  notation i-g->i' := g.has_edge_from_to i i'

  -- The proposition that a given digraph connects two given vertices by some path.
  inductive has_path_from_to (g : digraph ι δ ε) : ι → ι → Prop
    | direct {i i' : ι} : (i-g->i') → has_path_from_to i i'
    | composite {i iₘ i' : ι} : has_path_from_to i iₘ → has_path_from_to iₘ i' → has_path_from_to i i'

  notation i~g~>i' := g.has_path_from_to i i'

  -- The proposition that a given digraph is acyclic.
  def is_acyclic (g : digraph ι δ ε) := ∀ i, ¬ i~g~>i
      
  variable [decidable_eq ι]

  -- The in-degree of vertex `i` in digraph `g`. 
  def in_degree_of (g : digraph ι δ ε) (i : { x // x ∈ g.ids}) : ℕ :=
    (g.edges.filter (λ e, edge.dst e = i.val)).card

end digraph 









