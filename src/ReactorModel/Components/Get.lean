import ReactorModel.Components.Reactor.Properties

open Classical 

-- An enumeration of the different *kinds* of components that are addressable by IDs in a reactor.
inductive Cmp
  | rtr -- Nested reactors
  | rcn -- Reactions
  | prt -- Port
  | act -- Actions
  | stv -- State variables

namespace Cmp 

-- The *type* corresponding to the component labeled by a given `Cmp`.
-- 
-- Note that the types for `prt` and `stv` are just `υ`, because IDs don't refer to
-- the entire entire mappinngs, but rather the single values within them.
abbrev type : Cmp → Type _
  | rtr => Reactor
  | rcn => Reaction
  | prt => Port
  | act => Time.Tag ▸ Value
  | stv => Value

-- Associates each type of component with the finmap in which it can be found inside
-- of a reactor. We use this in `objFor` to generically resolve the lookup for *some*
-- component and *some* ID.
abbrev accessor : (cmp : Cmp) → Reactor → ID ▸ cmp.type
  | rtr => Reactor.nest
  | rcn => Reactor.rcns
  | prt => Reactor.ports
  | act => Reactor.acts
  | stv => Reactor.state

end Cmp

namespace Reactor

abbrev cmp (σ : Reactor) (cmp : Cmp) : ID ▸ cmp.type := cmp.accessor σ

namespace Lineage

-- The "direct parent" in a lineage is the reactor which contains the target of the lineage.
-- This function returns that reactor along with its ID.
-- If the direct parent is the top-level reactor `σ`, then the ID is `⊤`.
def directParent {σ : Reactor} {i} : Lineage σ i → (Rooted ID × Reactor)
  | nest σ' i' n _ => 
    match n with 
    | nest _ _ l _ => directParent l 
    | _ => (i', σ')
  | _ => (⊤, σ)

def target {σ : Reactor} {i} : Lineage σ i → Cmp 
  | rtr _ => Cmp.rtr
  | rcn _ => Cmp.rcn
  | prt _ => Cmp.prt
  | act _ => Cmp.act
  | stv _ => Cmp.stv
  | nest _ _ l _ => target l

def fromCmp {σ : Reactor} {i} : (cmp : Cmp) → (h : i ∈ (σ.cmp cmp).ids) → Lineage σ i
  | Cmp.rtr, h => Lineage.rtr h
  | Cmp.rcn, h => Lineage.rcn h
  | Cmp.prt, h => Lineage.prt h
  | Cmp.act, h => Lineage.act h
  | Cmp.stv, h => Lineage.stv h

def retarget {σ : Reactor} {i} : (l : Lineage σ i) → (cmp : Cmp) → i ∈ (l.directParent.snd.cmp cmp).ids → Lineage σ i
  | nest σ' i' l' h', cmp, h => Lineage.nest σ' i' (retarget l' cmp h) h'
  | _, cmp, h => Lineage.fromCmp cmp h

set_option maxHeartbeats 100000 in
theorem retarget_target (σ : Reactor) (i) (l : Lineage σ i) (cmp h) :
  (l.retarget cmp h).target = cmp :=
  sorry
  -- TODO: This used to work. Let's hope a newer Lean version can handle the `simp only [directParent]` again.
  /-
  induction l 
  case nest σ σ' i i' l' hσ' hi =>  
    have hp : l'.directParent.snd = (nest σ' i' l' hσ').directParent.snd := 
      by cases l' <;> simp only [directParent]
    rw [←hp] at h
    simp only [←(hi h)]
    cases cmp <;> (simp only [target]; rfl)
  all_goals { cases cmp <;> simp only [target, retarget] }
  -/

theorem retarget_ne {σ : Reactor} {i} (l : Lineage σ i) {cmp} (h) :
  cmp ≠ l.target → l ≠ l.retarget cmp h := by 
  intro hn hc
  have h' := Lineage.retarget_target σ i l cmp h
  rw [←hc] at h'
  have := Eq.symm h'
  contradiction

end Lineage

-- The `containerOf` relation is used to determine whether a given ID `c`
-- identifies a reactor that contains a given object identified by ID `i`.
-- In other words, whether `c` identifies the parent of `i`.
-- The *kind* of component addressed by `i` is not required, as all IDs in
-- a reactor are unique (by `Reactor.uniqueIDs`).
--
-- Formalization:
-- We use the concept of lineages to "find" the path of reactor-IDs that leads
-- us through `σ` to `i`. If such a lineage exists we check whether `c` is the ID
-- of the last reactor in that path, because by construction (of lineages) *that* 
-- is the reactor that contains `i`.
-- Note that while `c` *can* be the top-level ID `⊤`, `i` can't.
-- We need to restrict `i` in this way, because `Lineage`s are only defined over
-- non-optional IDs. In practice, this isn't really a restriction though, because
-- we could easily extend the definition of `containerOf` to check whether `i = ⊤`
-- and yield `False` in that case (as the top-level reactor will never have a
-- parent container).
def containerOf (σ : Reactor) (i : ID) (c : Rooted ID) : Prop := 
  ∃ l : Lineage σ i, (l.directParent).fst = c 

-- This notation is chosen to be akin to the address notation in C.
notation σ:max " &[" i "]= " c:max => Reactor.containerOf σ i c

-- In the `containerOf` relation, any given ID can have at most one parent (`containerOf` is functional).
theorem containerOf_unique {σ : Reactor} {i : ID} {c₁ c₂ : Rooted ID} :
  σ &[i]= c₁ → σ &[i]= c₂ → c₁ = c₂ := by
  intro h₁ h₂
  have ⟨l₁, h₁⟩ := h₁
  have ⟨l₂, h₂⟩ := h₂
  simp [←h₁, ←h₂, σ.uniqueIDs l₁ l₂]

-- The `objFor` relation is used to determine whether a given ID `i` identifies
-- an object `o` of component type `cmp`.
--
-- Example: 
-- If `σ.objFor Cmp.rcn i x`, then:
-- * `σ` is the "context" (top-level) reactor.
-- * `i` is interpreted as being an ID that refers to a reaction (because of `Cmp.rcn`).
-- * `x` is the `Reaction` identified by `i`.
--
-- Formalization:
-- We use the concept of lineages to "find" the path of reactor-IDs that leads
-- us through `σ` to `i`. If such a lineage exists we obtain the last reactor in
-- that path (`l.directParent.snd`). From that reactor we try to obtain an object 
-- identified by `i` of component kind `cmp` (cf. `Cmp.accessor`).
-- We then check whether the given object `o` matches that object.
--
-- Technicalities:
-- The left side of the equality produces an optional value, as it is possible
-- that no value of component kind `cmp` is found for ID `i`.
-- Thus the right side is automatically lifted by Lean to `some o`. 
-- It *would* be possible to avoid this optionality, as a lineage for `i` always
-- contains a proof that `i` identifies an object in its parent reactor.
-- In this case the kind of lineage and given `cmp` would have to be matched, e.g. 
-- by adding an instance of `Cmp` into the type of `Lineage`.
-- This leads to heterogeneous equality though, and is therefore undesirable:
-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/.E2.9C.94.20Exfalso.20HEq
def objFor (σ : Reactor) (cmp : Cmp) (o : cmp.type) : Rooted ID → Prop
  | Rooted.nested i => ∃ l : Lineage σ i, (l.directParent.snd.cmp cmp) i = o
  | ⊤ => match cmp with | Cmp.rtr => HEq o σ | _ => False

-- This notation is chosen to be akin to the dereference notation in C.
notation σ:max " *[" cmp ", " i "]= " o:max => Reactor.objFor σ cmp o i

-- In the `objFor` relation, any given ID can have associated objects of at most one component type.
-- E.g. an ID cannot have associated objects of type `Cmp.rcn` *and* `Cmp.prt`.
-- Cf. `objFor_unique_obj` for further information.
theorem objFor_unique_cmp {σ : Reactor} {i : Rooted ID} {cmp₁ cmp₂ : Cmp} {o₁ : cmp₁.type} {o₂ : cmp₂.type} :
  (σ *[cmp₁, i]= o₁) → (σ *[cmp₂, i]= o₂) → cmp₁ = cmp₂ := by
  intro h₁ h₂
  cases i
  case root => cases cmp₁ <;> cases cmp₂ <;> simp only [objFor] at *
  case nested =>
    have ⟨l₁, h₁⟩ := h₁
    have ⟨l₂, h₂⟩ := h₂
    have hu := σ.uniqueIDs l₁ l₂
    rw [←hu] at h₂
    by_contra hc
    have h₁ := Finmap.ids_def'.mpr ⟨o₁, Eq.symm h₁⟩
    have h₂ := Finmap.ids_def'.mpr ⟨o₂, Eq.symm h₂⟩
    by_cases hc₁ : cmp₁ = l₁.target
    case neg =>
      have := Lineage.retarget_ne l₁ h₁ hc₁
      have := σ.uniqueIDs l₁ $ l₁.retarget cmp₁ h₁
      contradiction
    case pos =>
      by_cases hc₂ : cmp₂ = l₂.target
      case neg =>
        have := Lineage.retarget_ne l₂ h₂ hc₂
        have := σ.uniqueIDs l₂ $ l₂.retarget cmp₂ h₂
        contradiction
      case pos =>
        rw [hu] at hc₁
        rw [←hc₂] at hc₁
        contradiction

-- In the `objFor` relation, any given ID can have at most one associated object. 
--
-- Technicalities:
-- There are really two aspects of uniqueness that come together in `objFor`.
--
-- 1. Any given ID can have associated objects of at most one component type, as shown by `objFor_unique_cmp`.
-- 2. Any given ID can have a most one associated object of each component type, as shown here.
--
-- The result is that each ID can have at most one associated object, even across component types.
-- We do not show this together as this would involve using `HEq`.
-- If this is important though, the two theorems can be used in succession:
-- First, `objFor_unique_obj` can be used to establish equality of the component types.
-- After appropriate type casting (using the previous result), `objFor_unique_obj` can be used to show
-- object equality. 
theorem objFor_unique_obj {σ : Reactor} {i : ID} {cmp : Cmp} {o₁ o₂ : cmp.type} : 
  (σ *[cmp, i]= o₁) → (σ *[cmp, i]= o₂) → o₁ = o₂ := by
  intro h₁ h₂
  have ⟨l₁, h₁⟩ := h₁
  have ⟨l₂, h₂⟩ := h₂
  have hu := σ.uniqueIDs l₁ l₂
  rw [hu] at h₁
  simp [h₁] at h₂
  exact h₂

noncomputable def ids (σ : Reactor) (cmp : Cmp) : Finset ID :=
  let description := { i : ID | ∃ v, σ *[cmp, i]= v }
  let finite : description.finite := sorry
  finite.toFinset

theorem ids_def {σ : Reactor} {cmp : Cmp} {i : ID} : 
  (∃ v, σ *[cmp, i]= v) ↔ i ∈ σ.ids cmp := by
  constructor <;> (
    intro h
    simp only [ids, Set.finite.mem_to_finset] at *
    exact h
  )

end Reactor