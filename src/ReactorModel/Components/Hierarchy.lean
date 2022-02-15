import ReactorModel.Components.Reactor.Properties
import ReactorModel.Time

open Classical

-- TODO: Redoc
-- TODO: Better notation for cmp.accessor σ, e.g. σ[cmp]

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

namespace Lineage

-- The "direct parent" in a lineage is the reactor which contains the target of the lineage.
-- This function returns that reactor along with its ID.
-- If the direct parent is the top-level reactor `σ`, then the ID is `⊤`.
def directParent {σ : Reactor} {i} : Lineage σ i → (Rooted ID × Reactor)
  | rtr _ => (⊤, σ)
  | rcn _ => (⊤, σ)
  | prt _ => (⊤, σ)
  | act _ => (⊤, σ)
  | stv _ => (⊤, σ)
  | nest σ' i' (rtr _) _ => (i', σ')
  | nest σ' i' (rcn _) _ => (i', σ')
  | nest σ' i' (prt _) _ => (i', σ')
  | nest σ' i' (stv _) _ => (i', σ')
  | nest _  _  l       _ => directParent l -- By case distinction `l` is a `Lineage.nest`.

def target {σ : Reactor} {i} : Lineage σ i → Cmp 
  | rtr _ => Cmp.rtr
  | rcn _ => Cmp.rcn
  | prt _ => Cmp.prt
  | act _ => Cmp.act
  | stv _ => Cmp.stv
  | nest _ _ l _ => target l

def fromCmp (σ : Reactor) (i) : (cmp : Cmp) → (h : i ∈ (cmp.accessor σ).ids) → Lineage σ i
  | Cmp.rtr, h => Lineage.rtr h
  | Cmp.rcn, h => Lineage.rcn h
  | Cmp.prt, h => Lineage.prt h
  | Cmp.act, h => Lineage.act h
  | Cmp.stv, h => Lineage.stv h

def retarget {σ : Reactor} {i} : (l : Lineage σ i) → (cmp : Cmp) → i ∈ (cmp.accessor l.directParent.snd).ids → Lineage σ i
  | nest σ' i' l' h', cmp, h => Lineage.nest σ' i' (retarget l' cmp h) h'
  | _, cmp, h => Lineage.fromCmp σ i cmp h


set_option maxHeartbeats 100000 in
theorem retarget_target (σ : Reactor) (i) (l : Lineage σ i) (cmp h) :
  (l.retarget cmp h).target = cmp := by sorry
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
  | Rooted.nested i => ∃ l : Lineage σ i, (cmp.accessor l.directParent.snd) i = o
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

theorem ids_def {σ : Reactor} {cmp : Cmp} {i : ID} {v : cmp.type} : 
  σ *[cmp, i]= v ↔ i ∈ σ.ids cmp := 
  sorry

-- Note, this only makes sense when talking about a top-level ID.
structure EqModID (σ₁ σ₂ : Reactor) (cmp : Cmp) (i : ID) : Prop where
  otherCmpsEq : ∀ {cmp'}, cmp' ≠ cmp → cmp'.accessor σ₁ = cmp'.accessor σ₂
  otherIDsEq : ∀ {i'}, i' ≠ i → cmp.accessor σ₁ i' = cmp.accessor σ₂ i'

notation σ₁:max " %[" cmp ", " i "]= " σ₂:max => EqModID σ₁ σ₂ cmp i

-- TODO: Find out how to solve the case distinction more concisely.
theorem EqModID.eq_from_eq_val_for_id {σ σ₁ σ₂ : Reactor} {cmp : Cmp} {i : ID} 
  (he₁ : σ %[cmp, i]= σ₁) (he₂ : σ %[cmp, i]= σ₂) :
  (cmp.accessor σ₁ i = cmp.accessor σ₂ i) → σ₁ = σ₂ := by
  intro ha
  apply ext
  have h_aux₁ : cmp.accessor σ₁ = cmp.accessor σ₂ := by
    apply Finmap.ext
    intro i'
    by_cases hc : i' = i
    case pos => simp only [hc, ha]
    case neg => simp only [he₁.otherIDsEq hc, Eq.symm $ he₂.otherIDsEq hc]
  have h_aux₂ : ∀ cmp', cmp' ≠ cmp → cmp'.accessor σ₁ = cmp'.accessor σ₂ := by
    intro cmp' hn
    have h := he₁.otherCmpsEq hn
    rw [he₂.otherCmpsEq hn] at h
    exact Eq.symm h
  cases cmp
  case a.rtr =>
    have h₀ := h_aux₁
    have h₁ := h_aux₂ Cmp.rcn (by intro; contradiction)
    have h₂ := h_aux₂ Cmp.prt (by intro; contradiction)
    have h₃ := h_aux₂ Cmp.act (by intro; contradiction)
    have h₄ := h_aux₂ Cmp.stv (by intro; contradiction)
    simp [h₀, h₁, h₂, h₃, h₄] 
  case a.rcn =>
    have h₀ := h_aux₁
    have h₁ := h_aux₂ Cmp.rtr (by intro; contradiction)
    have h₂ := h_aux₂ Cmp.prt (by intro; contradiction)
    have h₃ := h_aux₂ Cmp.act (by intro; contradiction)
    have h₄ := h_aux₂ Cmp.stv (by intro; contradiction)
    simp [h₀, h₁, h₂, h₃, h₄]
  case a.prt =>
    have h₀ := h_aux₁
    have h₁ := h_aux₂ Cmp.rtr (by intro; contradiction)
    have h₂ := h_aux₂ Cmp.rcn (by intro; contradiction)
    have h₃ := h_aux₂ Cmp.act (by intro; contradiction)
    have h₄ := h_aux₂ Cmp.stv (by intro; contradiction)
    simp [h₀, h₁, h₂, h₃, h₄]
  case a.act =>
    have h₀ := h_aux₁
    have h₁ := h_aux₂ Cmp.rtr (by intro; contradiction)
    have h₂ := h_aux₂ Cmp.prt (by intro; contradiction)
    have h₃ := h_aux₂ Cmp.rcn (by intro; contradiction)
    have h₄ := h_aux₂ Cmp.stv (by intro; contradiction)
    simp [h₀, h₁, h₂, h₃, h₄]
  case a.stv =>
    have h₀ := h_aux₁
    have h₁ := h_aux₂ Cmp.rtr (by intro; contradiction)
    have h₂ := h_aux₂ Cmp.prt (by intro; contradiction)
    have h₃ := h_aux₂ Cmp.rcn (by intro; contradiction)
    have h₄ := h_aux₂ Cmp.act (by intro; contradiction)
    simp [h₀, h₁, h₂, h₃, h₄]

inductive Update (cmp : Cmp) (v : cmp.type) : ID → Reactor → Reactor → Prop :=
  | top {i σ₁ σ₂} :
    (σ₁ %[cmp, i]= σ₂) →
    (cmp.accessor σ₁ i ≠ none) → -- This is required so that we know where to actually update i / so that there's at most one possible outcome of an update. 
    (cmp.accessor σ₂ i = v) → 
    Update cmp v i σ₁ σ₂
  | nested {i σ₁ σ₂} {j rtr₁ rtr₂} : 
    (σ₁ %[Cmp.rtr, j]= σ₂) →
    (σ₁.nest j = some rtr₁) →
    (σ₂.nest j = some rtr₂) →
    (Update cmp v i rtr₁ rtr₂) →
    Update cmp v i σ₁ σ₂

notation σ₁:max " -[" cmp ", " i " := " v "]→ " σ₂:max => Reactor.Update cmp v i σ₁ σ₂

theorem Update.requires_lineage_to_target {σ₁ σ₂ : Reactor} {cmp : Cmp} {i : ID} {v : cmp.type} (h : σ₁ -[cmp, i := v]→ σ₂) : Nonempty (Lineage σ₁ i) := by
  induction h
  case top i σ₁ _ _ ha _ => exact ⟨Lineage.fromCmp σ₁ i cmp $ Finmap.ids_def.mpr ha⟩
  case nested hn _ _ hi => exact ⟨Lineage.nest _ _ (Classical.choice hi) hn⟩

theorem Update.unique {σ σ₁ σ₂ : Reactor} {cmp : Cmp} {i : ID} {v : cmp.type} :
  (σ -[cmp, i := v]→ σ₁) → (σ -[cmp, i := v]→ σ₂) → σ₁ = σ₂ := by
  intro h₁ h₂
  (induction h₁ generalizing σ₂) <;> cases h₂
  case top.top _ he₁ _ hi₁ _ hi₂ he₂ => 
    rw [←hi₂] at hi₁
    exact EqModID.eq_from_eq_val_for_id he₁ he₂ hi₁
  case nested.nested i σ σ₁ j rtr₁ rtr₂ he₁ hn₁ hn₂ hu₁ hi j' rtr₁' rtr₂' hu₂ hn₁' hn₂' he₂ =>     
    let l₁ := Classical.choice hu₁.requires_lineage_to_target
    let l₁' := Classical.choice hu₂.requires_lineage_to_target
    let l₂ := Lineage.nest _ _ l₁ hn₁
    let l₂' := Lineage.nest _ _ l₁' hn₁'
    injection σ.uniqueIDs l₂ l₂' with _ hr _ hj
    rw [←hr] at hu₂
    have hi' := hi hu₂
    rw [hi', ←hn₂'] at hn₂
    rw [hj] at he₁ hn₂
    exact EqModID.eq_from_eq_val_for_id he₁ he₂ hn₂
  case top.nested i σ₁ _ _ ht _ _ _ _ hu hn _ _ =>
    let l₁ := Lineage.fromCmp σ₁ i cmp $ Finmap.ids_def.mpr ht
    let l₂ := Lineage.nest _ _ (Classical.choice hu.requires_lineage_to_target) hn
    have hc := σ₁.uniqueIDs l₁ l₂
    cases cmp <;> contradiction
  case nested.top i σ₁ _ _ _ _ _ hn _ hu _ ht _ _ =>
    let l₁ := Lineage.fromCmp σ₁ i cmp $ Finmap.ids_def.mpr ht
    let l₂ := Lineage.nest _ _ (Classical.choice hu.requires_lineage_to_target) hn
    have hc := σ₁.uniqueIDs l₁ l₂
    cases cmp <;> contradiction

theorem Update.reflects_in_objFor {σ₁ σ₂ : Reactor} {cmp : Cmp} {i : ID} {v : cmp.type} :
  (σ₁ -[cmp, i := v]→ σ₂) → σ₂ *[cmp, i]= v := by
  intro h
  induction h
  case top i _ σ₂ _ _ h =>
    simp only [objFor]
    have h' := Option.ne_none_iff_exists.mpr ⟨v, Eq.symm h⟩ |> Finmap.ids_def.mpr
    -- exists Lineage.fromCmp σ₂ i cmp h'
    sorry
    -- TODO: This used to work. Let's hope a newer Lean version can handle the `simp only [directParent]` again.
    -- cases cmp <;> simp only [Lineage.directParent, h]
  case nested i _ σ₂ j _ rtr₂ _ _ hn _ hi =>
    simp only [objFor] at *
    have ⟨l, hl⟩ := hi
    exists Lineage.nest rtr₂ j l hn
    have hp : l.directParent.snd = (Lineage.nest rtr₂ j l hn).directParent.snd := 
      sorry
      -- TODO: This used to work. Let's hope a newer Lean version can handle the `simp only [directParent]` again.
      -- by cases l <;> simp only [Lineage.directParent]
    simp [←hp, hl]

theorem Update.ne_cmp_and_ne_rtr_eq {σ₁ σ₂ : Reactor} {cmp : Cmp} {i : ID} {v : cmp.type} (cmp' : Cmp) :
  (σ₁ -[cmp, i := v]→ σ₂) → cmp' ≠ cmp → cmp' ≠ Cmp.rtr → cmp'.accessor σ₁ = cmp'.accessor σ₂ := by 
  intro hu _ _; cases hu <;> apply EqModID.otherCmpsEq <;> assumption

theorem Update.ne_cmp_comm (σ σ₁ σ₂ σ₁₂ σ₂₁ : Reactor) {cmp₁ cmp₂ : Cmp} {i₁ i₂ : ID} {v₁ : cmp₁.type} {v₂ : cmp₂.type} :
  (σ -[cmp₁, i₁ := v₁]→ σ₁) → (σ₁ -[cmp₂, i₂ := v₂]→ σ₁₂) →
  (σ -[cmp₂, i₂ := v₂]→ σ₂) → (σ₂ -[cmp₁, i₁ := v₁]→ σ₂₁) →
  (cmp₁ ≠ cmp₂) → 
  σ₁₂ = σ₂₁ :=
  sorry

theorem Update.ne_id_comm {σ σ₁ σ₂ σ₁₂ σ₂₁ : Reactor} {cmp₁ cmp₂ : Cmp} {i₁ i₂ : ID} {v₁ : cmp₁.type} {v₂ : cmp₂.type} :
  (σ -[cmp₁, i₁ := v₁]→ σ₁) → (σ₁ -[cmp₂, i₂ := v₂]→ σ₁₂) →
  (σ -[cmp₂, i₂ := v₂]→ σ₂) → (σ₂ -[cmp₁, i₁ := v₁]→ σ₂₁) →
  (i₁ ≠ i₂) → 
  σ₁₂ = σ₂₁ :=
  sorry

end Reactor

inductive Cmp.Field
  | prtVal -- Port value
  | act (g : Time.Tag) -- Action at tag

namespace Cmp.Field

abbrev cmp : Cmp.Field → Cmp 
  | prtVal => Cmp.prt
  | act .. => Cmp.act

abbrev type : Cmp.Field → Type _
  | prtVal => Value
  | act .. => Value

noncomputable def mkCmpObj : (f : Cmp.Field) → f.cmp.type → f.type → f.cmp.type
  | prtVal, c, v => { c .. with val := v }
  | act g, c, v => c.update g v

end Cmp.Field

namespace Reactor

def Update.Field (f : Cmp.Field) (v : f.type) (i : ID) (σ₁ σ₂ : Reactor) : Prop :=
  ∃ c, σ₁ *[f.cmp, i]= c ∧ σ₁ -[f.cmp, i := f.mkCmpObj c v]→ σ₂

notation σ₁:max " -[" f ", " i " := " v "]→ " σ₂:max => Reactor.Update.Field f v i σ₁ σ₂

theorem Update.Field.unique {σ σ₁ σ₂ : Reactor} {f : Cmp.Field} {i : ID} {v : f.type} :
  (σ -[f, i := v]→ σ₁) → (σ -[f, i := v]→ σ₂) → σ₁ = σ₂ :=
  sorry

theorem Update.Field.reflects_in_objFor {σ₁ σ₂ : Reactor} {f : Cmp.Field} {i : ID} {v : f.type} :
  (σ₁ -[f, i := v]→ σ₂) → ∃ c, σ₁ *[f.cmp, i]= c ∧ σ₂ *[f.cmp, i]= (f.mkCmpObj c v) :=
  λ ⟨c, hc, hu⟩ => ⟨c, hc, hu.reflects_in_objFor⟩

theorem Update.Field.ne_field_comm {σ σ₁ σ₂ σ₁₂ σ₂₁ : Reactor} {f₁ f₂ : Cmp.Field} {i₁ i₂ : ID} {v₁ : f₁.type} {v₂ : f₂.type} :
  (σ -[f₁, i₁ := v₁]→ σ₁) → (σ₁ -[f₂, i₂ := v₂]→ σ₁₂) →
  (σ -[f₂, i₂ := v₂]→ σ₂) → (σ₂ -[f₁, i₁ := v₁]→ σ₂₁) →
  (f₁ ≠ f₂) → 
  σ₁₂ = σ₂₁ :=
  sorry

theorem Update.Field.ne_cmp_comm {σ σ₁ σ₂ σ₁₂ σ₂₁ : Reactor} {f₁ : Cmp.Field} {cmp₂ : Cmp} {i₁ i₂ : ID} {v₁ : f₁.type} {v₂ : cmp₂.type} :
  (σ -[f₁, i₁ := v₁]→ σ₁) → (σ₁ -[cmp₂, i₂ := v₂]→ σ₁₂) →
  (σ -[cmp₂, i₂ := v₂]→ σ₂) → (σ₂ -[f₁, i₁ := v₁]→ σ₂₁) →
  (f₁.cmp ≠ cmp₂) → 
  σ₁₂ = σ₂₁ :=
  sorry

end Reactor