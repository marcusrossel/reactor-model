import ReactorModel.Components.Change

open Classical

@[ext]
structure Reaction.Input where
  ports : ID ⇉ Value
  acts : ID ⇉ Value
  state : ID ⇉ Value
  tag : Time.Tag

-- Reactions are the components that can produce changes in a reactor system.
-- The can be classified into "normal" reactions and "mutations". The `Reaction`
-- type encompasses both of these flavors (cf. `isNorm` and `isMut`).
--
-- The `deps` field defines both dependencies and antidependencies by referring to
-- the ports' IDs and separating these IDs by the role of the port they refer to.
--
-- A reaction's `triggers` are a subset of its input ports (by `tsSubInDeps`).
-- This field is used to define when a reaction triggers (cf. `triggersOn`).
--
-- The `outDepOnly` represents a constraint on the reaction's `body`.
open Reaction in
@[ext]
structure Reaction where
  deps :          Kind → Finset ID
  triggers :      Finset ID
  prio :          Priority
  body :          Input → List Change
  tsSubInDeps :   triggers ⊆ deps .in
  prtOutDepOnly : ∀ i v,   (o ∉ deps .out) → (.port o v) ∉ body i
  actOutDepOnly : ∀ i t v, (o ∉ deps .out) → (.action o t v) ∉ body i
  actNotPast :    (.action a t v) ∈ body i → i.tag.time ≤ t
  stateLocal :    (.state s v) ∈ body i → s ∈ i.state.ids
  
namespace Reaction

-- A coercion so that reactions can be called directly as functions.
-- So when you see something like `rcn p s` that's the same as `rcn.body p s`.
instance : CoeFun Reaction (λ _ => Input → List Change) where
  coe rcn := rcn.body

-- A reaction is normal ("norm") if its body produces no mutating changes.
def isNorm (rcn : Reaction) : Prop :=
  ∀ {i c}, (c ∈ rcn i) → ¬c.mutates 

-- A reaction is a mutation if it is not "normal", i.e. it does produce
-- mutating changes for some input.
def isMut (rcn : Reaction) : Prop := ¬rcn.isNorm

-- A reaction is pure if it does not interact with its container's state.
structure isPure (rcn : Reaction) : Prop where
  input : ∀ i s, rcn i = rcn { i with state := s }
  output : (c ∈ rcn.body i) → c.isPort ∨ c.isAction

theorem isMut_not_isPure (rcn : Reaction) : rcn.isMut → ¬rcn.isPure := by
  intro hm ⟨_, ho⟩
  simp [isMut, isNorm] at hm
  have ⟨_, c, hb, _⟩ := hm
  specialize ho hb
  cases ho <;> cases c <;> simp [Change.mutates] at *    
  
-- The condition under which a given reaction triggers on a given (input) port-assignment.
def triggersOn (rcn : Reaction) (i : Input) : Prop :=
  ∃ t v, (t ∈ rcn.triggers) ∧ (i.ports t = some v) ∧ (v.isPresent)
  
-- Relay reactions are a specific kind of reaction that allow us to simplify what
-- it means for reactors' ports to be connected. We can formalize connections between
-- reactors' ports by creating a reaction that declares these ports and only these
-- ports as dependency and antidependency respectively, and does nothing but relay the
-- value from its input to its output.
noncomputable def relay (src dst : ID) : Reaction := {
  deps := λ r => match r with | .in => Finset.singleton src | .out => Finset.singleton dst,
  triggers := Finset.singleton src,
  prio := none,
  body := λ i => match i.ports src with | none => [] | some v => [.port dst v],
  tsSubInDeps := by simp,
  prtOutDepOnly := by
    intro _ i 
    cases hs : i.ports src <;> simp_all [Option.elim, hs, Finset.not_mem_singleton]
  actOutDepOnly := by
    intro _ i
    cases hs : i.ports src <;> simp [Option.elim, hs]
  actNotPast := by
    intro i _ _ _ h
    cases hs : i.ports src <;> simp [hs] at h,
  stateLocal := by
    intro i _ _ h
    cases hs : i.ports src <;> simp [hs] at h
}

theorem relay_isPure (i₁ i₂) : (Reaction.relay i₁ i₂).isPure := {
  input := by simp [relay],
  output := by intro _ i h; cases hc : i.ports i₁ <;> simp_all [relay, hc, h]
}

end Reaction