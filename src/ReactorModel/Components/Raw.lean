import ReactorModel.Primitives

open Ports

namespace Raw

-- This block mainly serves the purpose of defining `Raw.Reactor`.
-- We later define an extension of `Raw.Reactor` called `Reactor`, which adds
-- all of the necessary constraints on it subcomponents.
-- Those subcomponents are then (re-)defined as well, by using the definition
-- of `Reactor`.
--
-- For more information on the use case of each component, cf. the definitions
-- of their non-`Raw` counterparts.
--
-- Side note:
-- The type class instances required by all types are named (`i` and `v`). This 
-- is necessary as Lean requires all type-level parameters of mutually inductive
-- definitions to have the same name. (So the `ι` and `υ` parameters also need to have
-- the same name across all definitions.)
mutual 

protected inductive Change (ι υ) [v : Value υ]
  | port (target : ι) (value : υ)
  | state (target : ι) (value : υ)
  | connect (src : ι) (dst : ι)
  | disconnect (src : ι) (dst : ι)
  | create (rtr : Raw.Reactor ι υ) (id : ι)
  | delete (rtrID : ι)

protected inductive Reaction (ι υ) [v : Value υ]
  | mk 
    (deps : Ports.Role → Finset ι) 
    (triggers : Finset ι)
    (children : Finset ι)
    (body : Ports ι υ → StateVars ι υ → List (Raw.Change ι υ))

protected inductive Reactor (ι υ) [v : Value υ]
  | mk 
    (ports : Ports ι υ) 
    (roles : ι ▸ Ports.Role)
    (state : StateVars ι υ)
    (rcns : ι → Option (Raw.Reaction ι υ))
    (nest : ι → Option (Raw.Reactor ι υ))
    (prios : PartialOrder ι)

-- This is a sanity check, to make sure that the above definition of reactors
-- actually allows them to be constructed.
deriving Inhabited

end

end Raw

-- We add some basic necessities for raw components, so that they are more 
-- comfortable to work with in the process of defining "proper" components.
-- We try to limit these conveniences though, as they are superfluous as soon
-- as we have "proper" components.

variable {ι υ} [Value υ]

-- Cf. `Change.mutates`.
def Raw.Change.mutates : Raw.Change ι υ → Prop
  | port _ _       => False
  | state _ _      => False
  | connect _ _    => True
  | disconnect _ _ => True
  | create _ _     => True
  | delete _       => True

namespace Raw.Reaction

-- These definitions give us the projections that would usually be generated for a structure.
def deps :     Raw.Reaction ι υ → (Ports.Role → Finset ι)                             | mk d _ _ _ => d
def triggers : Raw.Reaction ι υ → Finset ι                                            | mk _ t _ _ => t
def children : Raw.Reaction ι υ → Finset ι                                            | mk _ _ c _ => c
def body :     Raw.Reaction ι υ → (Ports ι υ → StateVars ι υ → List (Raw.Change ι υ)) | mk _ _ _ b => b

-- Cf. `Reaction.isNorm`.
def isNorm (rcn : Raw.Reaction ι υ) : Prop :=
  ∀ i s c, c ∈ (rcn.body i s) → ¬c.mutates

-- Cf. `Reaction.isMut`.
def isMut (rcn : Raw.Reaction ι υ) : Prop :=
  ¬rcn.isNorm

end Raw.Reaction

namespace Raw.Reactor

-- These definitions give us the projections that would usually be generated for a structure.
def ports : Raw.Reactor ι υ → Ports ι υ                       | mk p _ _ _ _ _ => p
def roles : Raw.Reactor ι υ → (ι ▸ Ports.Role)                | mk _ r _ _ _ _ => r
def state : Raw.Reactor ι υ → StateVars ι υ                   | mk _ _ s _ _ _ => s 
def rcns :  Raw.Reactor ι υ → (ι → Option (Raw.Reaction ι υ)) | mk _ _ _ r _ _ => r
def nest :  Raw.Reactor ι υ → (ι → Option (Raw.Reactor ι υ))  | mk _ _ _ _ n _ => n
def prios : Raw.Reactor ι υ → PartialOrder ι                  | mk _ _ _ _ _ p => p 

-- Cf. `Reactor.ports'`.
noncomputable def ports' (rtr : Raw.Reactor ι υ) (r : Ports.Role) : Ports ι υ := 
  rtr.ports.filter (λ i => rtr.roles i = r)

-- An extensionality theorem for `Raw.Reactor`.
theorem ext_iff {rtr₁ rtr₂ : Raw.Reactor ι υ} : 
  rtr₁ = rtr₂ ↔ 
  rtr₁.ports = rtr₂.ports ∧ rtr₁.roles = rtr₂.roles ∧
  rtr₁.state = rtr₂.state ∧ rtr₁.rcns  = rtr₂.rcns ∧
  rtr₁.nest  = rtr₂.nest  ∧ rtr₁.prios = rtr₂.prios := by
  apply Iff.intro
  case mp =>
    intro h
    cases rtr₁
    cases rtr₂
    simp [h]
  case mpr =>
    intro h
    simp [ports, roles, state, rcns, nest, prios] at h
    cases rtr₁
    cases rtr₂
    simp [h]

-- We need this additional theorem as the `ext` attribute can only be used on theorems proving an equality.
@[ext]
theorem ext {rtr₁ rtr₂ : Raw.Reactor ι υ} :
  rtr₁.ports = rtr₂.ports ∧ rtr₁.roles = rtr₂.roles ∧ 
  rtr₁.state = rtr₂.state ∧ rtr₁.rcns  = rtr₂.rcns ∧ 
  rtr₁.nest  = rtr₂.nest  ∧ rtr₁.prios = rtr₂.prios → 
  rtr₁ = rtr₂ :=
  λ h => ext_iff.mpr h  

end Raw.Reactor