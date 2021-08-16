import ReactorModel.Primitives
import ReactorModel.LGraph

open Reactor
open Reactor.Ports

structure NetworkEdge (ι) := 
  (src : ι)
  (dst : ι)

instance (ι) : LGraph.Edge (NetworkEdge ι) ι := 
  ⟨NetworkEdge.src, NetworkEdge.dst⟩

namespace Component

mutual 

inductive MutationOutput (ι υ)
  | mk
    (prtVals : Ports ι υ)
    (state   : StateVars ι υ)
    (newCns  : List (ι × ι))
    (delCns  : List (ι × ι))
    (newRtrs : List (Reactor ι υ))
    (delRtrs : Finset ι)

inductive Mutation (ι υ)
  | mk 
    (deps : Ports.Role → Finset ι) 
    (triggers : Finset ι)
    (body : Ports ι υ → StateVars ι υ → MutationOutput ι υ)
    (tsSubInDeps : triggers ⊆ deps Role.in)
    -- (inDepOnly : ∀ {i i'} s, (i =(deps Role.in)= i') → body i s = body i' s)
    -- (outPrtValsDepOnly : ∀ i s {o}, (o ∉ deps Role.out) → (body i s).at o = none)) 

inductive Reactor (ι υ)
  | mk 
    (ports : Ports.Role → Ports ι υ) 
    (state : StateVars ι υ)
    (rcns : ι ⇀ Mutation ι υ)
    (muts : ι ⇀ Mutation ι υ)
    -- (prioRel : PartialOrder ι)
    (nest : Network ι υ)
    -- (wf_rcn_deps : ∀ {rcn : reaction d} (h : rcn ∈ rcns.values) (r : ports.role), (rcn.deps r) ⊆ (prts r).ids)
    -- (wf_mut_deps : ∀ {m : mutation d} (h : m ∈ muts.values) (r : ports.role), (m.deps r) ⊆ (prts r).ids)

inductive Network (ι υ)
  | mk [l : LGraph.Edge (NetworkEdge ι) ι]
    (nodes : ι ⇀ (Reactor ι υ))
    (edges : Finset (NetworkEdge ι))

end

-- This is just a sanity check, to make sure that this definition of reactors actually allows them to be constructed.
instance : Inhabited (Reactor ι υ) where
  default := Reactor.mk Inhabited.default Inhabited.default Inhabited.default Inhabited.default (Network.mk Inhabited.default Inhabited.default)

end Component