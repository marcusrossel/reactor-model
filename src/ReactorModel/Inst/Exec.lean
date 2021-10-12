import ReactorModel.Inst.PrecGraph

open Reactor
open Ports

namespace Inst

variable {ι υ} [ID ι] [Value υ]

-- The parameter `orig` is the ID of the reaction from which this change was initiated.
-- This is required to ensure that mutations stay within their reactor.
def appOfChange (σ₁ σ₂ : Reactor ι υ) (orig : ι) : Change ι υ → Prop
  | Change.port i v =>  
    σ₁ -[Cmp.prt, i := v]→ σ₂ -- Port propagation doesn't exist, because we're using relay reactions.
  | Change.state i v => 
    σ₁ -[Cmp.stv, i := v]→ σ₂

  -- "Connecting" means inserting a relay reaction.
  -- 
  -- The objects and IDs used in the below correspond to this illustration:
  -- The outer box is a reactor and the boxes within the colons are nested reactors.
  --     ____________________________________________________
  --    |iₚ/p₁  :   ________                 ________    :   |
  --    |       :  |i₁/rtr₁ |               |i₂/rtr₂ |   :   |
  --    |       :  |        |               |        |   :   |
  --    |       :  |     src|>---        ---|>dst    |   :   |
  --    |       :  |________|   |        |  |________|   :   |
  --    |       :               |        |               :   |
  --    |       ::::::::::::::::|::::::::|::::::::::::::::   |
  --    |                       |  ____  |                   |
  --    |                       --|____|--                   |
  --    |____________________________________________________|
  --
  | Change.connect src dst =>  
    ∃ (iₚ i₁ i₂ i : ι) (p₁ p₂ rtr₁ rtr₂ : Reactor ι υ), 
      σ₁ *[Cmp.rtr] iₚ = p₁ ∧
      σ₁ & i₁ = iₚ ∧ -- We don't need specidy that i₁ and i₂ identify a reactor, because the next two lines
      σ₁ & i₂ = iₚ ∧ -- implicitly require this.
      σ₁ & src = i₁ ∧ -- We don't need to check whether src and dst are out- and input ports respectively,
      σ₁ & dst = i₂ ∧ -- because the relay reaction below will only be valid if that is the case.
      (i ∉ p₁.rcns.ids) ∧ -- Checks that i is an ununsed ID. 
      p₂.rcns = p₁.rcns.update' i (Reaction.relay src dst) ∧ -- Inserts the required relay reaction.
      p₂.prios = p₁.prios.withIncomparable i ∧ -- Sets the priority of the relay reaction to *.
      p₂.ports = p₁.ports ∧ p₂.roles = p₁.roles ∧ p₂.state = p₁.state ∧ p₂.nest = p₁.nest ∧ 
      σ₁ -[Cmp.rtr, iₚ := p₂]→ σ₂
  
  | Change.disconnect src dst => sorry

  -- Marten's PhD thesis:
  -- "If CREATE is called at (t, m), then any reaction of the newly-created reactor
  -- and any reactor in its containment hierarchy that is triggered by • will execute
  -- at (t, m) also (see start in Algorithm 5), but not before the last mutation of
  -- the new reactor’s container has finished executing (see Section 2.6)."
  | Change.create rtr i =>
    σ₁ & i = none ∧ -- The ID `i` has to be new.
    ∃ (iₚ : ι) (p₁ p₂ : Reactor ι υ) (rcn₁ rcn₂ : Reaction ι υ),
      σ₁ & orig = iₚ ∧
      σ₁ *[Cmp.rtr] iₚ = p₁ ∧
      p₁.rcns orig = rcn₁ ∧
      rcn₂.children = rcn₁.children ∪ (Finset.singleton i) ∧
      rcn₂.deps = rcn₁.deps ∧ rcn₂.body = rcn₁.body ∧ rcn₂.triggers = rcn₁.triggers ∧ 
      p₂.rcns = p₁.rcns.update orig rcn₂ ∧
      p₂.nest = p₁.nest.update i rtr ∧ 
      p₂.ports = p₁.ports ∧ p₂.roles = p₁.roles ∧ p₂.state = p₁.state ∧ p₂.prios = p₁.prios ∧ 
      σ₁ -[Cmp.rtr, iₚ := p₂]→ σ₂
      -- TODO: Somehow trigger startup reactions (by modifying the queue?).

  -- Deletion takes place in the time-world.
  -- Hence, here we only make sure that the conditions for deletion are met:
  -- The deleted reactor has to be nested in the reactor whose mutation triggered the deletion.
  | Change.delete i =>
    ∃ (iₚ : ι) (p : Reactor ι υ),
      σ₁ & orig = iₚ ∧
      σ₁ *[Cmp.rtr] iₚ = p ∧ 
      p *[Cmp.rtr] i ≠ none -- `p & i ≠ none` does not suffice here
      -- TODO: Somehow trigger shutdown reactions (by modifying the queue?).
      -- TODO: Remove `i` from the children of the respective reaction.

notation σ₁:max " -[" c ", " orig "]→ " σ₂:max => appOfChange σ₁ σ₂ orig c

def appOfOutput (σ₁ σ₂ : Reactor ι υ) (orig : ι) : List (Change ι υ) → Prop
  | [] => σ₁ = σ₂
  | hd::tl => ∃ σₘ, (σ₁ -[hd, orig]→ σₘ) ∧ (appOfOutput σₘ σ₂ orig tl)

notation σ₁:max " -[" o ", " orig "]→ " σ₂:max => appOfOutput σ₁ σ₂ orig o

def execOfRcn (σ₁ σ₂ : Reactor ι υ) (i : ι) : Prop :=
  ∃ (iₚ : ι) (ctx : Reactor ι υ) (rcn : Reaction ι υ),
    σ₁ & i = iₚ ∧
    σ₁ *[Cmp.rtr] iₚ = ctx ∧
    ctx.rcns i = rcn ∧
    let out := rcn (ctx.ports' Role.in) ctx.state
    σ₁ -[out, i]→ σ₂

notation σ₁ " -[" rcn "]→ " σ₂:max => execOfRcn σ₁ σ₂ rcn

def execOfQueue (σ₁ σ₂ : Reactor ι υ) : List ι → Prop
  | [] => σ₁ = σ₂
  | hd::tl => ∃ σₘ, (σ₁ -[hd]→ σₘ) ∧ (execOfQueue σₘ σ₂ tl)
  
notation σ₁:max " -[" q "]→ " σ₂:max => execOfQueue σ₁ σ₂ q

inductive exec (σ₁ σ₂ : Reactor ι υ) (remIn remOut : List ι) : Prop
  -- An execution is *short* if it does not cross the boundary of a logical
  -- time step. That is, it only processes reactions from the input remainer (`remIn`)
  -- and does not require the generation of a new reaction queue.
  | short (_ :
      -- TODO: 
      -- This definition enables a trivial partial execution: `l % σ₁ →ₑ σ₁ l`.
      -- Is this ok? If not, will `¬l.empty` solve it?
      ∃ (l : List ι),
        remIn = l ++ remOut ∧
        σ₁ -[l]→ σ₂
    )
  -- An execution is *long* if it crosses the boundary of a logical time step.
  -- That is, it processes all of the reactions from the input remainer (`remIn`),
  -- as well as reactions from the following new reaction queue.
  | long (_ :
      -- TODO:
      -- A consequence of requirement (1) is that the reactions enqueued in a
      -- remainder list can never be from different instantaneous exections.
      -- Hence, any (permitted) reordering within a remainder list will simply
      -- be equivalent to producing a different topological ordering of the
      -- precedence graph generated for that instantaneous step.
      -- So this probably enforces barrier synchronization again.
      -- On the other hand, if we want to allow the generation of a new precedence graph
      -- and derived reaction queue *before* all prior reactions have been executed,
      -- we probably need to figure out what constraints are required for this to be
      -- allowed. 
      -- Perhaps we only need to ensure that all previous mutations have run?
      -- Note, that figuring out when a new precedence graph can be created is not
      -- the same as figuring out in what way the time barrier can be crossed (i.e.
      -- in what way the remainder-queue can be reordered).
      -- If it is in fact the case that all previous mutations have to have run, 
      -- before we can create a new precedence graph, then this puts a bound on the
      -- time range of the reactions that can accumulate in the remainder queue.
      -- Specifically, (assuming requirement (1) will is resolved) they can only come
      -- from two consecutive instantaneous executions (unless we are able to reorder
      -- the remainder queue such that reactions can precede their mutations).
      -- The pattern being: [remaining rcns from step n, mutations from step n + 1, reactions from step n + 1].
      -- Perhaps this means that mutations enforce barrier sync - 
      -- unless we consider which mutations are actually triggered.
      -- E.g. assuming the following remainder queue:
      -- [a1, a2, a3, m1, m2, b1, b2, b3]
      -- Assuming that m1 and m2 are not triggered by the current port assigment,
      -- and additionally assuming that a1, a2 and a3 don't have a connection to m1 and m2,
      -- then we can deduce that m1 and m2 won't be triggered, therefore removing them from
      -- the queue. Aside from opening the possiblity for more reordering in the remainder queue,
      -- this also implies that we can generate a new prec graph.
      --
      -- Is it a problem, that all of the reactions are accumulating in *one* remainder queue?
      -- What happens when we ignore mutations?
      ∃ (σₘ : Reactor ι υ) (π : PrecGraph σₘ) (l : List ι),
        σ₁ -[remIn]→ σₘ ∧ -- (1) 
        π.isAcyclic ∧ 
        (l ++ remOut).isCompleteTopoOver π ∧  
        σₘ -[l]→ σ₂
    ) 

notation i:max " % " σ₁:max "→" σ₂:max " % " o:max => exec σ₁ σ₂ i o

end Inst