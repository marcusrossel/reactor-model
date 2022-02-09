import ReactorModel.Components.Reaction

variable {ι υ} [Value υ]

-- TODO: Remove the fromRaw' theorems.

namespace Reactor 

-- `Reactor.fromRaw` is already defined as the name of `Reactor`'s constructor.

structure RawEquiv (rtr : Reactor ι υ) (raw : Raw.Reactor ι υ) : Prop where
  equiv : rtr.raw = raw

theorem RawEquiv.unique {rtr : Reactor ι υ} {raw₁ raw₂ : Raw.Reactor ι υ} (h₁ : RawEquiv rtr raw₁) (h₂ : RawEquiv rtr raw₂) : 
  raw₁ = raw₂ := by simp [←h₁.equiv, ←h₂.equiv]

theorem RawEquiv.fromRaw {raw : Raw.Reactor ι υ} (h) : RawEquiv (Reactor.fromRaw (raw := raw) h) raw :=
  { equiv := rfl }

theorem RawEquiv.fromRaw' {rtr : Reactor ι υ} {raw h} : 
  rtr = Reactor.fromRaw (raw := raw) h → RawEquiv rtr raw := 
  λ h => by simp [h, RawEquiv.fromRaw]

end Reactor

namespace Change

-- If we have a well-formed raw reactor `rtr` which contains a raw reaction `rcn`
-- which can produce a raw change `c`, then we can convert that raw change to a
-- "proper" change.
--
-- This conversion is trivial for all changes except `Change.create`, where we
-- have to turn a raw reactor into a "proper" reactor. That's why we need all
-- the auxiliary proofs as input.
def fromRaw
  {rtr : Raw.Reactor ι υ} (hw : rtr.wellFormed) 
  {rcn : Raw.Reaction ι υ} (hr : ∃ i, rtr.rcns i = rcn) 
  {raw : Raw.Change ι υ} {i} (hc : raw ∈ rcn.body i) : 
  Change ι υ :=
  match hm:raw with 
    | Raw.Change.port target value        => Change.port target value  
    | Raw.Change.state target value       => Change.state target value 
    | Raw.Change.action target time value => Change.action target time value 
    | Raw.Change.connect src dst          => Change.connect src dst    
    | Raw.Change.disconnect src dst       => Change.disconnect src dst 
    | Raw.Change.delete rtrID             => Change.delete rtrID
    | Raw.Change.create cr id => 
      let cr' := Reactor.fromRaw cr (by
          rw [hm] at hc
          have ha := Raw.Reactor.isAncestorOf.creatable hr.choose_spec hc
          exact Raw.Reactor.isAncestorOf_preserves_wf ha hw
      )
      Change.create cr' id

-- To ensure that `Change.fromRaw` performs a sensible transformation from
-- raw to "proper" changes, we define what it means for raw and "proper"
-- changes to be "equivalent" (they contain the same data).
-- This notion of equivalence is then used in `Change.fromRaw_rawEquiv` to
-- prove that `Change.fromRaw` produces only equivalent changes.
inductive RawEquiv : Change ι υ → Raw.Change ι υ → Prop
  | port       {t v} :                              RawEquiv (Change.port t v) (Raw.Change.port t v)
  | state      {t v} :                              RawEquiv (Change.state t v) (Raw.Change.state t v)
  | action     {t tm v} :                           RawEquiv (Change.action t tm v) (Raw.Change.action t tm v)
  | connect    {s d} :                              RawEquiv (Change.connect s d) (Raw.Change.connect s d)
  | disconnect {s d} :                              RawEquiv (Change.disconnect s d) (Raw.Change.disconnect s d)
  | create     {r r' i} : (Reactor.RawEquiv r r') → RawEquiv (Change.create r i) (Raw.Change.create r' i)
  | delete     {i} :                                RawEquiv (Change.delete i) (Raw.Change.delete i)

theorem RawEquiv.unique {c : Change ι υ} {raw₁ raw₂ : Raw.Change ι υ} (h₁ : RawEquiv c raw₁) (h₂ : RawEquiv c raw₂) : 
  raw₁ = raw₂ := by
  cases h₁ <;> cases h₂
  case create.create rtr r₁ _ he r₂ he' => simp only [Reactor.RawEquiv.unique he he']
  all_goals { rfl }

theorem RawEquiv.fromRaw {raw : Raw.Change ι υ} {rtr rcn i} (hw hr hc) :
  RawEquiv (@Change.fromRaw _ _ _ rtr hw rcn hr raw i hc) raw := by
  cases raw <;> simp [Change.fromRaw] <;> constructor
  exact Reactor.RawEquiv.fromRaw _
  
theorem RawEquiv.mutates_iff {c : Change ι υ} {raw : Raw.Change ι υ} (h : RawEquiv c raw) :
  c.mutates ↔ raw.mutates := by
  cases h <;> simp [mutates, Raw.Change.mutates]

end Change

namespace Reaction

-- If we have a well-formed raw reactor `rtr` which contains a raw reaction `rcn`,
-- then we can convert that raw reaction to a "proper" reaction.
-- In the process we map all raw changes producable by the raw reaction to "proper"
-- changes (using `Change.fromRaw`).
def fromRaw {rtr : Raw.Reactor ι υ} (hw : rtr.wellFormed) {raw : Raw.Reaction ι υ} (hr : ∃ i, rtr.rcns i = raw) : Reaction ι υ := {
  deps := raw.deps,
  triggers := raw.triggers,
  prio := raw.prio,
  children := raw.children,
  body := (λ i => (raw.body i).attach.map (λ c => Change.fromRaw hw hr c.property)),
  tsSubInDeps := (hw.direct.rcnsWF hr).tsSubInDeps,
  prtOutDepOnly := by
    intro i _ v ho hc
    simp [List.mem_map] at hc
    have := (hw.direct.rcnsWF hr).prtOutDepOnly i v ho
    have ⟨_, hc, he⟩ := hc
    have he' := Change.RawEquiv.fromRaw hw hr hc
    rw [←he] at he'
    cases he'
    contradiction,
  actOutDepOnly := by
    intro i _ t v ho hc
    simp [List.mem_map] at hc
    have := (hw.direct.rcnsWF hr).actOutDepOnly i t v ho
    have ⟨_, hc, he⟩ := hc
    have he' := Change.RawEquiv.fromRaw hw hr hc
    rw [←he] at he'
    cases he'
    contradiction,
  normNoChild := by
    intro ha
    have hn := (hw.direct.rcnsWF hr).normNoChild
    simp at ha
    simp [Raw.Reaction.isNorm] at hw
    suffices hg : ∀ i c, c ∈ raw.body i → ¬c.mutates from hn hg
    intro i c hc
    have ha := ha i (Change.fromRaw hw hr hc)
    simp only [List.mem_map] at ha
    have ha := ha (by
      let a : { x // x ∈ raw.body i } := ⟨c, hc⟩
      exists a
      simp [List.mem_attach]
    )
    have h := Change.RawEquiv.fromRaw hw hr hc
    exact mt (Change.RawEquiv.mutates_iff h).mpr ha
}

-- To ensure that `fromRaw` performs a sensible transformation from a raw
-- to a "proper" reaction, we define what it means for raw and "proper"
-- reactions to be "equivalent" (they contain the same data).
-- This notion of equivalence is then used in `fromRaw_rawEquiv` to
-- prove that `fromRaw` produces only equivalent reactions.
structure RawEquiv (rcn : Reaction ι υ) (raw : Raw.Reaction ι υ) : Prop :=
  deps :     rcn.deps = raw.deps
  triggers : rcn.triggers = raw.triggers
  prio :     rcn.prio = raw.prio
  children : rcn.children = raw.children
  body :     ∀ i, List.forall₂ Change.RawEquiv (rcn.body i) (raw.body i)

theorem RawEquiv.unique {rcn : Reaction ι υ} {raw₁ raw₂ : Raw.Reaction ι υ} (h₁ : RawEquiv rcn raw₁) (h₂ : RawEquiv rcn raw₂) : 
  raw₁ = raw₂ := by
  apply Raw.Reaction.ext
  simp [←h₁.deps, ←h₂.deps, ←h₁.triggers, ←h₂.triggers, ←h₁.prio, ←h₂.prio, ←h₁.children, ←h₂.children]
  funext i
  have hb₁ := h₁.body i
  have hb₂ := h₂.body i
  generalize hc : rcn.body i = c
  generalize hr₁ : raw₁.body i = cr₁
  generalize hr₂ : raw₂.body i = cr₂
  rw [hc, hr₁] at hb₁
  rw [hc, hr₂] at hb₂
  clear hc hr₁ hr₂  
  (induction c generalizing cr₁ cr₂)
  case a.h.nil => cases hb₁; cases hb₂; rfl
  case a.h.cons hd tl hi => 
    cases hb₁
    case cons hd₁ tl₁ hhd₁ htl₁ => 
      cases hb₂
      case cons hd₂ tl₂ hhd₂ htl₂ =>
        simp [Change.RawEquiv.unique hhd₁ hhd₂, hi tl₁ htl₁ tl₂ htl₂]

theorem RawEquiv.fromRaw {raw : Raw.Reaction ι υ} {rtr} (hw hr) :
  RawEquiv (@Reaction.fromRaw _ _ _ rtr hw raw hr) raw := {
    deps := by simp [Reaction.fromRaw],
    triggers := by simp [Reaction.fromRaw],
    prio := by simp [Reaction.fromRaw],
    children := by simp [Reaction.fromRaw],
    body := by
      intro i
      sorry
  }

theorem RawEquiv.fromRaw' {rcn : Reaction ι υ} {rtr raw hw hr} :
  rcn = @Reaction.fromRaw _ _ _ rtr hw raw hr → RawEquiv rcn raw :=
  λ h => by simp [h, RawEquiv.fromRaw]

theorem RawEquiv.isMut_iff {rcn : Reaction ι υ} {raw : Raw.Reaction ι υ} (h : RawEquiv rcn raw) :
  rcn.isMut ↔ raw.isMut := by
  constructor <;> (
    intro hm
    simp [isMut, isNorm, Raw.Reaction.isMut, Raw.Reaction.isNorm] at *
    have ⟨i, c, hc, hm⟩ := hm
    exists i
    have hb := h.body i
    generalize hcs : rcn.body i = cs
    generalize hrcs : raw.body i = rcs
  )
  case mp => 
    rw [hcs] at hb hc
    rw [hrcs] at hb
    clear hcs hrcs
    induction hb
    case nil => contradiction
    case cons hd hdr tl tlr he _ hi =>
      cases List.mem_cons.mp hc
      case inl hml =>
        rw [←hml] at he
        exact ⟨hdr, ⟨by simp, (Change.RawEquiv.mutates_iff he).mp hm⟩⟩
      case inr hmr => 
        have ⟨x, ⟨hx₁, hx₂⟩⟩ := hi hmr
        exact ⟨x, ⟨List.mem_cons.mpr $ Or.inr hx₁, hx₂⟩⟩
  case mpr => 
    rw [hcs] at hb 
    rw [hrcs] at hb hc
    clear hcs hrcs
    induction hb
    case nil => contradiction
    case cons hd hdr tl tlr he _ hi =>
      cases List.mem_cons.mp hc
      case inl hml =>
        rw [←hml] at he
        exact ⟨hd, ⟨by simp, (Change.RawEquiv.mutates_iff he).mpr hm⟩⟩
      case inr hmr => 
        have ⟨x, ⟨hx₁, hx₂⟩⟩ := hi hmr
        exact ⟨x, ⟨List.mem_cons.mpr $ Or.inr hx₁, hx₂⟩⟩

theorem RawEquiv.isNorm_iff {rcn : Reaction ι υ} {raw : Raw.Reaction ι υ} (h : RawEquiv rcn raw) :
  rcn.isNorm ↔ raw.isNorm := by
  have he := RawEquiv.isMut_iff h
  simp only [isMut, Raw.Reaction.isMut] at he
  have he := not_iff_not_of_iff he
  simp at he
  exact he

end Reaction
