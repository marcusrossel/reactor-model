import ReactorModel.Execution.Basic

open Classical

-- This file defines (and proves) determinism for the reactor model.
-- Determinism can be understood in multiple ways.
-- Primarily, we say the execution is deterministic if there is always ot most one timed
-- step that can be taken.
namespace Execution

theorem ChangeStep.mutates_comm {σ σ₁ σ₂ σ₁₂ σ₂₁ : Reactor} {c₁ c₂ : Change} {g : Time.Tag} : 
  (σ -[c₁, g]→ σ₁) → (σ₁ -[c₂, g]→ σ₁₂) → 
  (σ -[c₂, g]→ σ₂) → (σ₂ -[c₁, g]→ σ₂₁) → 
  c₁.mutates → σ₁₂ = σ₂₁ := by
  intro h₁ h₁₂ h₂ h₂₁ hm
  cases c₁ 
  <;> (simp only [Change.mutates] at hm) 
  <;> (
    cases c₂
    case port => 
      cases h₁; cases h₂; cases h₁₂; cases h₂₁
      exact Reactor.Update.Field.unique (by assumption) (by assumption)
    case state => 
      cases h₁; cases h₂; cases h₁₂; cases h₂₁
      exact Reactor.Update.unique (by assumption) (by assumption)
    case action => 
      cases h₁
      cases h₂
      case _ ht₁ _ =>
        cases h₁₂
        case _ ht₂ _ =>
          cases h₂₁
          rw [Reactor.isNewTag_unique ht₁ ht₂] at *
          exact Reactor.Update.Field.unique (by assumption) (by assumption)
  )
  <;> (cases h₁; cases h₂; cases h₁₂; cases h₂₁; rfl)
  
theorem ChangeStep.ne_comm {σ σ₁ σ₂ σ₁₂ σ₂₁ : Reactor} {c₁ c₂ : Change} {g : Time.Tag} : 
  (σ -[c₁, g]→ σ₁) → (σ₁ -[c₂, g]→ σ₁₂) → 
  (σ -[c₂, g]→ σ₂) → (σ₂ -[c₁, g]→ σ₂₁) → 
  (¬ c₁ ≊ c₂) → σ₁₂ = σ₂₁ := by
  intro h₁ h₁₂ h₂ h₂₁ hc
  by_cases hm : c₁.mutates ∨ c₂.mutates
  case pos =>
    cases hm
    case inl h => exact ChangeStep.mutates_comm h₁ h₁₂ h₂ h₂₁ h
    case inr h => exact Eq.symm $ ChangeStep.mutates_comm h₂ h₂₁ h₁ h₁₂ h
  case neg =>
    cases c₁ <;> cases c₂ <;> (simp only [not_or, Change.mutates, Change.EqKind] at *)
    case port.state =>
      cases h₁; case _ h₁ => cases h₁₂; case _ h₁₂ => cases h₂; case _ h₂ => cases h₂₁; case _ h₂₁ =>
        exact Reactor.Update.Field.ne_cmp_comm h₁ h₁₂ h₂ h₂₁ (by intro; contradiction)
    case state.port => 
      cases h₁; case _ h₁ => cases h₁₂; case _ h₁₂ => cases h₂; case _ h₂ => cases h₂₁; case _ h₂₁ =>
        exact Eq.symm $ Reactor.Update.Field.ne_cmp_comm h₂ h₂₁ h₁ h₁₂ (by intro; contradiction)
    case port.action =>
      cases h₁; case _ h₁ => cases h₁₂; case _ ht₁ h₁₂ => cases h₂; case _ h₂ => cases h₂₁; case _ ht₂ h₂₁ =>
      have h := Reactor.isNewTag_not_action_step_unique ht₂ ht₁ (ChangeStep.port h₁) (by simp)
      rw [h] at h₂
      exact Reactor.Update.Field.ne_field_comm h₁ h₁₂ h₂ h₂₁ (by intro; contradiction)
    case action.port =>
      cases h₁; case _ h₁ => cases h₁₂; case _ ht₁ h₁₂ => cases h₂; case _ h₂ => cases h₂₁; case _ ht₂ h₂₁ =>
      have h := Reactor.isNewTag_not_action_step_unique ht₁ ht₂ (ChangeStep.port h₂) (by simp)
      rw [h] at h₁
      exact Reactor.Update.Field.ne_field_comm h₁ h₁₂ h₂ h₂₁ (by intro; contradiction)
    case state.action =>
      cases h₁; case _ h₁ => cases h₁₂; case _ ht₁ h₁₂ => cases h₂; case _ h₂ => cases h₂₁; case _ ht₂ h₂₁ =>
      have h := Reactor.isNewTag_not_action_step_unique ht₂ ht₁ (ChangeStep.state h₁) (by simp)
      rw [h] at h₂
      exact Eq.symm $ Reactor.Update.Field.ne_cmp_comm h₂ h₂₁ h₁ h₁₂ (by intro; contradiction)
    case action.state =>
      cases h₁; case _ h₁ => cases h₁₂; case _ ht₁ h₁₂ => cases h₂; case _ h₂ => cases h₂₁; case _ ht₂ h₂₁ =>
      have h := Reactor.isNewTag_not_action_step_unique ht₁ ht₂ (ChangeStep.state h₂) (by simp)
      rw [h] at h₁
      exact Reactor.Update.Field.ne_cmp_comm h₁ h₁₂ h₂ h₂₁ (by intro; contradiction)

theorem ChangeStep.port_comm {σ σ₁ σ₂ σ₁₂ σ₂₁ : Reactor} {i₁ i₂ : ID} {v₁ v₂ : Value} {g : Time.Tag} : 
  (σ -[Change.port i₁ v₁, g]→ σ₁) → (σ₁ -[Change.port i₂ v₂, g]→ σ₁₂) → 
  (σ -[Change.port i₂ v₂, g]→ σ₂) → (σ₂ -[Change.port i₁ v₁, g]→ σ₂₁) → 
  (i₁ ≠ i₂) → σ₁₂ = σ₂₁ := by
  intro h₁ h₁₂ h₂ h₂₁ hi
  cases h₁; case _ h₁ => cases h₁₂; case _ h₁₂ => cases h₂; case _ h₂ => cases h₂₁; case _ h₂₁ =>
  exact Reactor.Update.Field.ne_id_comm h₁ h₁₂ h₂ h₂₁ hi

theorem ChangeStep.state_comm {σ σ₁ σ₂ σ₁₂ σ₂₁ : Reactor} {i₁ i₂ : ID} {v₁ v₂ : Value} {g : Time.Tag} : 
  (σ -[Change.state i₁ v₁, g]→ σ₁) → (σ₁ -[Change.state i₂ v₂, g]→ σ₁₂) → 
  (σ -[Change.state i₂ v₂, g]→ σ₂) → (σ₂ -[Change.state i₁ v₁, g]→ σ₂₁) → 
  (i₁ ≠ i₂) → σ₁₂ = σ₂₁ := by
  intro h₁ h₁₂ h₂ h₂₁ hi
  cases h₁; case _ h₁ => cases h₁₂; case _ h₁₂ => cases h₂; case _ h₂ => cases h₂₁; case _ h₂₁ =>
  exact Reactor.Update.ne_id_comm h₁ h₁₂ h₂ h₂₁ hi

theorem ChangeStep.action_comm {σ σ₁ σ₂ σ₁₂ σ₂₁ : Reactor} {i₁ i₂ : ID} {v₁ v₂ : Value} {t₁ t₂ : Time} {g : Time.Tag} : 
  (σ -[Change.action i₁ t₁ v₁, g]→ σ₁) → (σ₁ -[Change.action i₂ t₂ v₂, g]→ σ₁₂) → 
  (σ -[Change.action i₂ t₂ v₂, g]→ σ₂) → (σ₂ -[Change.action i₁ t₁ v₁, g]→ σ₂₁) → 
  (i₁ ≠ i₂) → σ₁₂ = σ₂₁ := by
  intro h₁ h₁₂ h₂ h₂₁ hi
  cases h₁; case _ g₁ ht₁ h₁ => cases h₁₂; case _ ht₁₂ h₁₂ => cases h₂; case _ g₂ ht₂ h₂ => cases h₂₁; case _ ht₂₁ h₂₁ =>
  have hs₁ := ChangeStep.action ht₁ h₁
  have hs₂ := ChangeStep.action ht₂ h₂
  have hu₁ := Reactor.isNewTag_action_step_ne_ids_unique ht₂ ht₁₂ hs₁ hi.symm
  have hu₂ := Reactor.isNewTag_action_step_ne_ids_unique ht₁ ht₂₁ hs₂ hi
  rw [←hu₁] at h₁₂
  rw [←hu₂] at h₂₁
  by_cases hc : g₁ = g₂
  case pos =>
    rw [hc] at h₁ h₂₁
    exact Reactor.Update.Field.ne_id_comm h₁ h₁₂ h₂ h₂₁ hi
  case neg =>
    exact Reactor.Update.Field.ne_field_comm h₁ h₁₂ h₂ h₂₁ (by simp [hc])
  
-- indep = no dependency from i to j or j to i + assume that reactions within a reactor are totally ordered
-- non-pure reactions have to be totally ordered in every scenario!

theorem ChangeListStep.indep_comm {σ σ₁ σ₂ σ₁' σ₂' : Reactor} {rcn₁ rcn₂ : Reaction} {i₁ i₂ : Reaction.Input} {g : Time.Tag} : 
  (σ -[rcn₁ i₁, g]→* σ₁) → (σ₁ -[rcn₂ i₂, g]→* σ₂) → 
  (σ -[rcn₂ i₂, g]→* σ₁') → (σ₁' -[rcn₁ i₁, g]→* σ₂') → -- This doesn't work. The inputs to the reactions have to be derived from the network, or do they?
  (True /-rcn₁ and rcn₂ are independent-/) → 
  σ₂ = σ₂' := sorry

theorem InstExecution.first_step {s₁ s₂ : State} (he : s₁ ⇓ᵢ+ s₂) : ∃ sₘ, s₁ ⇓ᵢ sₘ := by 
  cases he; case' single h, trans s₂ h _ => exact ⟨s₂, h⟩

theorem InstExecution.preserves_time {s₁ s₂ : State} :
  (s₁ ⇓ᵢ+ s₂) → s₁.ctx.time = s₂.ctx.time := by
  intro h
  induction h
  case single h => cases h <;> simp [Context.addCurrentExecuted_same_time]
  case trans s₁ s₂ _ h₁₂ h₂₃ hi => 
    have ht : s₁.ctx.time = s₂.ctx.time := by cases h₁₂ <;> simp [Context.addCurrentExecuted_same_time]
    simp [hi, ht]

theorem InstExecution.preserves_ctx_past_future {s₁ s₂ : State} :
  (s₁ ⇓ᵢ+ s₂) → ∀ g, g ≠ s₁.ctx.time → s₁.ctx.executedRcns g = s₂.ctx.executedRcns g := by
  intro h g hg
  induction h
  case single h => cases h <;> simp [Context.addCurrentExecuted, Finmap.update_ne]
  case trans s₁ s₂ _ he _ hi =>
    have hc : s₁.ctx.executedRcns g = s₂.ctx.executedRcns g := by cases he <;> simp [Context.addCurrentExecuted, Finmap.update_ne]
    rw [InstExecution.preserves_time $ single he] at hg
    simp [hc, hi hg]

-- This theorem is the main theorem about determinism in an instantaneous setting.
-- Basically, if the same reactions have been executed, then we have the same resulting
-- reactor.
protected theorem InstExecution.deterministic {s s₁ s₂ : State} : 
  (s ⇓ᵢ+ s₁) → (s ⇓ᵢ+ s₂) → (s₁.ctx = s₂.ctx) → s₁ = s₂ := by
  intro he₁ he₂ hc
  sorry

theorem State.instComplete_to_inst_stuck {s : State} :
  s.instComplete → ∀ s', ¬(s ⇓ᵢ s') := by
  intro h s' he
  cases he
  case' execReaction hi he _ _, skipReaction hi he _ =>
    have h' := Reactor.ids_def.mp hi
    have := he.unexeced
    rw [←h] at h'
    contradiction

theorem CompleteInstExecution.convergent_rcns {s s₁ s₂ : State} :
  (s ⇓ᵢ| s₁) → (s ⇓ᵢ| s₂) → s₁.rtr.ids Cmp.rcn = s₂.rtr.ids Cmp.rcn := by
  sorry

theorem CompleteInstExecution.convergent_ctx {s s₁ s₂ : State} :
  (s ⇓ᵢ| s₁) → (s ⇓ᵢ| s₂) → s₁.ctx = s₂.ctx := by
  intro hc₁ hc₂
  apply Context.ext_iff.mpr; apply Finmap.ext
  intro g
  by_cases hg : g = s.ctx.time
  case pos => 
    have h₁ := hc₁.complete |> Option.some_inj.mpr
    have h₂ := hc₂.complete |> Option.some_inj.mpr
    rw [Context.currentExecutedRcns_def] at h₁ h₂
    simp only [←hc₁.exec.preserves_time, ←hc₂.exec.preserves_time, ←hg] at h₁ h₂
    simp only [h₁, h₂, CompleteInstExecution.convergent_rcns hc₁ hc₂]
  case neg => simp only [←hc₁.exec.preserves_ctx_past_future g hg, hc₂.exec.preserves_ctx_past_future g hg]

theorem CompleteInstExecution.convergent {s s₁ s₂ : State} :
  (s ⇓ᵢ| s₁) → (s ⇓ᵢ| s₂) → s₁ = s₂ :=
  λ hc₁ hc₂ => InstExecution.deterministic hc₁.exec hc₂.exec $ CompleteInstExecution.convergent_ctx hc₁ hc₂

end Execution

theorem Execution.Step.time_monotone {s₁ s₂ : State} : 
  (s₁ ⇓ s₂) → s₁.ctx.time ≤ s₂.ctx.time := by
  intro h
  cases h
  case completeInst h => exact le_of_eq h.exec.preserves_time
  case advanceTime hg _ _ => exact le_of_lt $ s₁.ctx.advanceTime_strictly_increasing _ (s₁.time_lt_nextTag hg)

protected theorem Execution.Step.deterministic {s s₁ s₂ : State} : 
  (s ⇓ s₁) → (s ⇓ s₂) → s₁ = s₂ := by
  intro he₁ he₂
  cases he₁ <;> cases he₂
  case completeInst.completeInst hc₁ hc₂ => 
    exact CompleteInstExecution.convergent hc₁ hc₂
  case advanceTime.advanceTime g₁ hg₁ _ h₁ _ g₂ hg₂ _ h₂ => 
    simp only [hg₁, Option.some_inj] at hg₂
    simp [Reactor.eqWithClearedPortsUnique h₁ h₂, Context.advanceTime, hg₂]  
  case' completeInst.advanceTime hc _ _ _ hic _, advanceTime.completeInst _ _ _ hic _ hc => 
    cases hc.exec; case' single hi, trans hi _ => exact False.elim $ impossible_case_aux hi hic
where
  impossible_case_aux {s₁ s₂ : State} (hi : s₁ ⇓ᵢ s₂) (hic : s₁.instComplete) : False := by
    cases hi 
    case' execReaction hl hce _ _, skipReaction hl hce _ =>
      have := mt (Finset.ext_iff.mp hic _).mpr <| hce.unexeced
      have := Reactor.ids_def.mp hl
      contradiction

theorem Execution.time_monotone {s₁ s₂ : State} : 
  (s₁ ⇓* s₂) → s₁.ctx.time ≤ s₂.ctx.time := by
  intro h
  induction h 
  case refl => simp
  case step h _ hi => exact le_trans h.time_monotone hi

protected theorem Execution.deterministic {s s₁ s₂ : State} (hc₁ : s₁.instComplete) (hc₂ : s₂.instComplete) : 
  (s ⇓* s₁) → (s ⇓* s₂) → (s₁.ctx.time = s₂.ctx.time) → s₁ = s₂ := by
  intro he₁ he₂ ht
  induction he₁ <;> cases he₂ 
  case refl.refl => rfl
  case step.refl _ _ h₂₃ _ h₁₂ => exact False.elim $ impossible_case_aux hc₂ (Eq.symm ht) h₁₂ h₂₃
  case refl.step _ _ h₁₂ h₂₃ => exact False.elim $ impossible_case_aux hc₁ ht h₁₂ h₂₃
  case step.step s sₘ₁ s₁ h₁ₘ₁ hₘ₁₂ hi sₘ₂ h₁ₘ₂ hₘ₂₂ => 
    rw [Execution.Step.deterministic h₁ₘ₁ h₁ₘ₂] at hi
    exact hi hc₁ hₘ₂₂ ht
where 
  impossible_case_aux {s₁ s₂ s₃ : State} (hc : s₁.instComplete) (ht : s₁.ctx.time = s₃.ctx.time) :
    (s₁ ⇓ s₂) → (s₂ ⇓* s₃) → False := by
    intro h₁₂ h₂₃
    cases h₁₂
    case completeInst hi =>
      have ⟨sₘ, _⟩ := hi.exec.first_step
      have := (State.instComplete_to_inst_stuck hc) sₘ
      contradiction
    case advanceTime g hg _ _ => 
      have h := time_monotone h₂₃
      rw [←ht] at h
      simp only at h
      have h' := s₁.ctx.advanceTime_strictly_increasing g (s₁.time_lt_nextTag hg)
      have h'' := lt_of_le_of_lt h h'
      have := lt_irrefl _ h''
      contradiction