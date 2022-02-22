import ReactorModel.Execution.Basic

open Classical

-- This file defines (and proves) determinism for the reactor model.
-- Determinism can be understood in multiple ways.
-- Primarily, we say the execution is deterministic if there is always ot most one timed
-- step that can be taken.
namespace Execution

theorem ChangeStep.mutates_comm {σ σ₁ σ₂ σ₁₂ σ₂₁ : Reactor} {rcn₁ rcn₂ : ID} {c₁ c₂ : Change} :
  (σ -[rcn₁:c₁]→ σ₁) → (σ₁ -[rcn₂:c₂]→ σ₁₂) →
  (σ -[rcn₂:c₂]→ σ₂) → (σ₂ -[rcn₁:c₁]→ σ₂₁) →
  c₁.mutates → σ₁₂ = σ₂₁ := by
  intro h₁ h₁₂ h₂ h₂₁ hm
  cases c₁
  <;> (simp only [Change.mutates] at hm)
  <;> (
    cases c₂
    case' port, state, action =>
      cases h₁; cases h₂; cases h₁₂; cases h₂₁
      exact Reactor.Update.unique' (by assumption) (by assumption)
  )
  <;> (cases h₁; cases h₂; cases h₁₂; cases h₂₁; rfl)

theorem ChangeStep.mutates_comm' {σ σ₁ σ₂ σ₁₂ σ₂₁ : Reactor} {rcn₁ rcn₂ : ID} {c₁ c₂ : Change} :
  (σ -[rcn₁:c₁]→ σ₁) → (σ₁ -[rcn₂:c₂]→ σ₁₂) →
  (σ -[rcn₂:c₂]→ σ₂) → (σ₂ -[rcn₁:c₁]→ σ₂₁) →
  (c₁.mutates ∨ c₂.mutates) → σ₁₂ = σ₂₁ := by
  intro h₁ h₁₂ h₂ h₂₁ hm
  cases hm
  case inl h => exact ChangeStep.mutates_comm h₁ h₁₂ h₂ h₂₁ h
  case inr h => exact (ChangeStep.mutates_comm h₂ h₂₁ h₁ h₁₂ h).symm

theorem ChangeStep.ne_cmp_comm {σ σ₁ σ₂ σ₁₂ σ₂₁ : Reactor} {rcn₁ rcn₂ : ID} {c₁ c₂ : Change} :
  (σ -[rcn₁:c₁]→ σ₁) → (σ₁ -[rcn₂:c₂]→ σ₁₂) →
  (σ -[rcn₂:c₂]→ σ₂) → (σ₂ -[rcn₁:c₁]→ σ₂₁) →
  (¬ c₁ ≈ c₂) → σ₁₂ = σ₂₁ := by
  intro h₁ h₁₂ h₂ h₂₁ hc
  by_cases hm : c₁.mutates ∨ c₂.mutates
  case pos => exact ChangeStep.mutates_comm' h₁ h₁₂ h₂ h₂₁ hm
  case neg =>
    cases c₁ <;> cases c₂ <;> (simp only [not_or, Change.mutates] at *) <;> (
      cases h₁; case _ h₁ => cases h₁₂; case _ h₁₂ => cases h₂; case _ h₂ => cases h₂₁; case _ h₂₁ =>
      simp [Reactor.Update.ne_cmp_ne_rtr_comm h₁ h₁₂ h₂ h₂₁ (by intro; contradiction) (by intro; contradiction) (by intro; contradiction)]
    )

theorem ChangeStep.indep_comm {σ σ₁ σ₂ σ₁₂ σ₂₁ : Reactor} {rcn₁ rcn₂ : ID} {c₁ c₂ : Change} :
  (σ -[rcn₁:c₁]→ σ₁) → (σ₁ -[rcn₂:c₂]→ σ₁₂) →
  (σ -[rcn₂:c₂]→ σ₂) → (σ₂ -[rcn₁:c₁]→ σ₂₁) →
  (∀ i₁ i₂, c₁.target = some i₁ → c₂.target = some i₂ → i₁ ≠ i₂) →
  σ₁₂ = σ₂₁ := by
  intro h₁ h₁₂ h₂ h₂₁ ht
  by_cases hm : c₁.mutates ∨ c₂.mutates
  case pos => exact ChangeStep.mutates_comm' h₁ h₁₂ h₂ h₂₁ hm
  case neg =>
    simp only [not_or] at hm
    have ⟨i₁, hi₁⟩ := mt (c₁.target_none_iff_mutates.mp) hm.left  |> Option.ne_none_iff_exists.mp
    have ⟨i₂, hi₂⟩ := mt (c₂.target_none_iff_mutates.mp) hm.right |> Option.ne_none_iff_exists.mp
    have ht' := ht i₁ i₂ hi₁.symm hi₂.symm
    have ht'' : c₁.target ≠ c₂.target := by simp [←hi₁, ←hi₂, ht']
    cases c₁ <;> cases c₂ <;> simp [Change.target] at ht''
    case' port.port, state.state, action.action =>
      cases h₁; case _ h₁ => cases h₁₂; case _ h₁₂ => cases h₂; case _ h₂ => cases h₂₁; case _ h₂₁ =>
      exact Reactor.Update.ne_id_ne_rtr_comm h₁ h₁₂ h₂ h₂₁ ht'' (by intro; contradiction)
    all_goals { exact ChangeStep.ne_cmp_comm h₁ h₁₂ h₂ h₂₁ (by intro; contradiction) }

theorem ChangeStep.unique {σ σ₁ σ₂ : Reactor} {rcn : ID} {c : Change} :
  (σ -[rcn:c]→ σ₁) → (σ -[rcn:c]→ σ₂) → σ₁ = σ₂ := by
  intro h₁ h₂
  cases h₁ <;> cases h₂
  case' port.port h₁ h₂, state.state h₁ h₂, action.action h₁ h₂ => exact Reactor.Update.unique' h₁ h₂
  all_goals { rfl }


theorem ChangeListStep.function {σ₁ σ₂ : Reactor} {cs : List Change} {rcn : ID} {i : ID} :
(σ₁ -[rcn:c]→ σ₂) →  ∃ u σ₂', σ₁ -[cmp:i u]→ σ₂' ∧ [] := by sorry


lemma ChangeListStep.split_changes {σ₁ σ₂ : Reactor} {cs cs₁ cs₂  : List Change} {rcn : ID}:
cs = cs₁ ++ cs₂ → ∃ σ, σ₁ -[rcn:cs₁]→* σ ∧ σ -[rcn:cs₂]→* σ₂ := by
sorry

/- Fo each cmp:i, the change of value either happens in cs₁ or in cs₂.
   This is expressed in the following two lemmas, that say that one of the two
   ChangeLists is a noop for cmp:i, one for the first step and one for the second
   step.
-/
lemma ChangeListStep.first_step_noop {σ σ₁ σ₂ σ₁₂ σ₂₁ : Reactor} {rcn₁ rcn₂ : ID} {cs₁ cs₂ : List Change} :
  (σ -[rcn₁:cs₁]→* σ₁) → (σ₁ -[rcn₂:cs₂]→* σ₁₂) →
  (σ -[rcn₂:cs₂]→* σ₂) → (σ₂ -[rcn₁:cs₁]→* σ₂₁) →
  (∀ c₁ c₂ i₁ i₂, c₁ ∈ cs₁ → c₂ ∈ cs₂ → c₁.target = some i₁ → c₂.target = some i₂ → i₁ ≠ i₂) →
  ∀ cmp i v, (σ *[cmp:i]= v → (σ₁ *[cmp:i]=v ∨ σ₂ *[cmp:i]=v)) := by
  sorry

lemma ChangeListStep.first_step_op {σ σ₁ σ₂ σ₁₂ σ₂₁ : Reactor} {rcn₁ rcn₂ : ID} {cs₁ cs₂ : List Change} :
  (σ -[rcn₁:cs₁]→* σ₁) → (σ₁ -[rcn₂:cs₂]→* σ₁₂) →
  (σ -[rcn₂:cs₂]→* σ₂) → (σ₂ -[rcn₁:cs₁]→* σ₂₁) →
  (∀ c₁ c₂ i₁ i₂, c₁ ∈ cs₁ → c₂ ∈ cs₂ → c₁.target = some i₁ → c₂.target = some i₂ → i₁ ≠ i₂) →
  ∀ cmp i v, (σ₁₂ *[cmp:i]= v → (σ₁ *[cmp:i]=v ∨ σ₂ *[cmp:i]= v)) := by
  sorry

lemma ChangeListStep.value_identical {σ σ₁ σ₂ σ₁₂ σ₂₁ : Reactor} {rcn₁ rcn₂ : ID} {cs₁ cs₂ : List Change} :
  (σ -[rcn₁:cs₁]→* σ₁) → (σ₁ -[rcn₂:cs₂]→* σ₁₂) →
  (σ -[rcn₂:cs₂]→* σ₂) → (σ₂ -[rcn₁:cs₁]→* σ₂₁) →
  (∀ c₁ c₂ i₁ i₂, c₁ ∈ cs₁ → c₂ ∈ cs₂ → c₁.target = some i₁ → c₂.target = some i₂ → i₁ ≠ i₂) →
  ∀ cmp i v, (σ₁₂ *[cmp:i]= v → σ₂₁ *[cmp:i]= v) := by
  intros h₁ h₁₂ h₂ h₂₁ ht cmp i v h₁₂v
  have Hop_step := first_step_op h₁ h₁₂ h₂ h₂₁ ht cmp i v h₁₂v
  cases Hop_step
  case inl Hv =>
   {
     cases h₁₂v with
     | root hr =>
     {
     }
     | nest s hs =>
      {
     }
   }
  case inr Hv =>
  {
    sorry
  }


-- This will be much more interesting once mutations are in the game!
lemma ChangeListStep.indep_comm_ids {σ σ₁ σ₂ σ₁₂ σ₂₁ : Reactor} {rcn₁ rcn₂ : ID} {cs₁ cs₂ : List Change} :
  (σ -[rcn₁:cs₁]→* σ₁) → (σ₁ -[rcn₂:cs₂]→* σ₁₂) →
  (σ -[rcn₂:cs₂]→* σ₂) → (σ₂ -[rcn₁:cs₁]→* σ₂₁) →
  (∀ c₁ c₂ i₁ i₂, c₁ ∈ cs₁ → c₂ ∈ cs₂ → c₁.target = some i₁ → c₂.target = some i₂ → i₁ ≠ i₂) →
  σ₁₂.ids = σ₂₁.ids := by
  intros hσσ₁ hσ₁σ₁₂ hσσ₂ hσ₂σ₂₁ his
  sorry

theorem ChangeListStep.indep_comm {σ σ₁ σ₂ σ₁₂ σ₂₁ : Reactor} {rcn₁ rcn₂ : ID} {cs₁ cs₂ : List Change} :
  (σ -[rcn₁:cs₁]→* σ₁) → (σ₁ -[rcn₂:cs₂]→* σ₁₂) →
  (σ -[rcn₂:cs₂]→* σ₂) → (σ₂ -[rcn₁:cs₁]→* σ₂₁) →
  (∀ c₁ c₂ i₁ i₂, c₁ ∈ cs₁ → c₂ ∈ cs₂ → c₁.target = some i₁ → c₂.target = some i₂ → i₁ ≠ i₂) →
  σ₁₂ = σ₂₁ := by
  intro h₁ h₁₂ h₂ h₂₁ ht
  have hIDs := ChangeListStep.indep_comm_ids h₁ h₁₂ h₂ h₂₁ ht
  apply (Reactor.equal_ids hIDs)
  intros i cmp v h₁₂v
  apply (ChangeListStep.value_identical h₁ h₁₂ h₂ h₂₁ ht cmp i v h₁₂v)


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
  case single h => cases h <;> simp [Context.addCurrentExecuted, Finmap.update_ne _ _ _ hg.symm]
  case trans s₁ s₂ _ he _ hi =>
    have hc : s₁.ctx.executedRcns g = s₂.ctx.executedRcns g := by cases he <;> simp [Context.addCurrentExecuted, Finmap.update_ne _ _ _ hg.symm]
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
    have h' := Reactor.ids_def.mp ⟨_, hi⟩
    rw [←h] at h'
    exact absurd h' he.unexeced

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
    simp [clearingPorts_unique h₁ h₂, Context.advanceTime, hg₂]  
  case' completeInst.advanceTime hc _ _ _ hic _, advanceTime.completeInst _ _ _ hic _ hc => 
    cases hc.exec; case' single hi, trans hi _ => exact False.elim $ impossible_case_aux hi hic
where
  impossible_case_aux {s₁ s₂ : State} (hi : s₁ ⇓ᵢ s₂) (hic : s₁.instComplete) : False := by
    cases hi 
    case' execReaction hl hce _ _, skipReaction hl hce _ =>
      exact absurd (Reactor.ids_def.mp ⟨_, hl⟩) $ mt (Finset.ext_iff.mp hic _).mpr <| hce.unexeced

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
  case step.refl _ _ h₂₃ _ h₁₂ => exact False.elim $ impossible_case_aux hc₂ ht.symm h₁₂ h₂₃
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
      have ⟨sₘ, h⟩ := hi.exec.first_step
      exact absurd h $ (State.instComplete_to_inst_stuck hc) sₘ
    case advanceTime g hg _ _ => 
      have h := time_monotone h₂₃
      rw [←ht] at h
      simp only at h
      have h' := s₁.ctx.advanceTime_strictly_increasing g (s₁.time_lt_nextTag hg)
      exact (lt_irrefl _ $ lt_of_le_of_lt h h').elim
