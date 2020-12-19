import reactor.basic

namespace reactor

  namespace sequential
    
    private def run' {nᵢ nₒ nₛ : ℕ} : (reactor nᵢ nₒ nₛ) → list (ports nᵢ) → list (ports nₒ) → (reactor nᵢ nₒ nₛ) × list (ports nₒ) 
      | r [] o := ⟨reactor.run r, o⟩ 
      | r (iₕ :: iₜ) o := 
        let rₕ := reactor.run r in
        let rₜ : (reactor nᵢ nₒ nₛ) := ⟨iₕ, ports.absent, rₕ.st, rₕ.rs⟩ in 
        run' rₜ iₜ (o ++ [rₕ.outputs])

    -- The first input is already within the given reactor, and the last output will also be part
    -- of the output reactor.
    protected def run {nᵢ nₒ nₛ : ℕ} (r : reactor nᵢ nₒ nₛ) (i : list (ports nᵢ)) : (reactor nᵢ nₒ nₛ) × list (ports nₒ) :=
       run' r i []

    -- Passing a finite sequence of inputs through a single unconnected reactor is deterministic,
    -- if equal sequences lead to equal outputs and end states.
    -- Since `reactor.sequence.run` is a function, determinism is trivially fulfilled.
    theorem deterministic {nᵢ nₒ nₛ : ℕ} (r : reactor nᵢ nₒ nₛ) (i₁ i₂ : list (ports nᵢ)) : 
      i₁ = i₂ → (sequential.run r i₁) = (sequential.run r i₂) :=
      begin
      intro h, 
      have sr : sequential.run r = sequential.run r, by apply congr_arg sequential.run (refl r), 
      rw h,
      sorry
      end

  end sequential

end reactor