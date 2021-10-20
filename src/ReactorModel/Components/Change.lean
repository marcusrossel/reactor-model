import ReactorModel.Components.Reactor

variable (ι υ) [ID ι] [Value υ]

inductive Change
  | port (target : ι) (value : υ)
  | state (target : ι) (value : υ)
  | connect (src : ι) (dst : ι)
  | disconnect (src : ι) (dst : ι)
  | create (rtr : Reactor ι υ) (id : ι)
  | delete (rtrID : ι)

variable {ι υ}

def Change.mutates : Change ι υ → Bool 
  | port _ _       => false
  | state _ _      => false
  | connect _ _    => true
  | disconnect _ _ => true
  | create _ _     => true
  | delete _       => true