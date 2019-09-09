module type S = Run_intf.S

module Make(A : ATS.S) : S with module A = A
