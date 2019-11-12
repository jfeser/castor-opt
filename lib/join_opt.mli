open! Core
open! Castor

module Config : sig
  module type S = sig
    include Ops.Config.S

    include Filter_tactics.Config.S

    include Simple_tactics.Config.S

    include Approx_cost.Config.S
  end
end

module Make (C : Config.S) : sig
  val transform : Ops.t
end
