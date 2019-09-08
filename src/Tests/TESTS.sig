signature TESTS =
sig
  type test = string * (unit -> unit)
  val assert : bool -> unit
  val register_test : test -> unit
  val run_all_tests : unit -> unit
end
