structure Tests : TESTS =
struct
  type test = string * (unit -> unit)

  fun assert x =
    if not x then raise Fail "test assertion" else ()

  val all_tests : test list ref = ref [];

  fun register_test t =
    all_tests := t :: !all_tests

  fun run_tests test_list : unit =
    case test_list of
      [] => ()
    | ((name, f) :: other) => (
        print ("running " ^ name ^ "\n");
        f();
        run_tests other
      )

  fun run_all_tests () = (
    run_tests (rev (!all_tests));
    print "All tests passed\n"
  )

end
