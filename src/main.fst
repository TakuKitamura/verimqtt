module Main

open FStar.HyperStack.ST
module LP = LowStar.Printf

val main : u:unit -> Stack C.exit_code (fun _ -> True) (fun _ _ _ -> True)
let main () =
    push_frame ();
    LP.print_string "Hello verimqtt.\n";
    pop_frame ();
    C.EXIT_SUCCESS
