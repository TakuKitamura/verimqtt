module Test

open Main
open FStar.HyperStack.ST
open LowStar.Printf
open Testing

val main : u:unit -> Stack C.exit_code (fun _ -> True) (fun _ _ _ -> True)
let main () =
    push_frame ();
    let r = is_valid_message_type_check 0xffuy in
    checku8 r 1uy;
    pop_frame ();
    C.EXIT_SUCCESS