module Test

open Main
open FStar.HyperStack.ST
open LowStar.Printf
open Testing

inline_for_extraction noextract
let (!$) = C.String.of_literal

val main : u:unit -> Stack C.exit_code (fun _ -> True) (fun _ _ _ -> True)
let main () =
    test_start ();
    push_frame ();
    check_ui8 !$"UInt8での比較" 1uy 1uy;
    check_i32 !$"Int32での比較" 1000l 1001l;
    check_bool !$"boolがTrueであるか" (1uy = 1uy);
    check_string !$"文字列の比較" !$"apple" !$"orange";
    pop_frame ();
    test_end ();
    C.EXIT_SUCCESS