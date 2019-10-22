module Testing
open FStar.HyperStack.ST

assume val test_start: unit ->  Stack unit (fun _ -> true) (fun _ _ _ -> true)
assume val test_end: unit -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
assume val check_i8: C.String.t -> Int8.t -> Int8.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
assume val check_i16: C.String.t -> Int16.t -> Int16.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
assume val check_i32: C.String.t -> Int32.t -> Int32.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
assume val check_i64: C.String.t -> Int64.t -> Int64.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
assume val check_ui8: C.String.t -> UInt8.t -> UInt8.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
assume val check_ui16: C.String.t -> UInt16.t -> UInt16.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
assume val check_ui32: C.String.t -> UInt32.t -> UInt32.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
assume val check_ui64: C.String.t -> UInt64.t -> UInt64.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
assume val check_bool: C.String.t -> bool -> bool -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
assume val check_string: C.String.t -> C.String.t -> C.String.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)