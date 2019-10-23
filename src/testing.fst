module Testing
open FStar.HyperStack.ST

assume val test_start: unit ->  Stack unit (fun _ -> true) (fun _ _ _ -> true)
assume val test_end: unit -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
assume val eq_i8: C.String.t -> Int8.t -> Int8.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
assume val eq_i16: C.String.t -> Int16.t -> Int16.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
assume val eq_i32: C.String.t -> Int32.t -> Int32.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
assume val eq_i64: C.String.t -> Int64.t -> Int64.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
assume val eq_u8: C.String.t -> UInt8.t -> UInt8.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
assume val eq_u16: C.String.t -> UInt16.t -> UInt16.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
assume val eq_u32: C.String.t -> UInt32.t -> UInt32.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
assume val eq_u64: C.String.t -> UInt64.t -> UInt64.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
assume val eq_bool: C.String.t -> bool -> bool -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
assume val eq_str: C.String.t -> C.String.t -> C.String.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)