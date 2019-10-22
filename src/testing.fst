module Testing
open FStar.HyperStack.ST

assume val check: bool -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
assume val check8: Int8.t -> Int8.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
assume val check16: Int16.t -> Int16.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
assume val check32: Int32.t -> Int32.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
assume val check64: Int64.t -> Int64.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
assume val checku8: UInt8.t -> UInt8.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
assume val checku16: UInt16.t -> UInt16.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
assume val checku32: UInt32.t -> UInt32.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
assume val checku64: UInt64.t -> UInt64.t -> Stack unit (fun _ -> true) (fun _ _ _ -> true)
