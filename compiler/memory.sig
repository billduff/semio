type memory_address

(* CR wduff: load will nominally pull the entire object into registers and or the heap, which would
   be wasteful, but it should be trivial to remove the extra loads with dead code elimination. *)
unsafe builtin load : memory_address -> a end
builtin store : memory_address -> a -> unit end

signature Raw_memory_unix = sig
  type t

  affine val the_one_and_only : t

  val mmap : { &t, length : nat } -> memory_address

  (* and munmap and sbrk *)
end

signature Memory_regions = sig
  type t

  module Region : sig
    type t
  end

  val create_unix : Raw_memory_unix.t -> t

  (* CR wduff: This can fail. *)
  val create_region : &t -> Region.t
end

signature Heap : sig
  type t

  module Box : sig
    type t : type -> type

    val swap : forall n. forall a b : type n. t a -> b -> a * t b

    val set : forall n. forall a : n. t (uninit n) -> a -> t a
    val get : forall n. forall a : n. t a -> a * t (uninit n)
  end

  val create : Memory_regions.Region.t -> t

  (* The idea is that this will allocate a box with the right shape for an [a] and copy the given
     [a] into it. We need the object itself because we need to know the length, which may not be
     determined by the type alone (e.g. for arrays). We can support ununitialized allocations by
     letting folks explicitly pass some kind of uninitialized (or partly initialized) value. *)
  val box : &t -> a -> Box.t a
end
