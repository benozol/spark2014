package body GP with
   Refined_State => (State        => GG1,
                     Atomic_State => GG2)
is
   GG1 : T;
   GG2 : T with Volatile;
end GP;
