package body Misc
is
   pragma Warnings (Off, "* has no effect");
   procedure Test_A
     with Depends => null
   is
      X : Enum_T;

      function Foo return Enum_T with Global => null
      is
      begin
         return Elem_2;
      end Foo;
   begin
      X := Enum_T'Succ (Foo);  --  @RANGE_CHECK:FAIL
   end Test_A;
   pragma Warnings (On, "* has no effect");
end Misc;
