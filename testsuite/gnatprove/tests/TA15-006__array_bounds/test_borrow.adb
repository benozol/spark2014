procedure Test_Borrow with SPARK_Mode is
   type Int_Acc is not null access Integer;

   type Two_Val is record
      X, Y : Int_Acc;
   end record;

   type Two_Val_Array is array (Positive range <>) of Two_Val;

   type Two_Val_Array_Acc is access Two_Val_Array;

   type Two_Arrays is record
      F, G : Two_Val_Array_Acc;
   end record;

   type Two_Array_Acc is not null access Two_Arrays;

   procedure Try (X : Two_Array_Acc) with
     Pre => X.F /= null and then X.F'First = 1 and then X.F'Last = 2
   is
      Z : access Integer := X.F (1).X; -- ok
   begin
      pragma Assert (X.F'First = 1 and X.F'Last = 2 and X.F'Length = 2);
   end Try;

   procedure Try_2 (X : Two_Array_Acc) with
     Pre => X.F /= null and then X.F'First = 1 and then X.F'Last = 2
   is
      Z : access Two_Val_Array := X.F;
   begin
      pragma Assert (X.F'First = 1 and X.F'Last = 2 and X.F'Length = 2); -- imprecise, could be accepted
   end Try_2;

   procedure Try_3 (X : Two_Array_Acc) with
     Pre => X.F /= null and then X.F'First = 1 and then X.F'Last = 2
   is
      Z : access Two_Arrays := X;
   begin
      pragma Assert (X.F'First = 1 and X.F'Last = 2 and X.F'Length = 2); -- should be rejected
   end Try_3;

   procedure Try_4 (X : Two_Array_Acc) with
     Pre => X.F /= null and then X.F'First = 1 and then X.F'Last = 2
   is
      Z : Int_Acc := X.F (1).X;
   begin
      pragma Assert (X.F'First = 1 and X.F'Last = 2 and X.F'Length = 2); -- ok
      X.F := null; --  Do not try to reconstruct X.F, as the borrow checker is imprecise on array elements
   end Try_4;

   procedure Try_5 (X : Two_Array_Acc) with
     Pre => X.F /= null and then X.F'First = 1 and then X.F'Last = 2
   is
      Z : Two_Val_Array_Acc := X.F;
   begin
      pragma Assert (X.F'First = 1 and X.F'Last = 2 and X.F'Length = 2); -- imprecise, could be accepted
      X.F := Z;
   end Try_5;

   procedure Try_6 (X : in out Two_Array_Acc) with
     Pre => X.F /= null and then X.F'First = 1 and then X.F'Last = 2
   is
      Z : Two_Array_Acc := X;
   begin
      pragma Assert (X.F'First = 1 and X.F'Last = 2 and X.F'Length = 2); -- should be rejected
      X := Z;
   end Try_6;

begin
   null;
end Test_Borrow;
