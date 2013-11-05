pragma SPARK_Mode (On);
package Stack_14
  with Abstract_State => Stack,
       Initializes    => Stack
is
   procedure Push(X : in Integer)
     with Global => (In_Out => Stack);

   procedure Pop(X : out Integer)
     with Global => (In_Out => Stack);

end Stack_14;
