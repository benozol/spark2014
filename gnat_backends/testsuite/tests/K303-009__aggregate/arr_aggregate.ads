package Arr_Aggregate is
   pragma Annotate (Gnatprove, Force);
   type A1 is array (1 .. 1) of Integer;
   type A2 is array (1 .. 2) of Integer;
   type A3 is array (1 .. 2) of A2;
   
   One : Integer;
   
   procedure P1 (A : in out A1; B : Integer) with
     Pre => One = 1,
     Post => (case B is when 1      => A (One) = One,
   	                when others => (for all K in A1'Range => A (K) = One));
	
   procedure P2 (A : in out A2; B : Integer) with
     Pre => One = 1,
     Post => (case B is when 1 => A (One) = One and A (2) = 2,
   	                when 2 => (for all K in A2'Range => A (K) = One),
   	                when 3 => (for all K in A2'Range => A (K) = One),
   	                when 4 => A (One) = 2 and A (2) = One,
   	                when others => A (One) = One and A (2) = 2);
     
   procedure P3 (A : in out A3; B : Integer) with
     Pre => One = 1,
     Post => (case B is when 1 => (for all J in A3'Range => (A (J) (One) = One and A (J) (2) = 2)),
	                when 2 => (for all J in A3'Range => (for all K in A2'Range => A (J) (K) = One)),
	                when 3 => (for all J in A3'Range => (for all K in A2'Range => A (J) (K) = One)),
	                when 4 => (for all J in A3'Range => (A (J) (One) = 2 and A (J) (2) = One)),
	                when others => (for all J in A3'Range => (A (J) (One) = One and A (J) (2) = 2)));
end Arr_Aggregate;
