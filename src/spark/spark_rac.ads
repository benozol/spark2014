-------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                             S P A R K _ R A C                            --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2010-2021, AdaCore                     --
--                                                                          --
-- gnatprove is  free  software;  you can redistribute it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnatprove is distributed  in the hope that  it will be useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General Public License  distributed with  gnatprove;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnatprove is maintained by AdaCore (http://www.adacore.com)              --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with Ada.Containers;        use Ada.Containers;
with Ada.Containers.Hashed_Maps;
with Ada.Numerics.Big_Numbers.Big_Integers;
use Ada.Numerics.Big_Numbers.Big_Integers;
with Types;                 use Types;
with VC_Kinds;              use VC_Kinds;
with Namet;                 use Namet;
with Common_Containers;     use Common_Containers;

--  This package implements small-step (normal) runtime-assertion checking
--  (RAC) for SPARK to check counterexamples.
package SPARK_RAC is

   type Result;
   --  Information about the termination of the RAC execution

   function Execute
     (E           : Entity_Id;
      Cntexmp     : Cntexample_File_Maps.Map;
      Fuel        : Integer := -1)
      return Result;
   --  Runtime-assertion checking execution of sub-program E using the
   --  counterexample Cntexmp as an oracle for program parameters. If Fuel
   --  is non-negative, it is decreased in the execution of every statement or
   --  expression, and the execution terminates as incomplete, when it reaches
   --  zero.

   type Value_Type is
     (Ty_Integer,
      --  unsigned integer or range (??? TODO signed integers)
      Ty_Enum,
      --  an enumeration value
      Ty_Record
      --  a record value
     );
   --  The type of a value in the RAC engine

   type Value;
   --  A value in the RAC engine

   type Access_Value is access Value;
   --  A pointer to a value

   function Name_Hash (N : Name_Id) return Hash_Type;

   package Fields is new Ada.Containers.Hashed_Maps
     (Key_Type        => Entity_Id,
      Element_Type    => Access_Value,
      Hash            => Node_Hash,
      Equivalent_Keys => "=");
   --  Fields of a record value

   type Value (Ty : Value_Type := Ty_Integer) is record
      case Ty is
         when Ty_Integer =>
            Integer_Content : Big_Integer;
         when Ty_Enum =>
            Enum_Entity     : Entity_Id;
         when Ty_Record =>
            Record_Fields   : Fields.Map;
      end case;
   end record;

   type Opt_Value (Present : Boolean := False) is record
      case Present is
         when True =>
            Content : Value;
         when False =>
            null;
      end case;
   end record;
   --  An optional value in the RAC engine

   type Result_Kind is
     (Res_Normal,
      --  RAC execution terminated normally, without encountering an invalid
      --  check
      Res_Failure,
      --  RAC execution failed due to an invalid check
      Res_Incomplete,
      --  RAC execution could not be completed (e.g., missing implementation)
      Res_Stuck,
      --  RAC execution got stuck (e.g., invalid values in the counterexample)
      Res_Not_Executed
      --  RAC execution has not been requested
     );
   --  The different ways how the RAC execution can terminate

   type Result (Res_Kind : Result_Kind := Res_Not_Executed) is record
      case Res_Kind is
         when Res_Normal =>
            Res_Value   : Opt_Value;
            --  The result value of toplevel RAC call
         when Res_Failure =>
            Res_Node    : Node_Id;
            --  The node of the check that failed (only set by RAC)
            Res_VC_Kind : VC_Kind;
            --  The VC kind that triggered the failure
            Res_VC_Id   : Natural := Natural'Last;
            --  The ID of the check that failed (not set by RAC)
         when Res_Incomplete
            | Res_Stuck
         =>
            Res_Reason  : Unbounded_String;
            --  The reason of the incomplete or stuck termination
         when Res_Not_Executed =>
            null;
      end case;
   end record;

   function "=" (V1 : Value; V2 : Value) return Boolean;

   function To_String (V : Value) return String;

   function To_String (V : Opt_Value) return String;

   function To_String (Res : Result) return String;
end SPARK_RAC;
