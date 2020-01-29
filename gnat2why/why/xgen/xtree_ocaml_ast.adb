------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                          X T R E E _ D E C L S                           --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2020, AdaCore                     --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute  it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnat2why is distributed  in the hope that  it will be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General  Public License  distributed with  gnat2why;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Characters.Conversions; use Ada.Characters.Conversions;
with GNAT.Case_Util;             use GNAT.Case_Util;
with Xkind_Tables; use Xkind_Tables;
with Xtree_Tables; use Xtree_Tables;
with Why.Sinfo;    use Why.Sinfo;

package body Xtree_OCaml_AST is

   Node_Kind_Name : constant Wide_String := "Why_Node_Kind";
   Node_Type_Name : constant Wide_String := "Why_Node";
   Kind_Name      : constant Wide_String := "Kind";

   function Lower_Case_Name (Kind : Why_Node_Kind) return Wide_String;
   function Lower_Case_Name (Name : Wide_String) return Wide_String;
   function Upper_Case_Name (Kind : Why_Node_Kind) return Wide_String;

   function Lower_Case_Name (Kind : Why_Node_Kind) return Wide_String is
      Name : String := Why_Node_Kind'Image (Kind);
   begin
      To_Lower (Name);
      return To_Wide_String (Name);
   end Lower_Case_Name;

   function Lower_Case_Name (Name : Wide_String) return Wide_String is
      Name1 : Wide_String := Name;
   begin
      return Name1;
   end Lower_Case_Name;

   function Upper_Case_Name (Kind : Why_Node_Kind) return Wide_String is
      Name : String := Why_Node_Kind'Image (Kind);
   begin
      To_Lower (Name);
      if Name'Length > 0 then
         Name (Name'First) := To_Upper (Name (Name'First));
      end if;
      return To_Wide_String (Name);
   end Upper_Case_Name;

   procedure Print_OCaml_Node_Types (O : in out Output_Record) is
      use Node_Lists;
      First : Boolean := True;
   begin
      for Kind in Why_Tree_Info'Range loop
         NL (O);
         P (O, (if First then "type " else "and "));
         P (O, Lower_Case_Name (Kind) & " = ");
         if Is_Empty (Why_Tree_Info (Kind).Fields) then
            PL (O, "unit");
         else
            Relative_Indent (O, 2);
            PL (O, "{ ");
            for FI of Why_Tree_Info (Kind).Fields loop
               PL (O, Lower_Case_Name (Param_Name (FI)) & ": "
& Lower_Case_Name (Type_Name (FI, Opaque)) & "; ");
            end loop;
            Relative_Indent (O, -2);
            PL (O, "}");
         end if;
         First := False;
      end loop;
   end Print_OCaml_Node_Types;

   procedure Print_OCaml_AST (O : in out Output_Record) is
      use Node_Lists;
      First : Boolean := True;
   begin
      for Class of Classes loop
         if First then
            First := False;
         else
            NL (O);
         end if;

         PL (O, (if First then "type " else "and ")
             & Lower_Case_Name (Class.Name.all) & " =");
         Relative_Indent (O, 2);

         if Class.Father /= null then -- TODO check Class.Father /= Class.Name
            PL (O, "| " & Class.Father.all & " of " & Class.Father.all);
         end if;

         for Kind in Class_First (Class) .. Class_Last (Class) loop
            PL (O, "| " & Upper_Case_Name (Kind));
         end loop;

         Relative_Indent (O, -2);
      end loop;
   end Print_OCaml_AST;

   procedure Print_Serialize_JSON_Ada (O : in out Output_Record) is
   begin
      PL (O, "procedure Serialize_JSON () is begin ... end Print_JSON;");
   end Print_Serialize_JSON_Ada;

   procedure Print_Deserialize_JSON_OCaml (O : in out Output_Record) is
   begin
      PL (O, "let deserialize_JSON () = ...");
   end Print_Deserialize_JSON_OCaml;

end Xtree_OCaml_AST;
