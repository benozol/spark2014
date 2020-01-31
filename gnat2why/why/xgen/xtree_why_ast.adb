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
with Xkind_Tables;
with Xtree_Tables;

package body Xtree_Why_AST is

   Node_Kind_Name : constant Wide_String := "Why_Node_Kind";
   Node_Type_Name : constant Wide_String := "Why_Node";
   Kind_Name      : constant Wide_String := "Kind";

   function Clean_Identifier (Str : String) return String;
   function OCaml_Type_Identifier (Str : String) return Wide_String;
   function OCaml_Variant_Identifier (Str : String) return Wide_String;

   procedure Print_OCaml_Why_Node_Field_Types (O : in out Output_Record);

   function Clean_Identifier (Str : String) return String is
      Res : String := Str;
   begin
      for Ix in Res'Range loop
         if Res (Ix) = '.' then
            Res (Ix) := '_';
         end if;
      end loop;
      return Res;
   end Clean_Identifier;

   function OCaml_Type_Identifier (Str : String) return Wide_String is
      Str1 : String := Clean_Identifier (Str);
   begin
      To_Lower (Str1);
      declare
         Str2 : String :=
           (if Str1 = "boolean" then
               "bool"
            else
               Str1);
      begin
         return To_Wide_String (Str2);
      end;
   end OCaml_Type_Identifier;

   function OCaml_Variant_Identifier (Str : String) return Wide_String is
      Str1 : String := Clean_Identifier (Str);
   begin
      To_Lower (Str1);
      if Str1'Length > 0 then
         Str1 (Str1'First) := To_Upper (Str1 (Str1'First));
      end if;
      return To_Wide_String (Str1);
   end OCaml_Variant_Identifier;

   --  Print types from Why.Sinfo
   procedure Print_OCaml_Why_Sinfo_Types (O : in out Output_Record) is
   begin
      PL (O, "(* Why.Sinfo *)");
      NL (O);

      PL (O, "type ew_odomain =");
      Relative_Indent (O, 2);
      for X in EW_ODomain'Range loop
         PL (O, "| " & OCaml_Variant_Identifier (EW_ODomain'Image (X)));
      end loop;
      Relative_Indent (O, -2);
      NL (O);

      PL (O, "type ew_domain =");
      Relative_Indent (O, 2);
      for X in EW_Domain'Range loop
         PL (O, "| " & OCaml_Variant_Identifier (EW_Domain'Image (X)));
      end loop;
      Relative_Indent (O, -2);
      NL (O);

      PL (O, "type ew_type =");
      Relative_Indent (O, 2);
      for X in EW_Type'Range loop
         PL (O, "| " & OCaml_Variant_Identifier (EW_Type'Image (X)));
      end loop;
      Relative_Indent (O, -2);
      NL (O);

      PL (O, "type ew_literal =");
      Relative_Indent (O, 2);
      for X in EW_Literal'Range loop
         PL (O, "| " & OCaml_Variant_Identifier (EW_Literal'Image (X)));
      end loop;
      Relative_Indent (O, -2);
      NL (O);

      PL (O, "type ew_theory_type =");
      Relative_Indent (O, 2);
      for X in EW_Theory_Type'Range loop
         PL (O, "| " & OCaml_Variant_Identifier (EW_Theory_Type'Image (X)));
      end loop;
      Relative_Indent (O, -2);
      NL (O);

      PL (O, "type ew_clone_type =");
      Relative_Indent (O, 2);
      for X in EW_Clone_Type'Range loop
         PL (O, "| " & OCaml_Variant_Identifier (EW_Clone_Type'Image (X)));
      end loop;
      Relative_Indent (O, -2);
      NL (O);

      PL (O, "type ew_subst_type =");
      Relative_Indent (O, 2);
      for X in EW_Subst_Type'Range loop
         PL (O, "| " & OCaml_Variant_Identifier (EW_Subst_Type'Image (X)));
      end loop;
      Relative_Indent (O, -2);
      NL (O);

      PL (O, "type ew_connector =");
      Relative_Indent (O, 2);
      for X in EW_Connector'Range loop
         PL (O, "| " & OCaml_Variant_Identifier (EW_Connector'Image (X)));
      end loop;
      Relative_Indent (O, -2);
      NL (O);

      PL (O, "type ew_assert_kind =");
      Relative_Indent (O, 2);
      for X in EW_Assert_Kind'Range loop
         PL (O, "| " & OCaml_Variant_Identifier (EW_Assert_Kind'Image (X)));
      end loop;
      Relative_Indent (O, -2);
   end Print_OCaml_Why_Sinfo_Types;

   procedure Print_OCaml_Opaque_ids (O : in out Output_Record) is
      use String_Lists;
      use Class_Lists;

      procedure Process_One_Node_Kind (Position : String_Lists.Cursor);
      --  Same as Print_Subtypes, but only for the kind
      --  pointed by Position.

      procedure Process_One_Class_Kind (Position : Class_Lists.Cursor);
      --  Same as Print_Subtypes, but only for the class
      --  pointed by Position.

      procedure Print_Subtypes (Prefix : Wide_String);
      --  Print subtypes for a given node kind whose prefix
      --  is passed as parameter.

      ----------------------------
      -- Process_One_Class_Kind --
      ----------------------------

      procedure Process_One_Class_Kind (Position : Class_Lists.Cursor) is
         CI : constant Class_Info := Class_Lists.Element (Position);
      begin
         Print_Subtypes (Class_Name (CI));

         if Position /= Classes.Last then
            NL (O);
         end if;
      end Process_One_Class_Kind;

      ---------------------------
      -- Process_One_Node_Kind --
      ---------------------------

      procedure Process_One_Node_Kind (Position : String_Lists.Cursor) is
         S : constant Wide_String_Access := String_Lists.Element (Position);
      begin
         Print_Subtypes (S.all);

         if Position /= Kinds.Last then
            NL (O);
         end if;
      end Process_One_Node_Kind;

      --------------------
      -- Print_Subtypes --
      --------------------

      procedure Print_Subtypes (Prefix : Wide_String) is
      begin
         for Multiplicity in Id_Multiplicity'Range loop
            PL (O, "and " & OCaml_Type_Identifier (To_String (Id_Subtype (Prefix, Opaque, Multiplicity)))
                & " = " & OCaml_Type_Identifier (To_String (Base_Id_Subtype (Prefix, Opaque, Multiplicity)))
               );
         end loop;
      end Print_Subtypes;

      --  Start of processing for Print_Subtypes

   begin
      Kinds.Iterate (Process_One_Node_Kind'Access);
      NL (O);
      Classes.Iterate (Process_One_Class_Kind'Access);
   end Print_OCaml_Opaque_ids;

   procedure Print_OCaml_Why_Node_Type (O : in out Output_Record) is
      use Xtree_Tables.Node_Lists;
   begin
      PL (O, "(* Why_Node *)");
      NL (O);

      PL (O, "and " & OCaml_Type_Identifier (To_String (Node_Type_Name)) & " =");
      Relative_Indent (O, 2);
      for Kind in Why_Tree_Info'Range loop
         PL (O, "| " & OCaml_Variant_Identifier (Why_Node_Kind'Image (Kind)) & " of");
         Relative_Indent (O, 4);
         for FI of Why_Tree_Info (Kind).Fields loop
            P (O, OCaml_Type_Identifier (To_String (Type_Name (FI, Opaque))) & " * ");
         end loop;
         --           if not Is_Empty (Why_Tree_Info (Kind).Fields) then
         --              NL (O);
         --           end if;
         declare
            First : Boolean := True;
         begin
            P (O, "(* common: *) ");
            for FI of Common_Fields.Fields loop
               P (O, (if First then "" else " * ") &
                    OCaml_Type_Identifier (To_String (Type_Name (FI, Opaque))));
               First := False;
            end loop;
         end;
         NL (O);
         Relative_Indent (O, -4);
      end loop;
      Relative_Indent (O, -2);
   end Print_OCaml_Why_Node_Type;

   procedure Print_Ada_Why_Node_Id_To_Json (O : in out Output_Record) is
   begin
      PL (O, "function Why_Node_Id_To_Json (N : Why_Node_Id) return JSON_Value_Type is");
      begin
         Relative_Indent (O, 3);
         PL (O, "N_Kind : constant Why_Node_Kind := Get_Kind (N);");
         PL (O, "Res : constant JSON_Value := Empty_Array;");
         Relative_Indent (O, -3);
      end;
      PL (O, "begin");
      begin
         Relative_Indent (O, 3);
         PL (O, "Append (Res, Why_Node_Kind'Image (N_Kind));");
         PL (O, "case N_Kind is");
         begin
            Relative_Indent (O, 3);
            for Kind in Why_Tree_Info'Range loop
               PL (O, "when " & Mixed_Case_Name (Kind) & " =>");
               Relative_Indent (O, 3);
               PL (O, "declare");
               begin
                  Relative_Indent (O, 3);
                  PL (O, "N1 : " & Mixed_Case_Name (Kind) & "_Id := +N;");
                  Relative_Indent (O, -3);
               end;
               PL (O, "begin");
               begin
                  Relative_Indent (O, 3);
                  for FI of Why_Tree_Info (Kind).Fields loop
                     PL (O, "Append (Res, " &
                           Type_Name (FI, Opaque) & "_To_Json " &
                           "(Get_Node (+N1)." & Type_Name (FI, Opaque)  & ")" &
                           ");");
                  end loop;
                  --                    declare
                  --                       First : Boolean := True;
                  --                    begin
                  --                       P (O, "(* common: *) ");
                  --                       for FI of Common_Fields.Fields loop
                  --                          P (O, (if First then "" else " * ") &
                  --                               OCaml_Type_Identifier (To_String (Type_Name (FI, Opaque))));
                  --                          First := False;
                  --                       end loop;
                  --                    end;
                  Relative_Indent (O, -3);
               end;
               PL (O, "end;");
               Relative_Indent (O, -3);
            end loop;
            Relative_Indent (O, -3);
         end;
         PL (O, "return Res;");
         Relative_Indent (O, -3);
      end;
      PL (O, "end Why_Node_To_Json");
   end Print_Ada_Why_Node_Id_To_Json;

   procedure Print_OCaml_Why_Node_From_Json (O : in out Output_Record) is
   begin
      PL (O, "let why_node_from_json () = ...");
   end Print_OCaml_Why_Node_From_Json;

   procedure Print_OCaml_Why_Node_Field_Types (O : in out Output_Record) is
      use Node_Lists;
   begin
      for Kind in Why_Tree_Info'Range loop
         NL (O);
         P (O, "and " & OCaml_Type_Identifier (Why_Node_Kind'Image (Kind)) & " = ");
         if Is_Empty (Why_Tree_Info (Kind).Fields) then
            PL (O, "unit");
         else
            Relative_Indent (O, 2);
            PL (O, "{ ");
            for FI of Why_Tree_Info (Kind).Fields loop
               PL (O, OCaml_Type_Identifier (To_String (Param_Name (FI))) & ": "
                   & OCaml_Type_Identifier (To_String (Type_Name (FI, Opaque))) & ";");
            end loop;
            Relative_Indent (O, -2);
            PL (O, "}");
         end if;
      end loop;
   end Print_OCaml_Why_Node_Field_Types;

end Xtree_Why_AST;
