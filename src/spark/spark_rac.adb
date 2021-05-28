-------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                             S P A R K _ R A C                            --
--                                                                          --
--                                 B o d y                                  --
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

with Ada.Containers.Indefinite_Vectors;
with Ada.Environment_Variables;
with GNAT.Traceback;
with GNAT.Traceback.Symbolic;
with Sinfo.Nodes;            use Sinfo.Nodes;
with Nlists;                 use Nlists;
with Einfo.Utils;            use Einfo.Utils;
with Atree;                  use Atree;
with Sinput;                 use Sinput;
with Snames;                 use Snames;
with Einfo.Entities;         use Einfo.Entities;
with SPARK_Util;             use SPARK_Util;
with SPARK_Util.Subprograms; use SPARK_Util.Subprograms;
with SPARK_Atree;
with GNATCOLL.Utils;         use GNATCOLL.Utils;
with GNATCOLL.JSON;          use GNATCOLL.JSON;
with Sinfo.Utils;            use Sinfo.Utils;
with Output;                 use Output;
with Uintp;                  use Uintp;
with Stand;                  use Stand;
with Treepr;
with Hashing; use Hashing;
with Sem_Util; use Sem_Util;
with Gnat2Why.CE_Utils; use Gnat2Why.CE_Utils;
with Ada.Strings; use Ada.Strings;
with Ada.Strings.Fixed;

package body SPARK_RAC is

   ----------------------------------------------------------------------------
   --  Values

   function No_Value return Opt_Value is
     (Present => False);
   --  Absence of an optional value

   function Some_Value (V : Value) return Opt_Value is
     (Present => True, Content => V);
   --  Presence of an optional value

   function Enum_Value (E : Entity_Id) return Value is
     (Ty => Ty_Enum, Enum_Entity => E);

   function Record_Value (F : Fields.Map) return Value is
     (Ty => Ty_Record, Record_Fields => F);

   function Boolean_Value (B : Boolean) return Value;

   function Value_Boolean (V : Value) return Boolean;

   procedure Check_Integer (I : Big_Integer; Ty : Entity_Id; N : Node_Id);

   function Integer_Value
     (I : Big_Integer; Ty : Entity_Id; N : Node_Id) return Value;
   --  Construct integer and check against type bounds

   function Integer_Value
     (I : Big_Integer; N : Node_Id) return Value
   is (Integer_Value (I, Etype (N), N));
   --  Shortcut to construct integer and check against the node's type bounds

   function Integer_Value
     (I : Integer; N : Node_Id) return Value
   is (Integer_Value (To_Big_Integer (I), N));

   function Snapshot (V : Value) return Value;
   --  Make a deep copy of a value

   function Snapshot (F : Fields.Map) return Fields.Map;
   --  Make a deep copy of record fields

   function Default_Value (Ty : Node_Id) return Value;
   --  Return the type default value

   function To_String (F : Fields.Map) return String;

   function "=" (F1, F2 : Fields.Map) return Boolean;

   ----------------------------------------------------------------------------
   --  Runtime control exceptions

   Exn_RAC_Exit : exception;
   --  Signal a loop exit

   Exn_RAC_Return : exception;
   --  Signal the return from a sub-program

   procedure RAC_Return (V : Opt_Value);
   pragma No_Return (RAC_Return);
   --  Return from sub-program, optionally with some return value

   function Flush_RAC_Return return Opt_Value;
   --  Get and reset return value from last call to RAC_Return

   ----------------------------------------------------------------------------
   --  RAC result exceptions

   Exn_RAC_Failure : exception;
   --  Invalid assertion (always use RAC_Failure to ensure
   --  Flush_Exn_RAC_Result)

   Exn_RAC_Stuck : exception;
   --  Invalid assumption (always use RAC_Stuck or related to ensure
   --  Flush_Exn_RAC_Result)

   Exn_RAC_Incomplete : exception;
   --  Execution or RAC incomplete (always use RAC_Incomplete or related to
   --  ensure Flush_Exn_RAC_Result)

   function Flush_Exn_RAC_Result return Result;
   --  Get and reset the result from the last call to RAC_Failure, RAC_Stuck,
   --  RAC_Incomplete, or related

   procedure RAC_Failure (N : Node_Id; K : VC_Kind);
   pragma No_Return (RAC_Failure);
   --  Raise Exn_RAC_Failure and set result

   procedure RAC_Stuck (Reason : String);
   pragma No_Return (RAC_Stuck);
   --  Raise Exn_RAC_Stuck and set result

   procedure RAC_Incomplete (Reason : String);
   pragma No_Return (RAC_Incomplete);
   --  Raise Exn_RAC_Incomplete and set result

   procedure RAC_Unsupported (Str : String; N : Node_Id);
   pragma No_Return (RAC_Unsupported);
   --  Raise Exn_RAC_Incomplete and set result

   procedure RAC_Unsupported (Str : String; Str1 : String);
   pragma No_Return (RAC_Unsupported);
   --  Raise Exn_RAC_Incomplete and set result

   ----------------------------------------------------------------------------
   --  The evaluation environment and context

   --  ??? No aliasing/value sharing is implemented. That's alright for SPARK?
   package Attributes is new Ada.Containers.Hashed_Maps
     (Key_Type        => Name_Id,
      Element_Type    => Value,
      Hash            => Name_Hash,
      Equivalent_Keys => "=");

   function To_String (Attrs : Attributes.Map) return String;

   type Binding is record
      Val   : Value;
      Attrs : Attributes.Map := Attributes.Empty;
   end record;
   --  A binding is a plain value and a mapping of attributes to values

   type Access_Binding is access Binding;

   function To_String (B : Binding) return String;

   package Scopes is new Ada.Containers.Hashed_Maps
     (Key_Type        => Entity_Id,
      Element_Type    => Access_Binding,
      Hash            => Node_Hash,
      Equivalent_Keys => "=");

   function To_String (S : Scopes.Map) return String;

   package Environments is new Ada.Containers.Indefinite_Vectors
     (Index_Type   => Natural,
      Element_Type => Scopes.Map,
      "="          => Scopes."=");
   --  An execution environment is stack of scopes

   function To_String (E : Environments.Vector) return String;
   pragma Unreferenced (To_String);

   procedure Set_Attribute
     (S : in out Scopes.Map;
      E : N_Defining_Identifier_Id;
      A : Name_Id;
      V : Value);

   procedure Set_Value
     (S : in out Scopes.Map; E : N_Defining_Identifier_Id; V : Value);

   procedure Update_Value
     (Env : in out Environments.Vector;
      E   : Entity_Id;
      V   : Value);

   type Context is record
      Env     : Environments.Vector;
      --  The variable environment
      Cntexmp : Cntexample_File_Maps.Map;
      --  The counterexample
      Fuel    : Integer;
      --  If Fuel is non-negative, it is decreased by each expression or
      --  statement and execution terminates as incomplete when out of fuel.
   end record;
   --  The execution context

   function Find_Binding
     (E   : N_Defining_Identifier_Id;
      Ctx : in out Context)
      return Access_Binding;

   ----------------------------------------------------------------------------
   --  Value oracles

   function Can_Get (N : Node_Id) return Boolean is
     (Nkind (N) in  N_Defining_Identifier |  N_Identifier | N_Expanded_Name)
       with Ghost => True;
   --  Predicate for nodes, for which a counterexample may have a value

   function Import (V : Cntexmp_Value; N : Node_Id) return Value
     with Pre => Can_Get (N);

   function Get
     (N : Node_Id; Cntexmp : Cntexample_File_Maps.Map) return Opt_Value
   with Pre => Can_Get (N);
   --  Get the value of variable N from the counterexample

   type Value_Origin is
     (From_Counterexample,
      From_Expr,
      From_Type_Default);
   --  The origin of a value in a call to Get

   function Get
     (N                : Node_Id;
      Ex               : Node_Id;
      Use_Type_Default : Boolean;
      Ctx              : in out Context;
      Origin           : out Value_Origin)
      return Value
   with Pre => Can_Get (N);
   --  Get the value of variable N from the counterexample in the context, from
   --  the evaluation of an expression Ex, or the type default

   ----------------------------------------------------------------------------
   --  Check the validity of annotations

   procedure Get_Type_Range (Ty : Entity_Id; Low, High : out Big_Integer);

   procedure Check_Fuel_Decrease (Fuel : in out Integer);
   --  Check fuel and decrease (if non-negative)

   procedure Check_Node
     (N : N_Subexpr_Id; Ctx : in out Context; Desc : String; K : VC_Kind);

   procedure Check_List
     (L   : Node_Lists.List;
      Ctx : in out Context;
      Msg : String;
      K   : VC_Kind);
   --  Check the validity of formulas L

   function RAC_Expr (N : N_Subexpr_Id; Ctx : in out Context) return Value;
   --  Evaluate node N to a value

   procedure RAC_Statement
     (N   : N_Statement_Other_Than_Procedure_Call_Id;
      Ctx : in out Context);
   --  RAC execution of a statement N

   procedure RAC_Pragma (N : N_Pragma_Id; Ctx : in out Context);
   --  RAC execution of a pragma N

   procedure RAC_Node (N : Node_Id; Ctx : in out Context);
   --  RAC execution of node N

   procedure RAC_List (L : List_Id; Ctx : in out Context);
   --  RAC execution of list L

   procedure RAC_Decl
     (Decl : Node_Id; Scope : in out Scopes.Map; Ctx : in out Context);
   --  Add a declaration to a scope

   procedure RAC_Decls
     (Decls : List_Id; Scope : in out Scopes.Map; Ctx : in out Context);
   --  Add declarations to a scope

   function RAC_Call
     (E : Entity_Id; Ctx : in out Context;  Scope : in out Scopes.Map)
      return Opt_Value;
   --  RAC execution of a call to E with parameters in Scope

   ----------------------------------------------------------------------------
   --  Debugging auxiliaries

   procedure RAC_Info (Ctx : String; Msg : String; N : Node_Id) with
      Inline;
   --  Print info about RAC checks

   procedure RAC_Info (Msg : String) with
      Inline;
   --  Print info about RAC checks

   procedure RAC_Trace (Msg : String; N : Node_Id := Empty) with
      Inline;
   --  Trace the RAC execution

   procedure Call_Stack;
   pragma Unreferenced (Call_Stack);

   ----------------------------------------------------------------------------
   --  Implementations

   ------------
   -- Import --
   ------------

   function Import (V : Cntexmp_Value; N : Node_Id) return Value is

      procedure Import_Error (Msg : String);
      pragma No_Return (Import_Error);

      function Field_Value
        (E : Entity_Id; Fi : Cntexmp_Value_Array.Map) return Value;

      ------------------
      -- Import_Error --
      ------------------

      procedure Import_Error  (Msg : String) is
      begin
         Treepr.Print_Tree_Node (N);
         Write_Line (Write (To_JSON (V), Compact => False));
         raise Program_Error with
           ("counterexample value import error: " & Msg);
      end Import_Error;

      -----------------
      -- Field_Value --
      -----------------

      function Field_Value
        (E : Entity_Id; Fi : Cntexmp_Value_Array.Map) return Value is
         K : constant String :=
               "." & Ada.Strings.Fixed.Trim (Entity_Id'Image (E), Both);
      begin
         for C in Fi.Iterate loop
            if Cntexmp_Value_Array.Key (C) = K then
               return Import (V.Fi (C).all, E);
            end if;
         end loop;
         Import_Error ("find value " & K);
      end Field_Value;

      --  Start processing of Import

   begin
      begin

         if Is_Integer_Type (Etype (N)) then

            if V.T /= Cnt_Integer then
               Import_Error ("not integer value");
            end if;

            return Integer_Value (From_String (To_String (V.I)), N);

         elsif Is_Signed_Integer_Type (Etype (N)) then
            RAC_Unsupported ("counterexample value import", N);

         elsif Is_Enumeration_Type (Etype (N)) then

            case V.T is

               when Cnt_Boolean =>
                  return Boolean_Value (V.Bo);

               when Cnt_Integer =>
                  declare
                     Ui  : constant Uint := UI_From_String (To_String (V.I));
                     Lit : constant Node_Id := Get_Enum_Lit_From_Pos
                       (Etype (N), Ui, No_Location);
                  begin
                     return Enum_Value (Entity (Lit));
                  end;

               when others =>
                  Import_Error ("unexpected value type for enumeration but " &
                                  Cntexmp_Type'Image (V.T));

            end case;

         elsif Is_Boolean_Type (Etype (N)) then

            if V.T /= Cnt_Boolean then
               Import_Error ("not boolean value");
            end if;

            return Boolean_Value (Boolean'Value (To_String (V.B)));

         elsif Is_Record_Type (Etype (N)) then

            if V.T /= Cnt_Record then
               Import_Error ("not record value");
            end if;

            declare
               F : Fields.Map := Fields.Empty;
               E : Entity_Id := First_Entity (Etype (N));
            begin
               while Present (E) loop
                  Fields.Insert
                    (F, E, new Value'(Field_Value (E, V.Fi)));
                  Next_Entity (E);
               end loop;
               return Record_Value (F);
            end;

         else
            Import_Error ("not handled: " &
                            Node_Kind'Image (Nkind (Etype (N))));
         end if;

      exception

         when Exn_RAC_Failure =>
            RAC_Stuck
              ("error in counterexample value: " &
                 Description (Flush_Exn_RAC_Result.Res_VC_Kind));
      end;

      case V.T is

         when Cnt_Integer =>
            if not Is_Integer_Type (Etype (N)) then
               raise Program_Error with "Target of import not signed integer";
            end if;

            if not Is_Signed_Integer_Type (Etype (N)) then
               RAC_Unsupported
                 ("a value could not be imported from the counterexample",
                  Etype (N));
            end if;

            begin
               return Integer_Value (From_String (To_String (V.I)), N);
            exception
               when Exn_RAC_Failure =>
                  RAC_Stuck
                    ("error in counterexample value: " &
                       Description (Flush_Exn_RAC_Result.Res_VC_Kind));
            end;

         when Cnt_Boolean =>
            if not Is_Boolean_Type (Etype (N)) then
               raise Program_Error with "Target of import not boolean";
            end if;

            return Boolean_Value (Boolean'Value (To_String (V.B)));

         when others =>
            RAC_Unsupported ("Import", Cntexmp_Type'Image (V.T));

      end case;
   end Import;

   ---------
   -- Get --
   ---------

   function Get
     (N : Node_Id; Cntexmp : Cntexample_File_Maps.Map) return Opt_Value
   is
      Filename : constant String  := File_Name (Sloc (N));
      Line     : constant Integer :=
                   Integer (Get_Physical_Line_Number (Sloc (N)));
      Files_C  : constant Cntexample_File_Maps.Cursor :=
                   Cntexmp.Find (Filename);
   begin

      if not Cntexample_File_Maps.Has_Element (Files_C) then
         return No_Value;
      else
         declare
            Lines   : Cntexample_Lines renames Cntexmp (Files_C);
            Lines_C : constant Cntexample_Line_Maps.Cursor :=
                        Lines.Other_Lines.Find (Line);
         begin

            if not Cntexample_Line_Maps.Has_Element (Lines_C) then
               return No_Value;
            end if;

            declare
               Elts : Cntexample_Elt_Lists.List renames
                        Lines.Other_Lines (Lines_C);
            begin

               for Elt of Elts loop
                  if Node_Id'Value (To_String (Elt.Name)) = N then
                     return
                       (Present => True,
                        Content => Import (Elt.Value.all, N));
                  end if;
               end loop;

               return No_Value;
            end;
         end;
      end if;

   end Get;

   --------------------
   -- Get_Or_Default --
   --------------------

   function Get
     (N                : Node_Id;
      Ex               : Node_Id;
      Use_Type_Default : Boolean;
      Ctx              : in out Context;
      Origin           : out Value_Origin)
      return Value
   is
      OV  : constant Opt_Value := Get (N, Ctx.Cntexmp);
      Res : Value;
   begin
      if OV.Present then
         Origin := From_Counterexample;
         Res := OV.Content;
      elsif Present (Ex) then
         Origin := From_Expr;
         Res := RAC_Expr (Ex, Ctx);
      elsif Use_Type_Default then
         Origin := From_Type_Default;
         Res := Default_Value (Etype (N));
      else
         RAC_Incomplete
           ("No counterexample value for program parameter " &
              Get_Name_String (Chars (N)));
      end if;
      RAC_Info
        ("Get " & Get_Name_String (Chars (N)) &
           " (" & Value_Origin'Image (Origin) & ")" &
           " = " & To_String (Res));
      return Res;
   end Get;

   ------------------
   -- Find_Binding --
   ------------------

   function Find_Binding
     (E   : N_Defining_Identifier_Id;
      Ctx : in out Context)
      return Access_Binding
   is
      C : Scopes.Cursor;
   begin
      for Scope of Ctx.Env loop
         C := Scopes.Find (Scope, E);

         if Scopes.Has_Element (C) then
            return Scope (C);
         end if;
      end loop;

      --  E must be a global
      --  ??? initialise globals early in Execute? how to find the globals?
      declare
         OV       : constant Opt_Value := Get (E, Ctx.Cntexmp);
         V        : Value;
         S        : Scopes.Map := Ctx.Env (Ctx.Env.Last);
         Inserted : Boolean;
      begin
         if OV.Present then
            V := OV.Content;
         else
            V := RAC_Expr (Expression (Declaration_Node (E)), Ctx);
         end if;
         Scopes.Insert
           (S, E, new Binding'(Val => V, others => <>), C, Inserted);
         RAC_Info ("Global " & Get_Name_String (Chars (E)) &
                     " initialised to " & To_String (V) & " (from " &
                     (if OV.Present then "CE" else "RHS") & ")");
         pragma Assert (Inserted);
         return S (C);
      end;
   end Find_Binding;

   -------------------
   -- Set_Attribute --
   -------------------

   procedure Set_Attribute
     (S : in out Scopes.Map;
      E : N_Defining_Identifier_Id;
      A : Name_Id;
      V : Value)
   is
      C      : Scopes.Cursor;
      Ignore : Boolean;
   begin
      Scopes.Insert (S, E, new Binding'(others => <>), C, Ignore);
      Attributes.Insert (S (C).Attrs, A, V);
   end Set_Attribute;

   ---------------
   -- Set_Value --
   ---------------

   procedure Set_Value
     (S : in out Scopes.Map; E : N_Defining_Identifier_Id; V : Value)
   is
      B        : constant Access_Binding :=
                   new Binding'(Val => V, others => <>);
      C        : Scopes.Cursor;
      Inserted : Boolean;
   begin
      Scopes.Insert (S, E, B, C, Inserted);
      if not Inserted then
         S (C).Val := V;
      end if;
   end Set_Value;

   ------------------
   -- Update_Value --
   ------------------

   procedure Update_Value
     (Env : in out Environments.Vector;
      E   : Entity_Id;
      V   : Value)
   is
      SC : Scopes.Cursor;
   begin
      for EC in Env.Iterate loop
         SC := Env (EC).Find (E);

         if Scopes.Has_Element (SC) then
            Env (EC) (SC).Val := V;
            return;
         end if;
      end loop;

      Write_Str ("Not found");
      Treepr.Print_Tree_Node (E);

      --  E must be a global
      --  ??? initialise globals early?
      Scopes.Insert (Env (Env.Last), E, new Binding'(Val => V, others => <>));
   end Update_Value;

   ----------------------------------------------------------------------------

   ----------------
   -- Check_Node --
   ----------------

   procedure Check_Node
     (N : N_Subexpr_Id; Ctx : in out Context; Desc : String; K : VC_Kind)
   is
      V : Value;
   begin
      RAC_Trace ("check node " & Node_Kind'Image (Nkind (N)));
      V := RAC_Expr (N, Ctx);

      if Value_Boolean (V) then
         RAC_Info (Capitalize (Desc), "is OK", N);
      else
         RAC_Info (Capitalize (Desc), "failed", N);
         RAC_Failure (N, K);
      end if;
   end Check_Node;

   ----------------
   -- Check_List --
   ----------------

   procedure Check_List
     (L   : Node_Lists.List;
      Ctx : in out Context;
      Msg : String;
      K : VC_Kind)
   is
   begin
      for N of L loop
         Check_Node (N, Ctx, Msg, K);
      end loop;
   end Check_List;

   ----------------------------------------------------------------------------

   -------------------------
   -- Check_Fuel_Decrease --
   -------------------------

   procedure Check_Fuel_Decrease (Fuel : in out Integer) is
   begin
      if Fuel = 0 then
         RAC_Incomplete ("out of fuel");
      end if;

      if Fuel > 0 then
         Fuel := Fuel - 1;
      end if;
   end Check_Fuel_Decrease;

   ---------
   -- RAC --
   ---------

   function Execute
     (E : Entity_Id; Cntexmp : Cntexample_File_Maps.Map; Fuel : Integer := -1)
      return Result
   is

      function Global_Scope (Ctx : Context) return Scopes.Map;
      --  Return a scope with global variables

      function Param_Scope (Ctx : in out Context) return Scopes.Map;
      --  Return a scopex

      ------------------
      -- Global_Scope --
      ------------------

      function Global_Scope (Ctx : Context) return Scopes.Map is
         pragma Unreferenced (Ctx);
         --  N : Node_Id := E;
         --
         --  function Process (N : Node_Id) return Atree.Traverse_Result;
         --
         --  function Process (N : Node_Id) return Atree.Traverse_Result is
         --  begin
         --     Write_Line (Node_Kind'Image (Nkind (N)));
         --     case Nkind (N) is
         --        when N_Subprogram_Body | N_Subprogram_Specification =>
         --           return Atree.Skip;
         --        when N_Object_Declaration =>
         --           Treepr.Print_Tree_Node (N);
         --           return Atree.Skip;
         --        when N_Defining_Identifier =>
         --           Treepr.Print_Tree_Node (N);
         --           return Atree.OK;
         --        when others =>
         --           return Atree.OK;
         --     end case;
         --  end Process;
         --
         --  function Traverse is new Atree.Traverse_Func (Process);
         --  Ignore : Atree.Traverse_Final_Result;
      begin
         --  while Present (N) loop
         --     Write_Line ("Scope");
         --     Treepr.Print_Tree_Node (N);
         --
         --     if Nkind (N) = N_Package_Body then
         --        Write_Line ("-- SPEC");
         --        Ignore := Traverse (Corresponding_Spec (N));
         --        Write_Line ("-- BODY");
         --        Ignore := Traverse (N);
         --     end if;
         --
         --     N := Parent (N);
         --  end loop;

         --  for File of Cntexmp loop
         --     for Line of File.Other_Lines loop
         --        for Elt of Line loop
         --           N := Node_Id'Value (To_String (Elt.Name));
         --           Write_Line ("-- Node " & Node_Id'Image (N));
         --           Treepr.Print_Tree_Node (N);
         --        end loop;
         --     end loop;
         --  end loop;
         --  Treepr.Print_Tree_Node (E);
         --  RAC_Unsupported ("Global_Scope", E);
         return Scopes.Empty;
      end Global_Scope;

      -----------------
      -- Param_Scope --
      -----------------

      function Param_Scope (Ctx : in out Context) return Scopes.Map is
         Res    : Scopes.Map := Scopes.Empty;
         Param  : Entity_Id  := First_Formal (E);
         V      : Value;
         Origin : Value_Origin;
      begin
         while Present (Param) loop
            V := Get (Param, Empty, False, Ctx, Origin);
            Scopes.Insert (Res, Param, new Binding'(Val => V, others => <>));
            Next_Formal (Param);
         end loop;
         return Res;
      end Param_Scope;

      Ctx : Context :=
              (Env               => Environments.Empty,
               Cntexmp           => Cntexmp,
               Fuel              => Fuel);

      --  Start of processing for RAC

   begin
      RAC_Trace ("cntexmp: " & Write (To_JSON (Cntexmp), False));
      RAC_Trace ("entry: " & Full_Name (E));
      Environments.Append (Ctx.Env, Global_Scope (Ctx));

      case Ekind (E) is

         when E_Function
            | E_Procedure =>
            declare
               Scope : Scopes.Map         := Param_Scope (Ctx);
               Res   : constant Opt_Value := RAC_Call (E, Ctx, Scope);
            begin
               return
                 (Res_Kind  => Res_Normal,
                  Res_Value => Res);
            end;

         when E_Package
            | E_Package_Body =>
            RAC_Unsupported ("RAC", Entity_Kind'Image (Ekind (E)));

         when others =>
            raise Program_Error with "Cannot execute RAC entity";

      end case;
   exception

      when Exn_RAC_Failure | Exn_RAC_Stuck | Exn_RAC_Incomplete =>
         return Flush_Exn_RAC_Result;

   end Execute;

   --------------
   -- RAC_Decl --
   --------------

   procedure RAC_Decl
     (Decl : Node_Id; Scope : in out Scopes.Map; Ctx : in out Context) is
   begin
      case Nkind (Decl) is

         when N_Object_Declaration =>
            declare
               Origin : Value_Origin;
               V      : Value;
            begin
               --  ??? Permitting default values here assumes that the value
               --      is actually not used in the program
               V := Get (Defining_Identifier (Decl), Expression (Decl), True,
                         Ctx, Origin);
               Set_Value (Scope, Defining_Identifier (Decl), V);
            end;

         when N_Pragma
            | N_Full_Type_Declaration
            | N_Implicit_Label_Declaration
            | N_Freeze_Entity =>
            null;

         when others =>
            RAC_Unsupported ("RAC_Decl", Node_Kind'Image (Nkind (Decl)));

      end case;
   end RAC_Decl;

   ---------------
   -- RAC_Decls --
   ---------------

   procedure RAC_Decls
     (Decls : List_Id; Scope : in out Scopes.Map; Ctx : in out Context)
   is
      Decl : Node_Id := First (Decls);
   begin
      while Present (Decl) loop
         RAC_Decl (Decl, Scope, Ctx);
         Next (Decl);
      end loop;
   end RAC_Decls;

   --------------
   -- RAC_Call --
   --------------

   function RAC_Call
     (E : Entity_Id; Ctx : in out Context;  Scope : in out Scopes.Map)
      return Opt_Value
   is
      Res    : Opt_Value;
      Pres   : constant Node_Lists.List :=
        Find_Contracts (E, Pragma_Precondition);
      Posts  : constant Node_Lists.List :=
        Find_Contracts (E, Pragma_Postcondition);
      E_Body : constant Node_Id := Get_Body (E);
   begin
      RAC_Trace ("call " & Get_Name_String (Chars (E)));
      --  ??? Add 'Old for variables in Env and remove at the end of RAC_Call
      --  ??? Can we (easily) know which variables are used with 'Old in the
      --      postconditions? The loop below is probably adding too much.
      for C in Scope.Iterate loop
         Attributes.Insert
           (Scope (C).Attrs, Snames.Name_Old, Snapshot (Scope (C).Val));
      end loop;
      Environments.Insert (Ctx.Env, 0, Scope);
      RAC_Decls (Declarations (E_Body), Ctx.Env (0), Ctx);
      Check_List (Pres, Ctx, "Precondition", VC_Assert);

      begin
         RAC_Node (Handled_Statement_Sequence (E_Body), Ctx);
         RAC_Trace ("call terminated");
         Res := No_Value;
      exception
         when Exn_RAC_Return =>
            RAC_Trace ("call return");
            Res := Flush_RAC_Return;
      end;

      if Res.Present then
         Set_Attribute (Ctx.Env (0), E, Snames.Name_Result, Res.Content);
      end if;

      Check_List (Posts, Ctx, "Postcondition", VC_Postcondition);
      Environments.Delete_First (Ctx.Env);
      RAC_Trace ("call result of " & Get_Name_String (Chars (E)) &
                   ": " & To_String (Res));
      return Res;
   end RAC_Call;

   --------------
   -- RAC_List --
   --------------

   procedure RAC_List (L : List_Id; Ctx : in out Context) is
      N : Node_Id := First (L);
   begin
      while Present (N) loop
         RAC_Node (N, Ctx);
         Next (N);
      end loop;
   end RAC_List;

   --------------
   -- RAC_Expr --
   --------------

   function RAC_Expr (N : N_Subexpr_Id; Ctx : in out Context) return Value is

      function RAC_Attribute_Reference return Value;

      function RAC_Op_Compare (Left, Right : Value) return Boolean;

      function RAC_Binary_Op return Value;

      function RAC_Unary_Op return Value;

      function RAC_In return Value;

      function RAC_If_Expression return Value;

      -----------------------------
      -- RAC_Attribute_Reference --
      -----------------------------

      function RAC_Attribute_Reference return Value is
      begin

         case Attribute_Name (N) is

            when Snames.Name_Old =>
               declare
                  E : constant Entity_Id := SPARK_Atree.Entity (Prefix (N));
                  B : constant Access_Binding := Find_Binding (E, Ctx);
                  C : constant Attributes.Cursor :=
                        Attributes.Find (B.Attrs, Snames.Name_Old);
               begin
                  return B.Attrs (C);
               end;

            when Snames.Name_Result =>
               declare
                  E : constant Entity_Id := SPARK_Atree.Entity (Prefix (N));
                  B : constant Access_Binding := Find_Binding (E, Ctx);
                  C : constant Attributes.Cursor :=
                        Attributes.Find (B.Attrs, Snames.Name_Result);
               begin
                  return B.Attrs (C);
               end;

            when Snames.Name_First
               | Snames.Name_Last =>

               if not (Is_Integer_Type (Etype (N))) then
                  RAC_Unsupported
                    ("RAC_Attribute_Reference first/last not integer", N);
               end if;

               case Attribute_Name (N) is
                  when Snames.Name_First =>
                     return Integer_Value (Integer'First, N);
                  when Snames.Name_Last =>
                     return Integer_Value (Integer'Last, N);
                  when others =>
                     raise Program_Error;
               end case;

            when Snames.Name_Min
               | Snames.Name_Max =>

               if not (Is_Integer_Type (Etype (N))) then
                  RAC_Unsupported
                    ("RAC_Attribute_Reference min/max not integer", N);
               end if;

               declare
                  Ex : constant Node_Id := First (Expressions (N));
                  I1 : constant Big_Integer :=
                         RAC_Expr (Ex, Ctx).Integer_Content;
                  I2 : constant Big_Integer :=
                         RAC_Expr (Next (Ex), Ctx).Integer_Content;
               begin
                  case Attribute_Name (N) is
                  when Snames.Name_Min =>
                     return Integer_Value (Min (I1, I2), N);
                  when Snames.Name_Max =>
                     return Integer_Value (Max (I1, I2), N);
                  when others =>
                     raise Program_Error;
                  end case;
               end;

            when Snames.Name_Succ
               | Snames.Name_Prev =>

               if not (Is_Enumeration_Type (Etype (N))) then
                  RAC_Unsupported
                    ("RAC_Attribute_Reference succ/prev not enum", N);
               end if;

               declare
                  Ex     : constant Node_Id := First (Expressions (N));
                  Arg    : constant Value := RAC_Expr (Ex, Ctx);
                  Ix     : Uint := Enumeration_Pos (Arg.Enum_Entity);
                  Lit_Ix : Uint := Uint_1;
                  --  ??? ^^ Are enumeration values always starting at 1?
                  Ty     : constant Entity_Id := Etype (N);
                  Lit    : Entity_Id := First_Literal (Ty);
               begin

                  case Attribute_Name (N) is
                     when Snames.Name_Succ =>
                        if Enumeration_Pos (Arg.Enum_Entity) = Esize (Ty) then
                           RAC_Failure (Ex, VC_Range_Check);
                        end if;
                        Ix := Ix + 1;

                     when Snames.Name_Prev =>
                        if Enumeration_Pos (Arg.Enum_Entity) = 1 then
                           RAC_Failure (Ex, VC_Range_Check);
                        end if;
                        Ix := Ix - 1;

                     when others =>
                        RAC_Unsupported
                          ("RAC_Attribute_Reference enumeration", N);
                  end case;

                  --  ??? There is a smarter way to get Ix-th entity, right?
                  while Lit_Ix < Enumeration_Pos (Arg.Enum_Entity) loop
                     Lit_Ix := UI_Add (Lit_Ix, 1);
                     Lit := Next_Literal (Lit);
                  end loop;

                  return Enum_Value (Lit);
               end;

            when Snames.Name_Update =>
               declare
                  F          : Fields.Map;
                  Ex, As, Ch : Node_Id;
                  V          : Value;
               begin
                  --  ??? Copy makes a flat copy, right?
                  F := Fields.Copy
                    (RAC_Expr (Prefix (N), Ctx).Record_Fields);
                  Ex := First (Expressions (N));
                  while Present (Ex) loop
                     As := First (Component_Associations (Ex));
                     while Present (As) loop
                        V := RAC_Expr (Expression (As), Ctx);
                        Ch := First (Choices (As));
                        while Present (Ch) loop
                           for FC in Fields.Iterate (F) loop
                              if
                                Chars (Fields.Key (FC)) = Chars (Ch)
                              then
                                 Fields.Replace_Element
                                   (F, FC, new Value'(Snapshot (V)));
                                 exit;
                              end if;
                           end loop;
                           Next (Ch);
                        end loop;
                        Next (As);
                     end loop;
                     Next (Ex);
                  end loop;
                  return Record_Value (F);
               end;

            when others =>
               RAC_Unsupported
                 ("RAC_Attribute_Reference",
                  Get_Name_String (Attribute_Name (N)));
         end case;
      end RAC_Attribute_Reference;

      --------------------
      -- RAC_Op_Compare --
      --------------------

      function RAC_Op_Compare (Left, Right : Value) return Boolean is
      begin

         case N_Op_Compare (Nkind (N)) is
            when N_Op_Eq =>
               return Left = Right;
            when N_Op_Ne =>
               return Left /= Right;
            when others =>
               pragma Assert (Left.Ty = Right.Ty);

               case Left.Ty is

               when Ty_Integer =>
                  declare
                     L : Big_Integer renames Left.Integer_Content;
                     R : Big_Integer renames Right.Integer_Content;
                  begin
                     case N_Op_Compare (Nkind (N)) is
                        when N_Op_Lt => return L < R;
                        when N_Op_Le => return L <= R;
                        when N_Op_Ge => return L >= R;
                        when N_Op_Gt => return L > R;
                        when others  => raise Program_Error;
                     end case;
                  end;

               when Ty_Enum =>
                  declare
                     L : Unat renames Enumeration_Pos (Left.Enum_Entity);
                     R : Unat renames Enumeration_Pos (Right.Enum_Entity);
                  begin
                     case N_Op_Compare (Nkind (N)) is
                        when N_Op_Lt => return L < R;
                        when N_Op_Le => return L <= R;
                        when N_Op_Ge => return L >= R;
                        when N_Op_Gt => return L > R;
                        when others => raise Program_Error;
                     end case;
                  end;

               when Ty_Record =>
                  RAC_Unsupported ("RAC_Op_Compare on records", N);

               end case;
         end case;
      end RAC_Op_Compare;

         -------------------
         -- RAC_Binary_Op --
      -------------------

      function RAC_Binary_Op return Value is
         Left  : constant Value := RAC_Expr (Left_Opnd (N), Ctx);
         Right : constant Value := RAC_Expr (Right_Opnd (N), Ctx);
      begin
         --  TODO standard operations should be dispatched on
         --  `Entity (N)`, which takes values `Stand.Standard_Op_*`.
         case N_Binary_Op (Nkind (N)) is

            when N_Op_Add =>
               return
                 Integer_Value
                   (Left.Integer_Content + Right.Integer_Content, N);

            when N_Op_Concat =>
               raise Program_Error with "RAC_Expr N_Op_Concat";

            when N_Op_Expon =>
               return Integer_Value
                 (Left.Integer_Content **
                    Natural (To_Integer (Right.Integer_Content)), N);

            when N_Op_Subtract =>
               return
                 Integer_Value
                   (Left.Integer_Content - Right.Integer_Content, N);

            when N_Multiplying_Operator =>

               if Nkind (N) in N_Op_Divide | N_Op_Mod | N_Op_Rem
                 and then
               --  ??? Initialisation with `0` alone triggers
               --      GNAT BUG during compilation!
                 Right.Integer_Content = To_Big_Integer (0)
               then
                  RAC_Failure (N, VC_Division_Check);
               end if;

               return
                 Integer_Value
                   ((case N_Multiplying_Operator (Nkind (N)) is
                       when N_Op_Divide   =>
                          Left.Integer_Content / Right.Integer_Content,
                       when N_Op_Mod      =>
                          Left.Integer_Content mod Right.Integer_Content,
                       when N_Op_Multiply =>
                          Left.Integer_Content * Right.Integer_Content,
                       when N_Op_Rem      =>
                          Left.Integer_Content rem
                            Right.Integer_Content), N);

            when N_Op_Boolean =>
               return
                 Boolean_Value
                   (case N_Op_Boolean (Nkind (N)) is
                       when N_Op_Or  =>
                          Value_Boolean (Left) or else Value_Boolean (Right),
                       when N_Op_And =>
                          Value_Boolean (Left) and then Value_Boolean (Right),
                       when N_Op_Xor =>
                          Value_Boolean (Left) xor Value_Boolean (Right),
                       when others =>
                          RAC_Op_Compare (Left, Right));

            when N_Op_Shift =>
               RAC_Unsupported ("RAC_Expr", N);

         end case;
      end RAC_Binary_Op;

      ------------------
      -- RAC_Unary_Op --
      ------------------

      function RAC_Unary_Op return Value is
         Right : constant Value := RAC_Expr (Right_Opnd (N), Ctx);
      begin

         if Nkind (N) = N_Op_Not then
            return Boolean_Value (not Value_Boolean (Right));
         else
            return
              Integer_Value
                ((case N_Unary_Op (Nkind (N)) is
                    when N_Op_Abs   => abs Right.Integer_Content,
                    when N_Op_Minus => -Right.Integer_Content,
                    when N_Op_Plus  => +Right.Integer_Content,
                    when N_Op_Not   =>
                    --  pragma Assert (False)
                   To_Big_Integer (0)), N);
         end if;

      end RAC_Unary_Op;

      ------------
      -- RAC_In --
      ------------

      function RAC_In return Value is
         Left  : constant Value   := RAC_Expr (Left_Opnd (N), Ctx);
         Right : constant Node_Id := Right_Opnd (N);
         Low   : Big_Integer      := 0;
         High  : Big_Integer      := 0;
      begin
         case Nkind (Right) is

            when N_Identifier | N_Expanded_Name =>
               Get_Type_Range (Etype (Right), Low, High);

            when others =>
               --  Many cases missing ...
               RAC_Unsupported ("RAC_Expr N_In", Right);
         end case;

         return
           Boolean_Value
             (Low <= Left.Integer_Content
              and then Left.Integer_Content <= High);
      end RAC_In;

      -----------------------
      -- RAC_If_Expression --
      -----------------------

      function RAC_If_Expression return Value is
         Cond_Expr : constant Node_Id := First (Expressions (N));
         Then_Expr : constant Node_Id := Next (Cond_Expr);
         Else_Expr : constant Node_Id := Next (Then_Expr);
      begin

         if Value_Boolean (RAC_Expr (Cond_Expr, Ctx)) then
            return RAC_Expr (Then_Expr, Ctx);
         else
            return RAC_Expr (Else_Expr, Ctx);
         end if;

      end RAC_If_Expression;

      --  Begin processing of RAC_Expr

   begin
      RAC_Trace ("expr " & Node_Kind'Image (Nkind (N)), N);
      Check_Fuel_Decrease (Ctx.Fuel);

      case Nkind (N) is

         when N_Integer_Literal =>
            return
              Integer_Value
                (From_Universal_Image (UI_Image (Intval (N))),
                 Etype (N));

         when N_Identifier | N_Expanded_Name =>
            declare
               E : constant Entity_Id := SPARK_Atree.Entity (N);
            begin
               if Ekind (E) = E_Enumeration_Literal then
                  return Enum_Value (E);
               else
                  return Find_Binding (E, Ctx).Val;
               end if;
            end;

         when N_Attribute_Reference =>
            return RAC_Attribute_Reference;

         when N_Binary_Op =>
            return RAC_Binary_Op;

         when N_Unary_Op =>
            return RAC_Unary_Op;

         when N_And_Then =>
            return
              (Boolean_Value
                 (Value_Boolean (RAC_Expr (Left_Opnd (N), Ctx))
                  and then
                  Value_Boolean (RAC_Expr (Right_Opnd (N), Ctx))));

         when N_Or_Else =>
            return
              (Boolean_Value
                 (Value_Boolean (RAC_Expr (Left_Opnd (N), Ctx))
                  or else
                  Value_Boolean (RAC_Expr (Right_Opnd (N), Ctx))));

         when N_In =>
            return RAC_In;

         when N_If_Expression =>
            return RAC_If_Expression;

         when N_Qualified_Expression =>
            --  ??? do range checks?
            return RAC_Expr (Expression (N), Ctx);

         when N_Type_Conversion =>
            --  ??? do range checks?
            return RAC_Expr (Expression (N), Ctx);

         when N_Aggregate =>

            if Is_Record_Type (Etype (N)) then
               declare
                  F : Fields.Map := Fields.Empty;
                  Assoc : Node_Id := First (Component_Associations (N));
                  V : Value;
                  Choice : Node_Id;
               begin
                  while Present (Assoc) loop
                     V := RAC_Expr (Expression (Assoc), Ctx);
                     Choice := First (Choices (Assoc));
                     while Present (Choice) loop
                        Fields.Insert (F, Entity (Choice), new Value'(V));
                        Next (Choice);
                     end loop;
                     Next (Assoc);
                  end loop;
                  return Record_Value (F);
               end;
            else
               RAC_Unsupported ("RAC_Expr aggregate not record", N);
            end if;

         when N_Selected_Component =>
            declare
               F : constant Fields.Map :=
                     RAC_Expr (Prefix (N), Ctx).Record_Fields;
               C : constant Fields.Cursor :=
                     F.Find (Entity (Selector_Name (N)));
            begin
               return F (C).all;
            end;

         when others =>
            RAC_Unsupported ("RAC_Expr", N);
      end case;
   end RAC_Expr;

   -------------------
   -- RAC_Statement --
   -------------------

   procedure RAC_Statement
     (N   : N_Statement_Other_Than_Procedure_Call_Id;
      Ctx : in out Context) is
   begin
      case Nkind (N) is

         when N_Simple_Return_Statement =>

            if Present (Expression (N)) then
               declare
                  Res : constant Value := RAC_Expr (Expression (N), Ctx);
                  Ty  : Entity_Id;
               begin

                  if Res.Ty = Ty_Integer then
                     --  ??? Etype (Expression (N)) is the base type. Is there
                     --  a better way to get the real return type?
                     Ty :=
                       Etype (Return_Applies_To (Return_Statement_Entity (N)));
                     Check_Integer (Res.Integer_Content, Ty, Expression (N));
                  end if;

                  RAC_Return (Some_Value (Res));
               end;
            else
               RAC_Return (No_Value);
            end if;

         when N_Assignment_Statement =>
            declare
               V  : constant Value := RAC_Expr (Expression (N), Ctx);
            begin
               case Nkind (Name (N)) is

                  when N_Identifier =>
                     Update_Value (Ctx.Env, Entity (Name (N)), V);

                  when N_Selected_Component =>
                     declare
                        V1 : Value :=
                               RAC_Expr (Prefix (Name (N)), Ctx);
                        E  : constant Entity_Id :=
                               Entity (Selector_Name (Name (N)));
                     begin
                        Fields.Replace (V1.Record_Fields, E, new Value'(V));
                     end;

                  when others =>
                     RAC_Unsupported ("N_Assignment_Statement", N);
               end case;
            end;

         when N_If_Statement =>

            if Value_Boolean (RAC_Expr (Condition (N), Ctx)) then
               RAC_List (Then_Statements (N), Ctx);
               return;
            end if;

            declare
               Elsif_Part : Node_Id := First (Elsif_Parts (N));
            begin
               while Present (Elsif_Part) loop
                  if
                    Value_Boolean (RAC_Expr (Condition (Elsif_Part), Ctx))
                  then
                     RAC_List (Then_Statements (Elsif_Part), Ctx);
                     return;
                  end if;
                  Next (Elsif_Part);
               end loop;
            end;

            if Present (Else_Statements (N)) then
               RAC_List (Else_Statements (N), Ctx);
            end if;

         when N_Loop_Statement =>
            declare
               Scheme     : constant Node_Id := Iteration_Scheme (N);
               Param_Spec : constant Node_Id :=
                 Loop_Parameter_Specification (Scheme);
            begin
               RAC_Info ("Loop!");

               if Present (Condition (Scheme)) then
                  --  while Cond loop ...
                  begin
                     while
                       Value_Boolean (RAC_Expr (Condition (Scheme), Ctx))
                     loop
                        RAC_List (Statements (N), Ctx);
                     end loop;
                  exception
                     when Exn_RAC_Exit =>
                        null;
                  end;

               elsif Present (Param_Spec) then
                  declare
                     Id         : constant Node_Id :=
                                    Defining_Identifier (Param_Spec);
                     Def        : constant Node_Id :=
                                    Discrete_Subtype_Definition (Param_Spec);
                     Range_Exp  : Node_Id;
                     Low, High  : Value;
                     Test       : access function
                                     (L, R : Valid_Big_Integer) return Boolean;
                     Current    : Big_Integer;
                     Step, Stop : Big_Integer;
                     Val        : Value;
                     Etyp       : Entity_Id;
                  begin
                     case Nkind (Def) is

                     when N_Range =>
                        --  for Id in Low .. High loop ...
                        Low := RAC_Expr (Low_Bound (Def), Ctx);
                        High := RAC_Expr (High_Bound (Def), Ctx);
                        Etyp  := Standard_Integer;

                     when N_Subtype_Indication =>
                        --  for Id in Type range Low High loop ...
                        Range_Exp := Range_Expression (Constraint (Def));
                        Low := RAC_Expr (Low_Bound (Range_Exp), Ctx);
                        High := RAC_Expr (High_Bound (Range_Exp), Ctx);
                        Etyp := Etype (Range_Exp);

                     when others =>
                        RAC_Unsupported ("Loop definition", Def);
                     end case;

                     if Reverse_Present (Param_Spec) then
                        Current := High.Integer_Content;
                        Stop := Low.Integer_Content;
                        Test :=
                          Ada.Numerics.Big_Numbers.Big_Integers.">="'Access;
                        Step := To_Big_Integer (-1);
                     else
                        Current := Low.Integer_Content;
                        Stop := High.Integer_Content;
                        Test :=
                          Ada.Numerics.Big_Numbers.Big_Integers."<="'Access;
                        Step := To_Big_Integer (1);
                     end if;

                     RAC_Trace ("Loop from " & To_String (Current) & " to " &
                                 To_String (Stop) & " by " & To_String (Step));
                     Environments.Insert (Ctx.Env, 0, Scopes.Empty);

                     begin
                        while Test (Current, Stop) loop
                           RAC_Trace ("Iterate: " & To_String (Current));
                           Val := Integer_Value (Current, Etyp, Empty);
                           Set_Value (Ctx.Env (0), Id, Val);
                           RAC_List (Statements (N), Ctx);
                           Current := Current + Step;
                        end loop;
                     exception
                        when Exn_RAC_Exit =>
                           null;
                     end;
                     Environments.Delete_First (Ctx.Env);
                  end;

               elsif Present (Iterator_Specification (Scheme)) then
                  RAC_Unsupported ("RAC_Statement Iterator", N);

               else
                  pragma Assert (False);
               end if;

            end;

         when N_Exit_Statement =>

            if Present (Name (N)) then
               RAC_Unsupported ("RAC_Statement exit statement with name", N);
            end if;

            if not Present (Condition (N))
              or else Value_Boolean (RAC_Expr (Condition (N), Ctx))
            then
               raise Exn_RAC_Exit;
            end if;

         when N_Case_Statement =>
            declare
               V     : constant Value := RAC_Expr (Expression (N), Ctx);
               A     : Node_Id := First (Alternatives (N));
               Ch    : Node_Id;
               Match : Boolean;
            begin
               Outer :
               while Present (A) loop
                  Ch := First (Discrete_Choices (A));
                  Match := False;
                  while Present (Ch) loop

                     if Nkind (Ch) = N_Others_Choice then
                        Match := True;
                     elsif Nkind (Ch) in N_Subexpr then
                        Match := V = RAC_Expr (Ch, Ctx);
                     else
                        RAC_Unsupported ("RAC_Statement choice", Ch);
                     end if;

                     if Match then
                        RAC_List (Statements (A), Ctx);
                        exit Outer;
                     end if;

                     Next (Ch);
                  end loop;

                  Next (A);
               end loop Outer;
            end;

         when others =>
            RAC_Unsupported ("RAC_Statement", N);

      end case;
   end RAC_Statement;

   ----------------
   -- RAC_Pragma --
   ----------------

   procedure RAC_Pragma (N : N_Pragma_Id; Ctx : in out Context) is
      Arg1 : constant Node_Id := First (Pragma_Argument_Associations (N));
      Expr : Node_Id;
      Desc : constant String  :=
        Get_Name_String (Chars (Pragma_Identifier (N)));
   begin
      case Get_Pragma_Id (Pragma_Name (N)) is

         when Pragma_Check =>

            if not Present (Arg1) then
               raise Program_Error with "No arg1 in check pragma";
            end if;

            Expr := Expression (Next (Arg1));
            Check_Node (Expr, Ctx, Desc, VC_Assert);

         when others =>
            RAC_Unsupported
              ("RAC_Pragma",
               Pragma_Id'Image (Get_Pragma_Id (Pragma_Name (N))));
      end case;
   end RAC_Pragma;

   --------------
   -- RAC_Node --
   --------------

   procedure RAC_Node (N : Node_Id; Ctx : in out Context) is
   begin
      RAC_Trace ("node " & Node_Kind'Image (Nkind (N)), N);
      Check_Fuel_Decrease (Ctx.Fuel);

      case Nkind (N) is

         when N_Statement_Other_Than_Procedure_Call =>
            RAC_Statement (N, Ctx);

         when N_Handled_Sequence_Of_Statements =>
            RAC_List (Statements (N), Ctx);

         when N_Pragma =>
            RAC_Pragma (N, Ctx);

         when N_Body_Stub | N_Variable_Reference_Marker =>
            null;

         when others =>
            RAC_Unsupported ("RAC_Node", N);
      end case;
   end RAC_Node;

   ---------
   -- "=" --
   ---------

   function "=" (F1, F2 : Fields.Map) return Boolean is
      C2 : Fields.Cursor;
   begin
      pragma Assert (Fields.Length (F1) = Fields.Length (F2));
      for C1 in F1.Iterate loop
         C2 := F2.Find (Fields.Key (C1));

         if not Fields.Has_Element (C2)
            or else F1 (C1).all /= F2 (C2).all
         then
            return False;
         end if;

      end loop;
      return True;
   end "=";

   ---------
   -- "=" --
   ---------

   function "=" (V1, V2 : Value) return Boolean is
     ((V1.Ty = V2.Ty)
      and then
        (case V1.Ty is
            when Ty_Enum      =>
               V1.Enum_Entity = V2.Enum_Entity,
            when Ty_Integer   =>
               V1.Integer_Content = V2.Integer_Content,
            when Ty_Record    =>
               V1.Record_Fields = V2.Record_Fields));

   -------------------
   -- Boolean_Value --
   -------------------

   function Boolean_Value (B : Boolean) return Value is
     (Ty          => Ty_Enum,
      Enum_Entity => (if B then Standard_True else Standard_False));

   --------------------
   -- Get_Type_Range --
   --------------------

   procedure Get_Type_Range (Ty : Entity_Id; Low, High : out Big_Integer)
   is

      function To_Big_Integer (N : Node_Id) return Big_Integer is
        (From_Universal_Image (UI_Image (SPARK_Atree.Expr_Value (N))));

   begin
      Low := To_Big_Integer (Low_Bound (Scalar_Range (Ty)));
      High := To_Big_Integer (High_Bound (Scalar_Range (Ty)));
   end Get_Type_Range;

   -------------------
   -- Check_Integer --
   -------------------

   procedure Check_Integer (I : Big_Integer; Ty : Entity_Id; N : Node_Id)
   is
      Low, High : Big_Integer;
      Kind      : VC_Kind;
      Desc      : constant String :=
                    "integer check for " & To_String (I) &
                    " for " & Get_Name_String (Chars (Ty));
   begin
      Get_Type_Range (Ty, Low, High);
      Kind :=
        (if Is_Base_Type (Ty) then VC_Overflow_Check else VC_Range_Check);

      if In_Range (I, Low, High) then
         RAC_Info
           (Desc, "is OK as " & VC_Kind'Image (Kind), N);
      else
         RAC_Info
           (Desc, "has failed as " & VC_Kind'Image (Kind), N);
         RAC_Failure (N, Kind);
      end if;

   end Check_Integer;

   -------------------
   -- Integer_Value --
   -------------------

   function Integer_Value
     (I : Big_Integer; Ty : Entity_Id; N : Node_Id) return Value is
   begin
      Check_Integer (I, Ty, N);
      return (Ty => Ty_Integer, Integer_Content => I);
   end Integer_Value;

   -------------------
   -- Default_Value --
   -------------------

   function Default_Value (Ty : Node_Id) return Value is
   begin

      if Is_Integer_Type (Ty) then
         return Integer_Value (0, Ty, Empty);
      elsif Is_Boolean_Type (Ty) then
         return Boolean_Value (False);
      elsif Is_Record_Type (Ty) then
         declare
            F : Fields.Map := Fields.Empty;
            E : Entity_Id := First_Entity (Ty);
         begin
            while Present (E) loop
               Fields.Insert (F, E, new Value'(Default_Value (Etype (E))));
               Next_Entity (E);
            end loop;
            return Record_Value (F);
         end;
      else
         RAC_Unsupported ("Default_Value", Ty);
      end if;

   end Default_Value;

   -------------
   -- Boolean --
   -------------

   function Value_Boolean (V : Value) return Boolean is
   begin

      if V.Ty /= Ty_Enum then
         raise Program_Error with "Boolean";
      end if;

      if V.Enum_Entity = Standard_True then
         return True;
      elsif V.Enum_Entity = Standard_False then
         return False;
      else
         raise Program_Error with "Boolean";
      end if;

   end Value_Boolean;

   --------------
   -- Snapshot --
   --------------

   function Snapshot (F : Fields.Map) return Fields.Map is
      Res : Fields.Map := Fields.Empty;
   begin
      for C in F.Iterate loop
         Fields.Insert (Res, Fields.Key (C), new Value'(Snapshot (F (C).all)));
      end loop;
      return Res;
   end Snapshot;

   --------------
   -- Snapshot --
   --------------

   function Snapshot (V : Value) return Value is
     (case V.Ty is
         when Ty_Integer =>
        (Ty => Ty_Integer, Integer_Content => V.Integer_Content),
         when Ty_Enum    =>
        (Ty => Ty_Enum, Enum_Entity => V.Enum_Entity),
         when Ty_Record  =>
        (Ty => Ty_Record, Record_Fields => Snapshot (V.Record_Fields)));

   Exn_RAC_Result : access Result;
   --  The result of a assertion or assumption failure, set by RAC_Failure,
   --  RAC_Stuck, or RAC_Stuck_For_Failure, retrieved by Flush_RAC_Result.
   --  ??? Is a global variable the right way to add a value to an exception?
   --  ??? Using pointer for optional values ... that doesn't feel like 21st
   --      century :/

   -----------------
   -- RAC_Failure --
   -----------------

   procedure RAC_Failure (N : Node_Id; K : VC_Kind) is
   begin
      Exn_RAC_Result := new Result'
        (Res_Kind    => Res_Failure,
         Res_Node    => N,
         Res_VC_Kind => K,
         Res_VC_Id   => <>);
      raise Exn_RAC_Failure;
   end RAC_Failure;

   -----------------------
   -- Flush_RAC_Failure --
   -----------------------

   function Flush_Exn_RAC_Result return Result is
      Res : Result;
   begin

      if Exn_RAC_Result = null then
         raise Program_Error with "Flush_Exn_RAC_Result";
      end if;

      Res := Exn_RAC_Result.all;
      Exn_RAC_Result := null;
      return Res;
   end Flush_Exn_RAC_Result;

   ---------------
   -- RAC_Stuck --
   ---------------

   procedure RAC_Stuck (Reason : String) is
   begin
      Exn_RAC_Result := new Result'
        (Res_Kind   => Res_Stuck,
         Res_Reason => To_Unbounded_String (Reason));
      raise Exn_RAC_Stuck;
   end RAC_Stuck;

   --------------------
   -- RAC_Incomplete --
   --------------------

   procedure RAC_Incomplete (Reason : String) is
   begin
      Exn_RAC_Result := new Result'
        (Res_Kind   => Res_Incomplete,
         Res_Reason => To_Unbounded_String (Reason));
      raise Exn_RAC_Incomplete;
   end RAC_Incomplete;

   ---------------------
   -- RAC_Unsupported --
   ---------------------

   procedure RAC_Unsupported (Str : String; Str1 : String) is
   begin
      RAC_Incomplete (Str & " not supported for " & Str1);
   end RAC_Unsupported;

   ---------------------
   -- RAC_Unsupported --
   ---------------------

   procedure RAC_Unsupported (Str : String; N : Node_Id) is
      Str1 : Unbounded_String;
   begin
      Write_Str ("Unsupported Node: ");
      Treepr.Print_Tree_Node (N);
      Append (Str1, "node kind " & Node_Kind'Image (Nkind (N)));

      if Present (N) then
         Append (Str1, " at ");
         Append (Str1, File_Name (Sloc (N)));
         Append (Str1, ":");
         Append (Str1, Physical_Line_Number'Image
                 (Get_Physical_Line_Number (Sloc (N))));
      end if;

      RAC_Unsupported (Str, To_String (Str1));
   end RAC_Unsupported;

   Exn_RAC_Return_Value : access Opt_Value;
   --  The return value, set by RAC_Return, retrieved by Flush_RAC_Return
   --  ??? Is a global variable the right way to add a value to an exception?

   ----------------
   -- RAC_Return --
   ----------------

   procedure RAC_Return (V : Opt_Value) is
   begin
      Exn_RAC_Return_Value := new Opt_Value'(V);
      raise Exn_RAC_Return;
   end RAC_Return;

   ----------------------
   -- Flush_RAC_Return --
   ----------------------

   function Flush_RAC_Return return Opt_Value is
      V : Opt_Value;
   begin

      if Exn_RAC_Return_Value = null then
         raise Program_Error with "Flush_RAC_Return";
      end if;

      V := Exn_RAC_Return_Value.all;
      Exn_RAC_Return_Value := null;
      return V;
   end Flush_RAC_Return;

   ---------------
   -- Name_Hash --
   ---------------

   function Name_Hash (N : Name_Id) return Hash_Type is
     (Generic_Integer_Hash (Integer (N)));

   ---------------
   -- To_String --
   ---------------

   function To_String (F : Fields.Map) return String is
      Res : Unbounded_String;
      C : Fields.Cursor := F.First;
   begin
      Res := Res & "(";
      while Fields.Has_Element (C) loop
         Res := Res & Get_Name_String (Chars (Fields.Key (C))) &
           " = " & To_String (F (C).all);
         Fields.Next (C);

         if Fields.Has_Element (C) then
            Res := Res & ", ";
         end if;
      end loop;
      Res := Res & ")";
      return To_String (Res);
   end To_String;

   ---------------
   -- To_String --
   ---------------

   function To_String (V : Value) return String is
     (case V.Ty is
         when Ty_Enum => Get_Name_String (Chars (V.Enum_Entity)),
         when Ty_Integer => To_String (V.Integer_Content),
         when Ty_Record  => To_String (V.Record_Fields));

   ---------------
   -- To_String --
   ---------------

   function To_String (V : Opt_Value) return String is
     (if V.Present then To_String (V.Content) else "NONE");

   ---------------
   -- To_String --
   ---------------

   function To_String (Res : Result) return String is
     (case Res.Res_Kind is
         when Res_Normal       =>
            "NORMAL" & (if Res.Res_Value.Present then
             " (" & To_String (Res.Res_Value.Content) & ")" else ""),
         when Res_Failure      =>
            "FAILURE (" &
            VC_Kind'Image (Res.Res_VC_Kind) &
            " at " & File_Name (Sloc (Res.Res_Node)) & ":" &
            Int'Image (Int (Get_Logical_Line_Number (Sloc (Res.Res_Node)))) &
            ")",
         when Res_Stuck        =>
            "STUCK (" & To_String (Res.Res_Reason) & ")",
         when Res_Incomplete   =>
            "INCOMPLETE (" & To_String (Res.Res_Reason) & ")",
         when Res_Not_Executed =>
            "NOT EXECUTED");

   ---------------
   -- To_String --
   ---------------

   function To_String (Attrs : Attributes.Map) return String is
      Res : Unbounded_String;
   begin
      for C in Attrs.Iterate loop
         Append (Res, " '" & Get_Name_String (Attributes.Key (C)));
         Append (Res, "=" & To_String (Attrs (C)));
      end loop;

      return To_String (Res);
   end To_String;

   ---------------
   -- To_String --
   ---------------

   function To_String (B : Binding) return String is
     (To_String (B.Val) & To_String (B.Attrs));

   ---------------
   -- To_String --
   ---------------

   function To_String (S : Scopes.Map) return String is
      Res : Unbounded_String;
   begin
      for C in S.Iterate loop
         Append (Res, " - " & Get_Name_String (Chars (Scopes.Key (C))));
         Append (Res, ": " & To_String (S (C).all));
      end loop;

      return To_String (Res);
   end To_String;

   ---------------
   -- To_String --
   ---------------

   function To_String (E : Environments.Vector) return String is
      Res : Unbounded_String;
   begin
      for S of E loop
         Append (Res, " -- " & To_String (S));
      end loop;

      return To_String (Res);
   end To_String;

   Do_RAC_Trace : constant Boolean :=
                 Ada.Environment_Variables.Value ("GNATPROVE_RAC_TRACE", "no")
                    = "yes";
   --  Enable RAC_Trace

   Do_RAC_Info : constant Boolean :=
                 Ada.Environment_Variables.Value ("GNATPROVE_RAC_INFO", "no")
                    = "yes";
   --  Enable RAC_Info

   --------------
   -- RAC_Info --
   --------------

   procedure RAC_Info (Ctx : String; Msg : String; N : Node_Id) is
   begin
      if Do_RAC_Info then
         Write_Str ("RAC info: " & Ctx & " " & Msg & " at ");
         Write_Location (Sloc (N));
         Write_Eol;
      end if;
   end RAC_Info;

   --------------
   -- RAC_Info --
   --------------

   procedure RAC_Info (Msg : String) is
   begin
      if Do_RAC_Info then
         Write_Line ("RAC info: " & Msg);
      end if;
   end RAC_Info;

   ---------------
   -- RAC_Trace --
   ---------------

   procedure RAC_Trace (Msg : String; N : Node_Id := Empty) is
   begin
      if Do_RAC_Trace then
         Write_Str ("RAC trace: " & Msg);

         if Present (N) then
            Write_Str (" at ");
            Write_Location (Sloc (N));
         end if;

         Write_Eol;
      end if;
   end RAC_Trace;

   ----------------
   -- Call_Stack --
   ----------------

   procedure Call_Stack is
      Trace  : GNAT.Traceback.Tracebacks_Array (1 .. 1_000);
      Length : Natural;
   begin
      GNAT.Traceback.Call_Chain (Trace, Length);
      Write_Line
        (GNAT.Traceback.Symbolic.Symbolic_Traceback (Trace (1 .. Length)));
   end Call_Stack;
end SPARK_RAC;
