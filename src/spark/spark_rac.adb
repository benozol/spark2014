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
with Ada.Containers.Hashed_Maps;
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
with Ada.Containers; use Ada.Containers;
with Namet; use Namet;
with Common_Containers; use Common_Containers;
with Ada.Exceptions; use Ada.Exceptions;

package body SPARK_RAC is

   ----------------------------------------------------------------------------
   --  Values

   function No_Value return Opt_Value;

   function Some_Value (V : Value) return Opt_Value;

   function Undefined_Value return Value;

   function Integer_Value
     (I              : Valid_Big_Integer;
      N              : Node_Id;
      Do_Range_Check : Boolean;
      Ty             : Node_Id := Empty) return Value;

   function Boolean_Value (B : Boolean) return Value;

   function Default_Value (Etype : Node_Id; N : Node_Id) return Value;

   function Import (V : Cntexmp_Value; N : Node_Id) return Value;

   function "+" (V : Value) return Boolean is
      (V.Boolean_Content);

   ----------------------------------------------------------------------------
   --  Runtime control exceptions

   Exn_RAC_Exit : exception;
   --  Exit loop

   Exn_RAC_Return : exception;
   --  Return from sub-program

   procedure RAC_Return (V : Opt_Value);
   pragma No_Return (RAC_Return);
   --  Return from sub-program, optionally with some return value

   function Flush_RAC_Return return Opt_Value;
   --  Retrieve and reset return value from last call to RAC_Return

   ----------------------------------------------------------------------------
   --  RAC result exceptions

   Exn_RAC_Stuck : exception;
   Exn_RAC_Failure : exception;
   Exn_RAC_Incomplete : exception;

   procedure RAC_Failure (N : Node_Id; K : VC_Kind);
   pragma No_Return (RAC_Failure);
   --  Raise Exn_RAC_Failure

   function Flush_RAC_Failure (Reason : String) return Result;

   function Flush_RAC_Stuck (Reason : String) return Result;

   function Flush_RAC_Incomplete (Reason : String) return Result;

   procedure RAC_Unsupported (Str : String; N : Node_Id);
   pragma No_Return (RAC_Unsupported);
   --  Retrieve and reset the exception from the last call to RAC_Failure

   procedure RAC_Unsupported (Str : String; Str1 : String);
   pragma No_Return (RAC_Unsupported);
   --  Raise Exn_RAC_Incomplete with an exception message

   ----------------------------------------------------------------------------
   --  The evaluation environment and context

   function Name_Hash (N : Name_Id) return Hash_Type;

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

   function To_String (B : Binding) return String;

   package Scopes is new Ada.Containers.Hashed_Maps
     (Key_Type        => Entity_Id,
      Element_Type    => Binding,
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

   --  function Flatten (Env : Environments.Vector) return Scopes.Map;
   --  pragma Unreferenced (Flatten);

   function Find_Binding
     (E : Entity_Id; Env : Environments.Vector) return Binding with
      Pre => Nkind (E) = N_Defining_Identifier;

   procedure Set_Attribute
     (S : in out Scopes.Map; E : Entity_Id; A : Name_Id; V : Value) with
      Pre => Nkind (E) = N_Defining_Identifier;

   procedure Set_Value (S : in out Scopes.Map; E : Entity_Id; V : Value) with
      Pre => Nkind (E) = N_Defining_Identifier;

   procedure Update_Value
     (Env : in out Environments.Vector; E : Entity_Id; V : Value) with
      Pre => Nkind (E) = N_Defining_Identifier;

   type Context is record
      Env               : Environments.Vector;
      --  The variable environment
      Cntexmp           : Cntexample_File_Maps.Map;
      --  The counterexample
      Do_Range_Check    : Boolean;
      --  Set if range checks should be tested
      Use_Type_Defaults : Boolean;
      --  Set if type default values should be used if no value is found in
      --  the counterexample
      Fuel              : Integer;
      --  If Fuel is non-negative, it is decreased by each expression or
      --  statement and execution terminates as incomplete when out of fuel.
   end record;
   --  The execution context

   function Get
     (N : Node_Id; Cntexmp : Cntexample_File_Maps.Map) return Opt_Value;
   --  Get the value of variable N from the counterexample

   function Get_Or_Default
     (N            : Node_Id;
      Ctx          : Context;
      From_Cntexmp : out Boolean) return Value;
   --  Get the value of variable N from the counterexample, or the type default

   ----------------------------------------------------------------------------
   --  Check the validity of annotations

   procedure Type_Range
     (E : Entity_Id; Low : out Big_Integer; High : out Big_Integer);
   --  Set Low and High to the lowest and highest value of the range type E

   procedure Range_Check (I : Valid_Big_Integer; E : Entity_Id; N : Node_Id);

   procedure Check_Node
     (N : Node_Id; Ctx : in out Context; Desc : String; K : VC_Kind) with
      Pre => N in N_Subexpr_Id;

   procedure Check_List
     (L   : Node_Lists.List;
      Ctx : in out Context;
      Msg : String;
      K   : VC_Kind);
   --  Check the validity of formulas L

   function RAC_Expr (N : Node_Id; Ctx : in out Context) return Value with
      Pre => N in N_Subexpr_Id;
   --  Evaluate node N to a value

   procedure Check_Fuel_Decrease (Fuel : in out Integer);
   --  Check fuel and decrease (if non-negative)

   procedure RAC_Statement (N : Node_Id; Ctx : in out Context);
   --  RAC execution of a statement N

   procedure RAC_Pragma (N : Node_Id; Ctx : in out Context);
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

   procedure RAC_Info (Ctx : String; Msg : String; N : Node_Id) with
      Inline;
   --  Print info about RAC checks

   procedure RAC_Info (Msg : String) with
      Inline;
   --  Print info about RAC checks

   procedure RAC_Trace (Msg : String; N : Node_Id := Empty) with
      Inline;
   --  Trace the RAC execution

   ----------------------------------------------------------------------------

   ------------
   -- Import --
   ------------

   function Import (V : Cntexmp_Value; N : Node_Id) return Value is
   begin
      case V.T is

         when Cnt_Integer =>
            if not Is_Integer_Type (Etype (N)) then
               raise Program_Error with "Target of import not signed integer";
            end if;

            if not Is_Signed_Integer_Type (Etype (N)) then
               RAC_Unsupported ("Import", Etype (N));
            end if;

            return Integer_Value (From_String (To_String (V.I)), N, True);

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
      Lines    : Cntexample_Line_Maps.Map;
      Elts     : Cntexample_Elt_Lists.List;
   begin
      if not Cntexmp.Contains (Filename) then
         return No_Value;
      end if;

      Lines := Cntexmp (Filename).Other_Lines;

      if not Lines.Contains (Line) then
         return No_Value;
      end if;

      Elts := Lines (Line);

      for Elt of Elts loop
         if Node_Id'Value (To_String (Elt.Name)) = N then
            return (Present => True, Content => Import (Elt.Value.all, N));
         end if;
      end loop;

      return No_Value;
   end Get;

   --------------------
   -- Get_Or_Default --
   --------------------

   function Get_Or_Default
     (N            : Node_Id;
      Ctx          : Context;
      From_Cntexmp : out Boolean) return Value
   is
      OV : constant Opt_Value := Get (N, Ctx.Cntexmp);
   begin
      From_Cntexmp := OV.Present;

      if OV.Present then
         return OV.Content;
      elsif Ctx.Use_Type_Defaults then
         return Default_Value (Etype (N), N);
      else
         raise Exn_RAC_Incomplete
           with ("No counterexample value for program parameter " &
                   Node_Id'Image (N));
      end if;
   end Get_Or_Default;

   --  function Flatten (Env : Environments.Vector) return Scopes.Map is
   --     use Scopes;
   --     C : Cursor;
   --     Res : Map := Scopes.Empty;
   --  begin
   --     for S of reverse Env loop
   --        C := First (S);
   --        while Has_Element (C) loop
   --           Scopes.Insert (Res, Key (C), S (C));
   --           Next (C);
   --        end loop;
   --     end loop;
   --     return Res;
   --  end Flatten;

   ------------------
   -- Find_Binding --
   ------------------

   function Find_Binding
     (E : Entity_Id; Env : Environments.Vector) return Binding
   is
      C : Scopes.Cursor;
   begin
      for Scope of Env loop
         C := Scope.First;

         while Scopes.Has_Element (C) loop
            Scopes.Next (C);
         end loop;

         C := Scopes.Find (Scope, E);

         if Scopes.Has_Element (C) then
            return Scopes.Element (C);
         end if;
      end loop;

      raise Program_Error
        with
        ("Cannot find binding for variable: " & Get_Name_String (Chars (E)));
   end Find_Binding;

   -------------------
   -- Set_Attribute --
   -------------------

   procedure Set_Attribute
     (S : in out Scopes.Map; E : Entity_Id; A : Name_Id; V : Value)
   is
   begin
      if not S.Contains (E) then
         Scopes.Insert (S, E, (others => <>));
      end if;

      Attributes.Insert (S (E).Attrs, A, V);
   end Set_Attribute;

   ---------------
   -- Set_Value --
   ---------------

   procedure Set_Value (S : in out Scopes.Map; E : Entity_Id; V : Value) is
   begin
      if S.Contains (E) then
         S (E).Val := V;
      else
         Scopes.Insert (S, E, (Val => V, others => <>));
      end if;
   end Set_Value;

   ------------------
   -- Update_Value --
   ------------------

   procedure Update_Value
     (Env : in out Environments.Vector; E : Entity_Id; V : Value)
   is
   begin
      for S of Env loop
         if S.Contains (E) then
            S (E).Val := V;
            return;
         end if;
      end loop;

      raise Program_Error
        with
        ("Cannot find variable for update: " & Get_Name_String (Chars (E)));
   end Update_Value;

   ----------------------------------------------------------------------------

   ----------------
   -- Check_Node --
   ----------------

   procedure Check_Node
     (N : Node_Id; Ctx : in out Context; Desc : String; K : VC_Kind)
   is
      V : Value;
   begin
      RAC_Trace ("check node " & Node_Kind'Image (Nkind (N)));
      V := RAC_Expr (N, Ctx);

      if V.Boolean_Content then
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
         raise Exn_RAC_Incomplete with "out of fuel";
      end if;

      if Fuel > 0 then
         Fuel := Fuel - 1;
      end if;
   end Check_Fuel_Decrease;

   ---------
   -- RAC --
   ---------

   function RAC
     (E : Entity_Id; Cntexmp : Cntexample_File_Maps.Map; Fuel : Integer := -1)
      return Result
   is

      function Global_Scope (Ctx : Context) return Scopes.Map;
      --  Return a scope with global variables

      function Param_Scope (Ctx : Context) return Scopes.Map;
      --  Return a scope

      ------------------
      -- Global_Scope --
      ------------------

      function Global_Scope (Ctx : Context) return Scopes.Map is
         pragma Unreferenced (Ctx);
      begin
         --  TODO
         return Scopes.Empty;
      end Global_Scope;

      -----------------
      -- Param_Scope --
      -----------------

      function Param_Scope (Ctx : Context) return Scopes.Map is
         Res        : Scopes.Map := Scopes.Empty;
         Param      : Entity_Id  := First_Formal (E);
         V          : Value;
         From_Cntexmp : Boolean;
      begin
         while Present (Param) loop

            begin
               V := Get_Or_Default (Param, Ctx, From_Cntexmp);
            exception
               when Constraint_Error =>
                  raise Exn_RAC_Stuck;
            end;

            RAC_Info
              ("Param " & Get_Name_String (Chars (Param)) & " (" &
               Node_Id'Image (Param) & ") = " & To_String (V) &
               (if From_Cntexmp then "" else " (no counterexample value)"));
            Scopes.Insert (Res, Param, (Val => V, others => <>));
            Next_Formal (Param);
         end loop;
         return Res;
      end Param_Scope;

      Ctx : Context :=
              (Env               => Environments.Empty,
               Cntexmp           => Cntexmp,
               Do_Range_Check    => True,
               Use_Type_Defaults => False,
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
                  Res_Value => Res,
                  others    => <>);
            end;

         when E_Package
            | E_Package_Body =>
            RAC_Unsupported ("RAC", Entity_Kind'Image (Ekind (E)));

         when others =>
            raise Program_Error with "Cannot execute RAC entity";

      end case;
   exception

      when Exn_RAC_Failure =>
         return Flush_RAC_Failure ("exception encountered");

      when E : Exn_RAC_Stuck =>
         return Flush_RAC_Stuck (Exception_Message (E));

      when E : Exn_RAC_Incomplete =>
         return Flush_RAC_Incomplete (Exception_Message (E));

   end RAC;

   --------------
   -- RAC_Decl --
   --------------

   procedure RAC_Decl
     (Decl : Node_Id; Scope : in out Scopes.Map; Ctx : in out Context)
   is
   begin
      case Nkind (Decl) is

         when N_Object_Declaration =>
            declare
               E : constant Node_Id := Expression (Decl);
               V : Value;
            begin
               if Present (E) then
                  V := RAC_Expr (E, Ctx);
               else
                  V := Undefined_Value;
               end if;

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
      Res  : Opt_Value;
      Pres : constant Node_Lists.List :=
        Find_Contracts (E, Pragma_Precondition);
      Posts : constant Node_Lists.List :=
        Find_Contracts (E, Pragma_Postcondition);
      E_Body : constant Node_Id := Get_Body (E);
   begin
      RAC_Trace ("call " & Get_Name_String (Chars (E)));
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

   function RAC_Expr
     (N : Node_Id; Ctx : in out Context) return Value
   is
      function Integer_Value (I : Big_Integer) return Value is
        (Integer_Value (I, N, Ctx.Do_Range_Check));
      function RAC_Expr (N : Node_Id) return Value is
         (RAC_Expr (N, Ctx));
   begin
      RAC_Trace ("expr " & Node_Kind'Image (Nkind (N)), N);
      Check_Fuel_Decrease (Ctx.Fuel);

      case Nkind (N) is

         when N_Integer_Literal =>
            return
              Integer_Value (From_Universal_Image (UI_Image (Intval (N))));

         when N_Identifier | N_Expanded_Name =>
            if Entity (N) = Standard_True then
               return Boolean_Value (True);
            elsif Entity (N) = Standard_False then
               return Boolean_Value (False);
            elsif Is_Enumeration_Type (Etype (N)) then
               RAC_Unsupported ("RAC_Expr enumeration literal", N);
            else
               return Find_Binding (SPARK_Atree.Entity (N), Ctx.Env).Val;
            end if;

         when N_Attribute_Reference =>
            if Nkind (Prefix (N)) in N_Identifier | N_Expanded_Name then
               declare
                  E    : constant Entity_Id := SPARK_Atree.Entity (Prefix (N));
                  Bind : constant Binding   := Find_Binding (E, Ctx.Env);
               begin
                  return Bind.Attrs (Attribute_Name (N));
               end;
            else
               RAC_Unsupported ("RAC_Expr attribute reference", Prefix (N));
            end if;

         when N_Binary_Op =>
            declare
               Left  : constant Value := RAC_Expr (Left_Opnd (N));
               Right : constant Value := RAC_Expr (Right_Opnd (N));
            begin
               --  TODO standard operations should be dispatched on
               --  `Entity (N)`, which takes values `Stand.Standard_Op_*`.
               case N_Binary_Op (Nkind (N)) is

                  when N_Op_Add =>
                     return
                       Integer_Value
                         (Left.Integer_Content + Right.Integer_Content);

                  when N_Op_Concat =>
                     raise Program_Error with "RAC_Expr N_Op_Concat";

                  when N_Op_Expon =>
                     RAC_Unsupported ("RAC_Expr Expon", N);

                  when N_Op_Subtract =>
                     return
                       Integer_Value
                         (Left.Integer_Content - Right.Integer_Content);

                  when N_Multiplying_Operator =>

                     if Nkind (N) in N_Op_Divide | N_Op_Mod | N_Op_Rem
                       and then
                        --  TODO Leaving out `To_Big_Integer` triggers
                        --  GNAT BUG during compilation!
                        Right.Integer_Content = To_Big_Integer (0)
                     then
                        RAC_Failure (N, VC_Division_Check);
                     end if;

                     return
                       Integer_Value
                         ((case N_Multiplying_Operator (Nkind (N)) is
                             when N_Op_Divide =>
                               Left.Integer_Content / Right.Integer_Content,
                             when N_Op_Mod =>
                               Left.Integer_Content mod Right.Integer_Content,
                             when N_Op_Multiply =>
                               Left.Integer_Content * Right.Integer_Content,
                             when N_Op_Rem =>
                               Left.Integer_Content rem
                                  Right.Integer_Content));

                  when N_Op_Boolean =>
                     return
                       Boolean_Value
                         (case N_Op_Boolean (Nkind (N)) is
                            when N_Op_Or =>
                              Left.Boolean_Content
                              or else Right.Boolean_Content,
                            when N_Op_And =>
                              Left.Boolean_Content
                              and then Right.Boolean_Content,
                            when N_Op_Xor =>
                              Left.Boolean_Content xor Right.Boolean_Content,
                            when N_Op_Eq => Left = Right,
                            when N_Op_Ne => Left /= Right,
                            when N_Op_Lt =>
                              Left.Integer_Content < Right.Integer_Content,
                            when N_Op_Le =>
                              Left.Integer_Content <= Right.Integer_Content,
                            when N_Op_Ge =>
                              Left.Integer_Content >= Right.Integer_Content,
                            when N_Op_Gt =>
                                Left.Integer_Content > Right.Integer_Content);

                  when N_Op_Shift =>
                     RAC_Unsupported ("RAC_Expr", N);

               end case;
            end;

         when N_Unary_Op =>
            declare
               Right : constant Value := RAC_Expr (Right_Opnd (N));
            begin
               if Nkind (N) = N_Op_Not then
                  return Boolean_Value (not Right.Boolean_Content);
               else
                  return
                    Integer_Value
                      ((case N_Unary_Op (Nkind (N)) is
                          when N_Op_Abs   => abs Right.Integer_Content,
                          when N_Op_Minus => -Right.Integer_Content,
                          when N_Op_Plus  => +Right.Integer_Content,
                          when N_Op_Not   =>
                          --  pragma Assert (False)
                         To_Big_Integer (0)));
               end if;
            end;

         when N_In =>
            declare
               Left  : constant Value   := RAC_Expr (Left_Opnd (N));
               Right : constant Node_Id := Right_Opnd (N);
               Low   : Big_Integer      := 0;
               High  : Big_Integer      := 0;
            begin
               case Nkind (Right) is

                  when N_Identifier =>
                     Type_Range (Etype (Right), Low, High);

                  when others =>
                     --  Many cases missing ...
                     RAC_Unsupported ("RAC_Expr N_In", Right);

               end case;

               return
                 Boolean_Value
                   (Low <= Left.Integer_Content
                    and then Left.Integer_Content <= High);
            end;

         when N_If_Expression =>
            declare
               Test_Expr : constant Node_Id := First (Expressions (N));
               Then_Expr : constant Node_Id := Next (Test_Expr);
               Else_Expr : constant Node_Id := Next (Then_Expr);
            begin
               if RAC_Expr (Test_Expr).Boolean_Content then
                  return RAC_Expr (Then_Expr);
               else
                  return RAC_Expr (Else_Expr);
               end if;
            end;

         when N_Qualified_Expression =>
            if Is_Signed_Integer_Type (Etype (N)) then
               return
                 Integer_Value
                   (RAC_Expr (Expression (N)).Integer_Content,
                    Etype (N), Ctx.Do_Range_Check);
            else
               RAC_Unsupported
                 ("RAC_Expr qualified expression not integer", N);
            end if;

         when N_Type_Conversion =>
            if Is_Signed_Integer_Type (Etype (N)) then
               return
                 Integer_Value
                   (RAC_Expr (Expression (N)).Integer_Content,
                    Etype (N), Ctx.Do_Range_Check);
            else
               RAC_Unsupported ("RAC_Expr type conversion not integer", N);
            end if;

         when others =>
            RAC_Unsupported ("RAC_Expr", N);

      end case;
   end RAC_Expr;

   -------------------
   -- RAC_Statement --
   -------------------

   procedure RAC_Statement (N : Node_Id; Ctx : in out Context) is
   begin
      case N_Statement_Other_Than_Procedure_Call'(Nkind (N)) is

         when N_Simple_Return_Statement =>
            if Present (Expression (N)) then
               declare
                  V : constant Value := RAC_Expr (Expression (N), Ctx);
               begin
                  RAC_Return (Some_Value (V));
               end;
            else
               RAC_Return (No_Value);
            end if;

         when N_Assignment_Statement =>
            declare
               V : constant Value := RAC_Expr (Expression (N), Ctx);
            begin
               Update_Value (Ctx.Env, Entity (Name (N)), V);
            end;

         when N_If_Statement =>
            if +RAC_Expr (Condition (N), Ctx) then
               RAC_List (Then_Statements (N), Ctx);
               return;
            end if;

            declare
               Elsif_Part : Node_Id := First (Elsif_Parts (N));
            begin
               while Present (Elsif_Part) loop
                  if +RAC_Expr (Condition (Elsif_Part), Ctx) then
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
                     while +RAC_Expr (Condition (Scheme), Ctx) loop
                        RAC_List (Statements (N), Ctx);
                     end loop;
                  exception
                     when Exn_RAC_Exit =>
                        null;
                  end;
               elsif Present (Param_Spec) then
                  declare
                     Id          : constant Node_Id :=
                                     Defining_Identifier (Param_Spec);
                     Def         : constant Node_Id :=
                                     Discrete_Subtype_Definition (Param_Spec);
                     Range_Exp   : Node_Id;
                     Low, High   : Value;
                     Test        :
                     access function (L, R : Valid_Big_Integer) return Boolean;
                     Current, Step, Stop : Big_Integer;
                     Val                 : Value;
                     Etyp                : Entity_Id;
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
                        Treepr.Print_Tree_Node (Def);
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
                           Val := Integer_Value (Current, N, True, Etyp);
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
              or else +RAC_Expr (Condition (N), Ctx)
            then
               raise Exn_RAC_Exit;
            end if;

         when others =>
            RAC_Unsupported ("RAC_Statement", N);

      end case;
   end RAC_Statement;

   ----------------
   -- RAC_Pragma --
   ----------------

   procedure RAC_Pragma (N : Node_Id; Ctx : in out Context) is
      Arg1 : constant Node_Id := First (Pragma_Argument_Associations (N));
      Expr : Node_Id          := Empty;
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

   ----------------------------------------------------------------------------

   ---------
   -- "=" --
   ---------

   function "=" (V1, V2 : Value) return Boolean is
     ((V1.Ty = V2.Ty)
      and then
      (case V1.Ty is
         when Ty_Boolean   => V1.Boolean_Content = V2.Boolean_Content,
         when Ty_Integer   => V1.Integer_Content = V2.Integer_Content,
         when Ty_Undefined => False));

   --------------
   -- No_Value --
   --------------

   function No_Value return Opt_Value is (Present => False);

   ----------------
   -- Some_Value --
   ----------------

   function Some_Value (V : Value) return Opt_Value is
     (Present => True, Content => V);

   ---------------------
   -- Undefined_Value --
   ---------------------

   function Undefined_Value return Value is (Ty => Ty_Undefined);

   -------------------
   -- Boolean_Value --
   -------------------

   function Boolean_Value (B : Boolean) return Value is
     (Ty => Ty_Boolean, Boolean_Content => B);

   ----------------
   -- Type_Range --
   ----------------

   procedure Type_Range (E : Entity_Id; Low, High : out Big_Integer) is
      Low_Str : constant String :=
        UI_Image (SPARK_Atree.Expr_Value (Type_Low_Bound (E)));
      High_Str : constant String :=
        UI_Image (SPARK_Atree.Expr_Value (Type_High_Bound (E)));
   begin
      High := From_Universal_Image (High_Str);
      Low  := From_Universal_Image (Low_Str);
   end Type_Range;

   -----------------
   -- Range_Check --
   -----------------

   procedure Range_Check (I : Valid_Big_Integer; E : Entity_Id; N : Node_Id) is
      Low  : Big_Integer := 0;
      High : Big_Integer := 0;
   begin
      Type_Range (E, Low, High);

      if not In_Range (I, Low, High) then
         RAC_Failure (N, VC_Range_Check);
      end if;
   end Range_Check;

   -------------------
   -- Integer_Value --
   -------------------

   function Integer_Value
     (I              : Valid_Big_Integer;
      N              : Node_Id;
      Do_Range_Check : Boolean;
      Ty             : Node_Id := Empty) return Value
   is
   begin
      if Do_Range_Check then
         Range_Check (I, (if Ty = Empty then Etype (N) else Ty), N);
      end if;

      return (Ty => Ty_Integer, Integer_Content => I);
   end Integer_Value;

   -------------------
   -- Default_Value --
   -------------------

   function Default_Value (Etype : Node_Id; N : Node_Id) return Value is
   begin
      if Is_Integer_Type (Etype) then
         return Integer_Value (0, N, True);
      elsif Is_Boolean_Type (Etype) then
         return Boolean_Value (False);
      else
         RAC_Unsupported ("Default_Value", Etype);
      end if;
   end Default_Value;

   ----------------------------------------------------------------------------

   Exn_RAC_Return_Value : Opt_Value := No_Value;

   ----------------
   -- RAC_Return --
   ----------------

   procedure RAC_Return (V : Opt_Value) is
   begin
      Exn_RAC_Return_Value := V;
      raise Exn_RAC_Return;
   end RAC_Return;

   ----------------------
   -- Flush_RAC_Return --
   ----------------------

   function Flush_RAC_Return return Opt_Value is
      V : constant Opt_Value := Exn_RAC_Return_Value;
   begin
      Exn_RAC_Return_Value := No_Value;
      return V;
   end Flush_RAC_Return;

   Exn_RAC_Failure_Node    : Node_Id      := Empty;
   Exn_RAC_Failure_VC_Kind : VC_Kind := VC_Dead_Code;  -- placeholder

   -----------------
   -- RAC_Failure --
   -----------------

   procedure RAC_Failure (N : Node_Id; K : VC_Kind) is
   begin
      Exn_RAC_Failure_Node    := N;
      Exn_RAC_Failure_VC_Kind := K;
      raise Exn_RAC_Failure;
   end RAC_Failure;

   -----------------------
   -- Flush_RAC_Failure --
   -----------------------

   function Flush_RAC_Failure (Reason : String) return Result is
      Res : constant Result :=
              (Res_Kind    => Res_Failure,
               Res_Reason  => To_Unbounded_String (Reason),
               Res_Node    => Exn_RAC_Failure_Node,
               Res_VC_Kind => Exn_RAC_Failure_VC_Kind,
               Res_VC      => <>);
   begin
         Exn_RAC_Failure_Node := Empty;
         Exn_RAC_Failure_VC_Kind := VC_Dead_Code;
         return Res;
   end Flush_RAC_Failure;

   ---------------------
   -- Flush_RAC_Stuck --
   ---------------------

   function Flush_RAC_Stuck (Reason : String) return Result is
      (Res_Kind   => Res_Stuck,
       Res_Reason => To_Unbounded_String (Reason));

   --------------------------
   -- Flush_RAC_Incomplete --
   --------------------------

   function Flush_RAC_Incomplete (Reason : String) return Result is
      (Res_Kind    => Res_Incomplete,
        Res_Reason => To_Unbounded_String (Reason));

   ---------------------
   -- RAC_Unsupported --
   ---------------------

   procedure RAC_Unsupported (Str : String; Str1 : String) is
   begin
      raise Exn_RAC_Incomplete with (Str & " not supported: " & Str1);
   end RAC_Unsupported;

   ---------------------
   -- RAC_Unsupported --
   ---------------------

   procedure RAC_Unsupported (Str : String; N : Node_Id) is
      Str1 : Unbounded_String := To_Unbounded_String ("");
   begin
      Append (Str1, Node_Kind'Image (Nkind (N)));

      if N /= Empty then
         Append (Str1, " at ");
         Append (Str1, File_Name (Sloc (N)));
         Append (Str1, ":");
         Append
           (Str1,
            Physical_Line_Number'Image (Get_Physical_Line_Number (Sloc (N))));
      end if;

      RAC_Unsupported (Str, To_String (Str1));
   end RAC_Unsupported;

   ----------------------------------------------------------------------------

   ---------------
   -- Name_Hash --
   ---------------

   function Name_Hash (N : Name_Id) return Hash_Type is
     (Generic_Integer_Hash (Integer (N)));

   ---------------
   -- To_String --
   ---------------

   function To_String (V : Value) return String is
     (case V.Ty is when Ty_Boolean => Boolean'Image (V.Boolean_Content),
        when Ty_Integer            => To_String (V.Integer_Content),
        when Ty_Undefined          => "UNDEFINED");

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
             " (Value = " & To_String (Res.Res_Value.Content) & ")" else ""),
         when Res_Failure      =>
            "FAILURE (" &
            VC_Kind'Image (Res.Res_VC_Kind) &
            " at " & File_Name (Sloc (Res.Res_Node)) & ":" &
            Int'Image (Int (Get_Logical_Line_Number (Sloc (Res.Res_Node)))) &
            ")",
         when Res_Stuck        =>
            "STUCK (Reason = " & To_String (Res.Res_Reason) & ")",
         when Res_Incomplete   =>
            "INCOMPLETE (Reason = " & To_String (Res.Res_Reason) & ")",
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
         Append (Res, "=" & To_String (Attributes.Element (C)));
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
         Append (Res, ": " & To_String (Scopes.Element (C)));
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

   ----------------------------------------------------------------------------

   --------------
   -- RAC_Info --
   --------------

   procedure RAC_Info (Ctx : String; Msg : String; N : Node_Id) is
   begin
      if
        Ada.Environment_Variables.Value ("GNATPROVE_RAC_INFO", "no") = "yes"
      then
         Write_Str ("RAC: " & Ctx & " " & Msg & " at ");
         Write_Location (Sloc (N));
         Write_Eol;
      end if;
   end RAC_Info;

   --------------
   -- RAC_Info --
   --------------

   procedure RAC_Info (Msg : String) is
   begin
      if
        Ada.Environment_Variables.Value ("GNATPROVE_RAC_INFO", "no") = "yes"
      then
         Write_Line ("RAC: " & Msg);
      end if;
   end RAC_Info;

   ---------------
   -- RAC_Trace --
   ---------------

   procedure RAC_Trace (Msg : String; N : Node_Id := Empty) is
   begin
      if
        Ada.Environment_Variables.Value ("GNATPROVE_RAC_TRACE", "no") = "yes"
      then
         Write_Str ("RAC: " & Msg);

         if N /= Empty then
            Write_Str (" at ");
            Write_Location (Sloc (N));
         end if;

         Write_Eol;
      end if;
   end RAC_Trace;
end SPARK_RAC;
