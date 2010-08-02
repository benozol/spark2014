------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                              O U T P U T S                               --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010, AdaCore                        --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute it and/or modify it   --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. gnat2why is distributed in the hope that it will  be  useful,   --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHAN-  --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Wide_Text_IO; use Ada.Wide_Text_IO;

package Outputs is

   type Output_Record is limited private;

   procedure Open_Output
     (O        : in out Output_Record;
      Filename : String);
   procedure Close_Output (O : in out Output_Record);

   procedure Absolute_Indent (O : in out Output_Record; Level : Natural);
   procedure Relative_Indent (O : in out Output_Record; Diff : Integer);

   procedure P  (O : in out Output_Record; S : Wide_String);
   procedure PL (O : in out Output_Record; S : Wide_String);
   procedure NL (O : in out Output_Record);

private

   type Output_Record is limited record
      File     : File_Type;
      Indent   : Natural := 0;
      New_Line : Boolean := False;
   end record;

end Outputs;
