------------------------------------------------------------------------------
--                                                                          --
--                            HI-LITE COMPONENTS                            --
--                                                                          --
--                         S T R I N G - U T I L S                          --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010-2011, AdaCore                   --
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
-- hi-lite is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Containers.Indefinite_Doubly_Linked_Lists;

package String_Utils is
   package String_Lists is new
      Ada.Containers.Indefinite_Doubly_Linked_Lists (String);

   function Ends_With (Str, Suffix : String) return Boolean;
   --  return True when Str ends with Suffix

   function Starts_With (Str, Prefix : String) return Boolean;
   --  Check if Str starts with Prefix

   function Int_Image (N : Integer) return String;
   --  Generate a string from an Integer, without the leading space.

end String_Utils;
