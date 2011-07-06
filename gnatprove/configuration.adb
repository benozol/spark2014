------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                         C O N F I G U R A T I O N                        --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2011, AdaCore                   --
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

with Ada.Text_IO;

with GNAT.Command_Line; use GNAT.Command_Line;
with GNAT.OS_Lib;

with Call;              use Call;

package body Configuration is

   ----------
   -- Init --
   ----------

   procedure Init (Tree : out Project_Tree)
   is
      Proj_Env  : Project_Environment_Access;
      GNAT_Version : GNAT.Strings.String_Access;
   begin
      Initialize (Proj_Env);
      Set_Path_From_Gnatls (Proj_Env.all, "gnatls", GNAT_Version);
      Set_Object_Subdir (Proj_Env.all, Subdir_Name);
      Tree.Load
        (GNATCOLL.VFS.Create (Filesystem_String (Project_File.all)),
         Proj_Env);
   end Init;

   -----------------------
   -- Read_Command_Line --
   -----------------------

   procedure Read_Command_Line
   is
      Config           : Command_Line_Configuration;
      Argument_Present : Boolean := False;
   begin
      --  Install command line config

      Define_Switch (Config, Verbose'Access,
                     "-v", Long_Switch => "--verbose",
                     Help => "Output extra verbose information");

      Define_Switch (Config, MMode_Input'Access,
                     Long_Switch => "--mode=",
                     Help =>
                       "Set the mode of GNATprove (detect | force | check)");

      Define_Switch (Config, Report_Input'Access,
                     Long_Switch => "--report=",
                     Help => "Set the report mode of GNATprove (all | fail)");

      Define_Switch
         (Config,
          Force'Access,
          "-f",
          Help => "Force recompilation / proving of all units and all VCs");

      Define_Switch
         (Config,
          Quiet'Access,
          "-q",
          Long_Switch => "--quiet",
          Help => "Be quiet/terse");

      Define_Switch
         (Config,
          Debug'Access,
          "-d",
          Long_Switch => "--debug",
          Help => "Debug mode");

      Define_Switch
        (Config,
         No_Proof'Access,
         Long_Switch => "--no-proof",
         Help => "Disable proof of VCs, only generate VCs");

      Define_Switch
         (Config, Timeout'Access,
          Long_Switch => "--timeout=",
          Help => "Set the timeout for Alt-Ergo in seconds (default is 10)");

      Define_Switch
         (Config, Steps'Access,
          Long_Switch => "--steps=",
          Help => "Set the maximum number of proof steps for Alt-Ergo");

      Define_Switch
         (Config, Parallel'Access,
          Long_Switch => "-j:",
          Help => "Set the number of parallel processes (default is 1)");

      Define_Switch (Config, Project_File'Access,
                     "-P:",
                     Help => "The name of the project file");

      Getopt (Config);
      if MMode_Input.all = "detect" or else MMode_Input.all = "" then
         MMode := GPM_Detect;
      elsif MMode_Input.all = "force" then
         MMode := GPM_Force;
      elsif MMode_Input.all = "check" then
         MMode := GPM_Check;
      elsif MMode_Input.all = "prove" then
         MMode := GPM_Prove;
      else
         Abort_With_Message ("mode should be one of (detect | force | check)");
      end if;

      if Report_Input.all = "fail" or else Report_Input.all = "" then
         Report := False;
      elsif Report_Input.all = "all" then
         Report := True;
      else
         Abort_With_Message ("report should be one of (all | fail)");
      end if;

      --  Read the command line arguments in Arg_List and set Argument_Present
      --  to True if there are any

      loop
         declare
            Arg : constant String :=
               Get_Argument (Do_Expansion => True);
         begin
            exit when Arg'Length = 0;
            Argument_Present := True;
            File_List.Append (Arg);
         end;
      end loop;

      --  Detect the call mode of GNATprove and check for compatibility with
      --  feature mode

      if Argument_Present then
         if not (MMode in GP_Alfa_Detection_Mode) then
            Abort_With_Message ("mode should be one of (detect | force)");
         end if;
         if Project_File.all = "" then
            Call_Mode := GPC_Only_Files;
         else
            Call_Mode := GPC_Project_Files;
         end if;
      else
         if Project_File.all = "" then
            Abort_With_Message ("No project and no source file given.");
         else
            Call_Mode := GPC_Project;
         end if;
      end if;

   exception
      when Invalid_Switch | Exit_From_Command_Line =>
         GNAT.OS_Lib.OS_Exit (1);
      when Invalid_Parameter =>
         Ada.Text_IO.Put_Line
           (Ada.Text_IO.Standard_Error,
            "No parameter given to switch -" & Full_Switch);
         GNAT.OS_Lib.OS_Exit (1);
   end Read_Command_Line;

end Configuration;
