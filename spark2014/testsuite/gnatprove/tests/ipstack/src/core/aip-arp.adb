------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

with AIP.ARPH;
with AIP.Conversions;
with AIP.EtherH;

package body AIP.ARP is

   ARP_Table : array (ARP_Entry_Id) of ARP_Entry;
   ARP_Free_List   : Any_ARP_Entry_Id;
   ARP_Active_List : Any_ARP_Entry_Id;

   --------------
   -- ARP_Find --
   --------------

   procedure ARP_Find
     (Addr     : IPaddrs.IPaddr;
      Id       : out Any_ARP_Entry_Id;
      Allocate : Boolean)
   is
      Last_Active_Id : Any_ARP_Entry_Id;
   begin
      --  First look for address in active list

      Id := ARP_Active_List;
      Scan_ARP_Entries : while Id /= No_ARP_Entry loop
         if ARP_Table (Id).Dst_IP_Address = Addr then
            --  Entry found

            ARP_Unlink (ARP_Active_List, Id);
            exit Scan_ARP_Entries;
         end if;

         --  Record entry as candidate for recycling, unless it is marked as
         --  permanent.

         if not ARP_Table (Id).Permanent then
            Last_Active_Id := Id;
         end if;

         Id := ARP_Table (Id).Next;
      end loop Scan_ARP_Entries;

      --  Entry not found, try to allocate a new one if requested

      if Id = No_ARP_Entry and then Allocate then
         if ARP_Free_List /= No_ARP_Entry then

            --  Allocate from free list if possible

            Id := ARP_Free_List;
            ARP_Unlink (ARP_Free_List, Id);

         elsif Last_Active_Id /= No_ARP_Entry then

            --  If free list is empty, recycle oldest active entry

            Id := Last_Active_Id;
            ARP_Unlink (ARP_Active_List, Id);
         end if;

         if Id /= No_ARP_Entry then

            --  Initialize newly-allocated entry

            declare
               New_Entry : ARP_Entry renames ARP_Table (Id);
            begin
               ARP_Reset (New_Entry);
               New_Entry.Dst_IP_Address := Addr;
            end;
         end if;
      end if;

      --  If entry found or allocated, mark it as active now and insert it at
      --  the head of the active list.

      if Id /= No_ARP_Entry then
         ARP_Prepend (ARP_Active_List, Id);
         ARP_Table (Id).Timestamp := Time_Types.Now;
      end if;
   end ARP_Find;

   --------------------
   -- ARP_Initialize --
   --------------------

   procedure ARP_Initialize is
   begin
      for J in ARP_Table'Range loop
         ARP_Table (J).State := Unused;
         ARP_Table (J).Next := J - 1;
      end loop;
      ARP_Free_List := ARP_Table'Last;
   end ARP_Initialize;

   ---------------
   -- ARP_Input --
   ---------------

   procedure ARP_Input
     (Nid                : NIF.Netif_Id;
      Netif_MAC_Addr_Ptr : System.Address;
      Buf                : Buffers.Buffer_Id)
   is
      Err  : Err_T := NOERR;

      Ehdr : EtherH.Ether_Header;
      for Ehdr'Address use Buffers.Buffer_Payload (Buf);
      pragma Import (Ada, Ehdr);

      Ahdr : ARPH.ARP_Header;
      for Ahdr'Address use
        Conversions.Ofs (Buffers.Buffer_Payload (Buf), Ehdr'Size / 8);
      pragma Import (Ada, Ahdr);

      Ifa : constant IPaddrs.IPaddr := NIF.NIF_Addr (Nid);

      Local : Boolean;

      Netif_MAC : Ethernet_Address;
      for Netif_MAC'Address use Netif_MAC_Addr_Ptr;
      pragma Import (Ada, Netif_MAC);

   begin
      if Buffers.Buffer_Len (Buf) < Ahdr'Size / 8
           or else
         ARPH.ARPH_Hardware_Type (Ahdr) /= ARPH.ARP_Hw_Ethernet
           or else
         ARPH.ARPH_Protocol (Ahdr) /= EtherH.Ether_Type_IP
           or else
         ARPH.ARPH_Hw_Len (Ahdr) /= Ethernet_Address'Size / 8
           or else
         ARPH.ARPH_Pr_Len (Ahdr) /= IPaddrs.IPaddr'Size / 8
      then
         --  Discard packet if short, or if not a consistent Ethernet/IP ARP
         --  message.

         Err := ERR_USE;
      end if;

      if No (ERR) then
         Local := Ifa /= IPaddrs.IP_ADDR_ANY
                    and then Ifa = ARPH.ARPH_Dst_Ip_Address (Ahdr);

         --  Update entry for sender. If message is to us, assume we'll need to
         --  talk back to them, and allocate a new entry if none exists.

         ARP_Update
           (Nid,
            ARPH.ARPH_Src_Eth_Address (Ahdr),
            ARPH.ARPH_Src_IP_Address (Ahdr),
            Allocate => Local,
            Err      => Err);
      end if;

      if No (Err) then
         case ARPH.ARPH_Operation (Ahdr) is
            when ARPH.ARP_Op_Request =>
               if Local then
                  --  Send ARP reply, reusing original buffer

                  EtherH.Set_EtherH_Dst_MAC_Address (Ehdr,
                    EtherH.EtherH_Src_MAC_Address (Ehdr));
                  EtherH.Set_EtherH_Src_MAC_Address (Ehdr, Netif_MAC);

                  ARPH.Set_ARPH_Operation (Ahdr, ARPH.ARP_Op_Reply);

                  ARPH.Set_ARPH_Dst_Eth_Address (Ahdr,
                    ARPH.ARPH_Src_Eth_Address (Ahdr));
                  ARPH.Set_ARPH_Dst_IP_Address (Ahdr,
                    ARPH.ARPH_Src_IP_Address  (Ahdr));

                  ARPH.Set_ARPH_Src_Eth_Address (Ahdr, Netif_MAC);
                  ARPH.Set_ARPH_Src_IP_Address  (Ahdr, Ifa);

                  NIF.Low_Level_Output (Nid, Buf);
               end if;

            when ARPH.ARP_Op_Reply =>
               --  We updated the cache already, nothing more to do

               null;

            when others =>
               --  Invalid ARP operation, discard

               null;
         end case;
      end if;

      --  Free received packet

      Buffers.Buffer_Blind_Free (Buf);
   end ARP_Input;

   ----------------
   -- ARP_Output --
   ----------------

   procedure ARP_Output
     (Nid         : NIF.Netif_Id;
      Buf         : Buffers.Buffer_Id;
      Dst_Address : IPaddrs.IPaddr)
   is
      pragma Unreferenced (Nid);
      AEID : Any_ARP_Entry_Id;
   begin
      ARP_Find (Dst_Address, AEID, Allocate => True);
      if AEID /= No_ARP_Entry then
         declare
            AE : ARP_Entry renames ARP_Table (AEID);
         begin
            case AE.State is
               when Unused     =>
                  --  Cannot happend
                  raise Program_Error;

               when Active     =>
                  --  Call netif low level output callback
                  --  TBD
                  raise Program_Error;

               when Incomplete =>
                  --  Park packet on entry's pending list

                  Buffers.Append_Packet (AE.Packet_Queue, Buf);
            end case;
         end;
      else
         --  Unable to find or allocate ARP entry, discard packet

         null;
      end if;
   end ARP_Output;

   -----------------
   -- ARP_Prepend --
   -----------------

   procedure ARP_Prepend
     (List : in out Any_ARP_Entry_Id;
      AEID : ARP_Entry_Id)
   is
      AE : ARP_Entry renames ARP_Table (AEID);
   begin
      pragma Assert (AE.Prev = No_ARP_Entry);
      AE.Next := List;
      if List /= No_ARP_Entry then
         ARP_Table (List).Prev := AEID;
      end if;
      List := AEID;
   end ARP_Prepend;

   ---------------
   -- ARP_Timer --
   ---------------

   procedure ARP_Timer is
   begin
      null;
      --  TBD???
   end ARP_Timer;

   ----------------
   -- ARP_Unlink --
   ----------------

   procedure ARP_Unlink
     (List : in out Any_ARP_Entry_Id;
      AEID : ARP_Entry_Id)
   is
      AE : ARP_Entry renames ARP_Table (AEID);
   begin
      if List = AEID then
         List := AE.Next;
      else
         pragma Assert (AE.Prev /= No_ARP_Entry);
         ARP_Table (AE.Prev).Next := AE.Next;
      end if;
      AE.Prev := No_ARP_Entry;
      AE.Next := No_ARP_Entry;
   end ARP_Unlink;

   ----------------
   -- ARP_Update --
   ----------------

   procedure ARP_Update
     (Nid         : NIF.Netif_Id;
      Eth_Address : Ethernet_Address;
      IP_Address  : IPaddrs.IPaddr;
      Allocate    : Boolean;
      Err         : out Err_T)
   is
      pragma Unreferenced (Nid);
      AEID : Any_ARP_Entry_Id;

      Packet_Buf : Buffers.Buffer_Id;
   begin
      Err := NOERR;

      ARP_Find (IP_Address, AEID, Allocate => Allocate);
      if AEID = No_ARP_Entry then
         Err := ERR_MEM;
      end if;

      if No (Err) then
         declare
            AE : ARP_Entry renames ARP_Table (AEID);
         begin
            AE.State := Active;
            AE.Dst_MAC_Address := Eth_Address;

            Flush_Queue : loop
               Buffers.Remove_Packet (AE.Packet_Queue, Packet_Buf);
               exit Flush_Queue when Packet_Buf = Buffers.NOBUF;

               --  Send out Packet_Buf???
            end loop Flush_Queue;
         end;
      end if;
   end ARP_Update;

   ---------------
   -- ARP_Reset --
   ---------------

   procedure ARP_Reset (AE : in out ARP_Entry) is
   begin
      AE.State     := Incomplete;
      AE.Permanent := False;
      AE.Timestamp := Time_Types.Time'First;
   end ARP_Reset;

   --------------
   -- IP_Input --
   --------------

   procedure IP_Input
     (Nid   : NIF.Netif_Id;
      Buf   : Buffers.Buffer_Id)
   is
   begin
      --  TBD
      raise Program_Error;
   end IP_Input;

end AIP.ARP;
