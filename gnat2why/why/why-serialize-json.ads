with GNATCOLL.JSON; use GNATCOLL.JSON;
with GNATCOLL.Strings; use GNATCOLL.Strings;

package Why.Serialize_Json is
   function Why_Node_Id_To_Json (N : Why_Node_Id) return JSON_Value_Type;
begin

