with GNATCOLL.JSON;    use GNATCOLL.JSON;
with Outputs;          use Outputs;
with Why.Atree.Tables; use Why.Atree.Tables;
with Gnat2Why.Util;    use Gnat2Why.Util;
with WHy.Types; use Why.Types;

package Why.Serialize_Json is
   function Why_Node_Id_To_Json (N : Why_Node_Id) return JSON_Value;
   function Why_Node_List_To_Json (L : Why_Node_Lists.List) return JSON_Value;
end Why.Serialize_Json;
