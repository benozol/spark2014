with GNATCOLL.JSON;    use GNATCOLL.JSON;
with Why.Atree.Tables; use Why.Atree.Tables;

with Why.Atree;    use Why.Atree;

package Why.Atree.To_Json is
   function Why_Node_To_Json (Node : Why_Node) return JSON_Value;
   function Why_Node_Lists_List_To_Json (L : Why_Node_Lists.List)
      return JSON_Value;
end Why.Atree.To_Json;
