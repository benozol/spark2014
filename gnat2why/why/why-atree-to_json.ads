with GNATCOLL.JSON;    use GNATCOLL.JSON;
with Outputs;          use Outputs;
with Why.Atree.Tables; use Why.Atree.Tables;
with Gnat2Why.Util;    use Gnat2Why.Util;

with Why.Atree;    use Why.Atree;

package Why.Atree.To_Json is
   function To_Json (Node : Why_Node) return JSON_Value;
   function To_Json (L : Why_Node_Lists.List) return JSON_Value;
end Why.Atree.To_Json;
