with HW.GFX.DP_Aux_Ch;
with HW.GFX.DP_Info;

private generic

   type Aux_T (<>) is limited private;

   with package Aux_Ch is new DP_Aux_Ch (T => Aux_T, others => <>);

   with package DP_Info is new GFX.DP_Info (T => Aux_T, Aux_Ch => Aux_Ch);

package HW.GFX.DP_Training
is

   procedure Train_DP;

end HW.GFX.DP_Training;
