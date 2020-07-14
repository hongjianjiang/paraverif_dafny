datatype CACHE_STATE = I| S| E
datatype MSG_CMD = Empty| ReqS| ReqE| Inv| InvAck| GntS| GntE
type NODE=nat
type DATA=nat
type boolean=bool

class  class_0  {
var 
Data : DATA,
Cmd : MSG_CMD
}


class  class_1  {
var 
Data : DATA,
State : CACHE_STATE
}

predicate  inv__1(top:TopC,N0:nat,p__Inv3:nat, p__Inv4:nat)
  reads top
  reads Cache_State[p
reads Cache_State[p
  requires top.Cache.Length ==N0
 requires N0>0
requires top.Cache.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv3<N0
 requires 0<= p__Inv4<N0
  {
(!((top.Cache[p__Inv4].State == E) && (!(top.Cache[p__Inv3].State == I))))
}


predicate  inv__2(top:TopC,N0:nat,p__Inv3:nat, p__Inv4:nat)
  reads top
  reads Cache_State[p
reads Cache_State[p
  requires top.Cache.Length ==N0
 requires N0>0
requires top.Cache.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv3<N0
 requires 0<= p__Inv4<N0
  {
(!((top.Cache[p__Inv4].State == S) && (!(top.Cache[p__Inv3].State == I)) && (!(top.Cache[p__Inv3].State == S))))
}


predicate  inv__3(top:TopC,,)
  reads top
  reads AuxData
reads ExGntd
reads MemData
   
  
  {
(!((top.ExGntd == false) && (!(top.MemData == top.AuxData))))
}


predicate  inv__4(top:TopC,N0:nat,p__Inv4:nat)
  reads top
  reads AuxData
reads Cache_Data[p
reads Cache_State[p
  requires top.Cache.Length ==N0
 requires N0>0
requires top.Cache.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv4<N0
  {
(!((!(top.Cache[p__Inv4].State == I)) && (!(top.Cache[p__Inv4].Data == top.AuxData))))
}


predicate  inv__5(top:TopC,N0:nat,p__Inv3:nat, p__Inv4:nat)
  reads top
  reads Cache_State[p
reads Chan2_Cmd[p
  requires top.Cache.Length ==N0
 requires N0>0
requires top.Chan2.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv3<N0
 requires 0<= p__Inv4<N0
  {
(!((top.Cache[p__Inv3].State == E) && (top.Chan2[p__Inv4].Cmd == GntS)))
}


predicate  inv__6(top:TopC,N0:nat,p__Inv3:nat, p__Inv4:nat)
  reads top
  reads Cache_State[p
reads Chan2_Cmd[p
  requires top.Cache.Length ==N0
 requires N0>0
requires top.Chan2.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv3<N0
 requires 0<= p__Inv4<N0
  {
(!((!(top.Cache[p__Inv4].State == I)) && (top.Chan2[p__Inv3].Cmd == GntE)))
}


predicate  inv__7(top:TopC,N0:nat,p__Inv3:nat, p__Inv4:nat)
  reads top
  reads Cache_State[p
reads Chan2_Cmd[p
  requires top.Cache.Length ==N0
 requires N0>0
requires top.Chan2.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv3<N0
 requires 0<= p__Inv4<N0
  {
(!((top.Cache[p__Inv3].State == E) && (top.Chan2[p__Inv4].Cmd == GntE)))
}


predicate  inv__8(top:TopC,N0:nat,p__Inv4:nat)
  reads top
  reads Cache_State[p
reads ExGntd
  requires top.Cache.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv4<N0
  {
(!((top.ExGntd == false) && (top.Cache[p__Inv4].State == E)))
}


predicate  inv__9(top:TopC,N0:nat,p__Inv4:nat)
  reads top
  reads AuxData
reads Chan3_Cmd[p
reads Chan3_Data[p
reads ExGntd
  requires top.Chan3.Length ==N0
 requires N0>0
requires top.Chan3.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv4<N0
  {
(!((!(top.Chan3[p__Inv4].Data == top.AuxData)) && (top.ExGntd == true) && (top.Chan3[p__Inv4].Cmd == InvAck)))
}


predicate  inv__10(top:TopC,N0:nat,p__Inv4:nat)
  reads top
  reads AuxData
reads Chan2_Cmd[p
reads Chan2_Data[p
  requires top.Chan2.Length ==N0
 requires N0>0
requires top.Chan2.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv4<N0
  {
(!((!(top.Chan2[p__Inv4].Data == top.AuxData)) && (top.Chan2[p__Inv4].Cmd == GntS)))
}


predicate  inv__11(top:TopC,N0:nat,p__Inv4:nat)
  reads top
  reads AuxData
reads Chan2_Cmd[p
reads Chan2_Data[p
  requires top.Chan2.Length ==N0
 requires N0>0
requires top.Chan2.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv4<N0
  {
(!((!(top.Chan2[p__Inv4].Data == top.AuxData)) && (top.Chan2[p__Inv4].Cmd == GntE)))
}


predicate  inv__12(top:TopC,N0:nat,p__Inv3:nat, p__Inv4:nat)
  reads top
  reads Chan2_Cmd[p
reads Chan2_Cmd[p
  requires top.Chan2.Length ==N0
 requires N0>0
requires top.Chan2.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv3<N0
 requires 0<= p__Inv4<N0
  {
(!((top.Chan2[p__Inv3].Cmd == GntS) && (top.Chan2[p__Inv4].Cmd == GntE)))
}


predicate  inv__13(top:TopC,N0:nat,p__Inv4:nat)
  reads top
  reads Cache_State[p
reads ShrSet[p
  requires top.Cache.Length ==N0
 requires N0>0
requires top.ShrSet.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv4<N0
  {
(!((!(top.Cache[p__Inv4].State == I)) && (top.ShrSet[p__Inv4] == false)))
}


predicate  inv__14(top:TopC,N0:nat,p__Inv3:nat, p__Inv4:nat)
  reads top
  reads Chan2_Cmd[p
reads Chan2_Cmd[p
  requires top.Chan2.Length ==N0
 requires N0>0
requires top.Chan2.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv3<N0
 requires 0<= p__Inv4<N0
  {
(!((top.Chan2[p__Inv4].Cmd == GntE) && (top.Chan2[p__Inv3].Cmd == GntE)))
}


predicate  inv__15(top:TopC,N0:nat,p__Inv4:nat)
  reads top
  reads Cache_State[p
reads Chan3_Cmd[p
  requires top.Cache.Length ==N0
 requires N0>0
requires top.Chan3.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv4<N0
  {
(!((top.Cache[p__Inv4].State == E) && (top.Chan3[p__Inv4].Cmd == InvAck)))
}


predicate  inv__16(top:TopC,N0:nat,p__Inv3:nat, p__Inv4:nat)
  reads top
  reads Cache_State[p
reads Chan3_Cmd[p
  requires top.Cache.Length ==N0
 requires N0>0
requires top.Chan3.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv3<N0
 requires 0<= p__Inv4<N0
  {
(!((top.Cache[p__Inv3].State == E) && (top.Chan3[p__Inv4].Cmd == InvAck)))
}


predicate  inv__17(top:TopC,N0:nat,p__Inv4:nat)
  reads top
  reads Chan2_Cmd[p
reads ExGntd
  requires top.Chan2.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv4<N0
  {
(!((top.ExGntd == false) && (top.Chan2[p__Inv4].Cmd == GntE)))
}


predicate  inv__18(top:TopC,N0:nat,p__Inv4:nat)
  reads top
  reads Cache_State[p
reads Chan2_Cmd[p
reads ExGntd
  requires top.Cache.Length ==N0
 requires N0>0
requires top.Chan2.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv4<N0
  {
(!((top.ExGntd == true) && (!(top.Cache[p__Inv4].State == E)) && (top.Chan2[p__Inv4].Cmd == Inv)))
}


predicate  inv__19(top:TopC,N0:nat,p__Inv4:nat)
  reads top
  reads Chan3_Cmd[p
reads ShrSet[p
  requires top.Chan3.Length ==N0
 requires N0>0
requires top.ShrSet.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv4<N0
  {
(!((top.Chan3[p__Inv4].Cmd == InvAck) && (top.ShrSet[p__Inv4] == false)))
}


predicate  inv__20(top:TopC,N0:nat,p__Inv4:nat)
  reads top
  reads Cache_State[p
reads Chan2_Cmd[p
  requires top.Cache.Length ==N0
 requires N0>0
requires top.Chan2.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv4<N0
  {
(!((top.Chan2[p__Inv4].Cmd == GntS) && (top.Cache[p__Inv4].State == E)))
}


predicate  inv__21(top:TopC,N0:nat,p__Inv4:nat)
  reads top
  reads Cache_State[p
reads Chan2_Cmd[p
  requires top.Cache.Length ==N0
 requires N0>0
requires top.Chan2.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv4<N0
  {
(!((top.Chan2[p__Inv4].Cmd == GntE) && (top.Cache[p__Inv4].State == E)))
}


predicate  inv__22(top:TopC,N0:nat,p__Inv4:nat)
  reads top
  reads Chan2_Cmd[p
reads ShrSet[p
  requires top.Chan2.Length ==N0
 requires N0>0
requires top.ShrSet.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv4<N0
  {
(!((top.Chan2[p__Inv4].Cmd == GntS) && (top.ShrSet[p__Inv4] == false)))
}


predicate  inv__23(top:TopC,N0:nat,p__Inv4:nat)
  reads top
  reads Cache_State[p
reads Chan3_Cmd[p
  requires top.Cache.Length ==N0
 requires N0>0
requires top.Chan3.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv4<N0
  {
(!((!(top.Cache[p__Inv4].State == I)) && (top.Chan3[p__Inv4].Cmd == InvAck)))
}


predicate  inv__24(top:TopC,N0:nat,p__Inv4:nat)
  reads top
  reads Chan2_Cmd[p
reads ShrSet[p
  requires top.Chan2.Length ==N0
 requires N0>0
requires top.ShrSet.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv4<N0
  {
(!((top.ShrSet[p__Inv4] == false) && (top.Chan2[p__Inv4].Cmd == GntE)))
}


predicate  inv__25(top:TopC,N0:nat,p__Inv4:nat)
  reads top
  reads Chan2_Cmd[p
reads Chan3_Cmd[p
  requires top.Chan2.Length ==N0
 requires N0>0
requires top.Chan3.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv4<N0
  {
(!((top.Chan3[p__Inv4].Cmd == InvAck) && (top.Chan2[p__Inv4].Cmd == GntE)))
}


predicate  inv__26(top:TopC,N0:nat,p__Inv3:nat, p__Inv4:nat)
  reads top
  reads Cache_State[p
reads Chan2_Cmd[p
  requires top.Cache.Length ==N0
 requires N0>0
requires top.Chan2.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv3<N0
 requires 0<= p__Inv4<N0
  {
(!((top.Cache[p__Inv4].State == E) && (top.Chan2[p__Inv3].Cmd == Inv)))
}


predicate  inv__27(top:TopC,N0:nat,p__Inv3:nat, p__Inv4:nat)
  reads top
  reads Chan2_Cmd[p
reads Chan3_Cmd[p
  requires top.Chan2.Length ==N0
 requires N0>0
requires top.Chan3.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv3<N0
 requires 0<= p__Inv4<N0
  {
(!((top.Chan3[p__Inv3].Cmd == InvAck) && (top.Chan2[p__Inv4].Cmd == GntE)))
}


predicate  inv__28(top:TopC,N0:nat,p__Inv4:nat)
  reads top
  reads Cache_State[p
reads Chan2_Cmd[p
reads ExGntd
reads InvSet[p
  requires top.Cache.Length ==N0
 requires N0>0
requires top.Chan2.Length ==N0
 requires N0>0
requires top.InvSet.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv4<N0
  {
(!((top.ExGntd == true) && (!(top.Cache[p__Inv4].State == E)) && (top.Chan2[p__Inv4].Cmd == Empty) && (top.InvSet[p__Inv4] == true)))
}


predicate  inv__29(top:TopC,N0:nat,p__Inv4:nat)
  reads top
  reads Chan2_Cmd[p
reads ShrSet[p
  requires top.Chan2.Length ==N0
 requires N0>0
requires top.ShrSet.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv4<N0
  {
(!((top.Chan2[p__Inv4].Cmd == Inv) && (top.ShrSet[p__Inv4] == false)))
}


predicate  inv__30(top:TopC,N0:nat,p__Inv4:nat)
  reads top
  reads Chan2_Cmd[p
reads Chan3_Cmd[p
  requires top.Chan2.Length ==N0
 requires N0>0
requires top.Chan3.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv4<N0
  {
(!((top.Chan2[p__Inv4].Cmd == GntS) && (top.Chan3[p__Inv4].Cmd == InvAck)))
}


predicate  inv__31(top:TopC,N0:nat,p__Inv3:nat, p__Inv4:nat)
  reads top
  reads Cache_State[p
reads InvSet[p
  requires top.Cache.Length ==N0
 requires N0>0
requires top.InvSet.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv3<N0
 requires 0<= p__Inv4<N0
  {
(!((top.Cache[p__Inv3].State == E) && (top.InvSet[p__Inv4] == true)))
}


predicate  inv__32(top:TopC,N0:nat,p__Inv3:nat, p__Inv4:nat)
  reads top
  reads Chan2_Cmd[p
reads Chan2_Cmd[p
  requires top.Chan2.Length ==N0
 requires N0>0
requires top.Chan2.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv3<N0
 requires 0<= p__Inv4<N0
  {
(!((top.Chan2[p__Inv4].Cmd == Inv) && (top.Chan2[p__Inv3].Cmd == GntE)))
}


predicate  inv__33(top:TopC,N0:nat,p__Inv4:nat)
  reads top
  reads Cache_State[p
reads Chan2_Cmd[p
reads CurCmd
reads ShrSet[p
  requires top.Cache.Length ==N0
 requires N0>0
requires top.Chan2.Length ==N0
 requires N0>0
requires top.ShrSet.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv4<N0
  {
(!((top.Chan2[p__Inv4].Cmd == Empty) && (top.ShrSet[p__Inv4] == true) && (top.Cache[p__Inv4].State == I) && (top.CurCmd == Empty)))
}


predicate  inv__34(top:TopC,N0:nat,p__Inv4:nat)
  reads top
  reads Cache_State[p
reads Chan2_Cmd[p
reads CurCmd
reads ExGntd
reads ShrSet[p
  requires top.Cache.Length ==N0
 requires N0>0
requires top.Chan2.Length ==N0
 requires N0>0
requires top.ShrSet.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv4<N0
  {
(!((top.ExGntd == true) && (!(top.Cache[p__Inv4].State == E)) && (top.Chan2[p__Inv4].Cmd == Empty) && (top.ShrSet[p__Inv4] == true) && (top.CurCmd == Empty)))
}


predicate  inv__35(top:TopC,N0:nat,p__Inv4:nat)
  reads top
  reads Cache_State[p
reads ExGntd
  requires top.Cache.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv4<N0
  {
(!((top.ExGntd == true) && (top.Cache[p__Inv4].State == S)))
}


predicate  inv__36(top:TopC,N0:nat,p__Inv4:nat)
  reads top
  reads Chan2_Cmd[p
reads InvSet[p
  requires top.Chan2.Length ==N0
 requires N0>0
requires top.InvSet.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv4<N0
  {
(!((top.InvSet[p__Inv4] == true) && (top.Chan2[p__Inv4].Cmd == Inv)))
}


predicate  inv__37(top:TopC,N0:nat,p__Inv4:nat)
  reads top
  reads InvSet[p
reads ShrSet[p
  requires top.InvSet.Length ==N0
 requires N0>0
requires top.ShrSet.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv4<N0
  {
(!((top.InvSet[p__Inv4] == true) && (top.ShrSet[p__Inv4] == false)))
}


predicate  inv__38(top:TopC,N0:nat,p__Inv4:nat)
  reads top
  reads Chan2_Cmd[p
reads ExGntd
  requires top.Chan2.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv4<N0
  {
(!((top.ExGntd == true) && (top.Chan2[p__Inv4].Cmd == GntS)))
}


predicate  inv__39(top:TopC,N0:nat,p__Inv4:nat)
  reads top
  reads Chan2_Cmd[p
reads Chan3_Cmd[p
  requires top.Chan2.Length ==N0
 requires N0>0
requires top.Chan3.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv4<N0
  {
(!((top.Chan2[p__Inv4].Cmd == Inv) && (top.Chan3[p__Inv4].Cmd == InvAck)))
}


predicate  inv__40(top:TopC,N0:nat,p__Inv4:nat)
  reads top
  reads Chan3_Cmd[p
reads CurCmd
reads ExGntd
  requires top.Chan3.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv4<N0
  {
(!((top.Chan3[p__Inv4].Cmd == InvAck) && (top.CurCmd == ReqS) && (top.ExGntd == false)))
}


predicate  inv__41(top:TopC,N0:nat,p__Inv3:nat, p__Inv4:nat)
  reads top
  reads Cache_State[p
reads ShrSet[p
  requires top.Cache.Length ==N0
 requires N0>0
requires top.ShrSet.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv3<N0
 requires 0<= p__Inv4<N0
  {
(!((top.Cache[p__Inv4].State == E) && (top.ShrSet[p__Inv3] == true)))
}


predicate  inv__42(top:TopC,N0:nat,p__Inv3:nat, p__Inv4:nat)
  reads top
  reads Chan2_Cmd[p
reads InvSet[p
  requires top.Chan2.Length ==N0
 requires N0>0
requires top.InvSet.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv3<N0
 requires 0<= p__Inv4<N0
  {
(!((top.InvSet[p__Inv3] == true) && (top.Chan2[p__Inv4].Cmd == GntE)))
}


predicate  inv__43(top:TopC,N0:nat,p__Inv4:nat)
  reads top
  reads Chan2_Cmd[p
reads CurCmd
  requires top.Chan2.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv4<N0
  {
(!((top.CurCmd == Empty) && (top.Chan2[p__Inv4].Cmd == Inv)))
}


predicate  inv__44(top:TopC,N0:nat,p__Inv4:nat)
  reads top
  reads Cache_State[p
reads Chan2_Cmd[p
reads CurCmd
reads ExGntd
reads ShrSet[p
  requires top.Cache.Length ==N0
 requires N0>0
requires top.Chan2.Length ==N0
 requires N0>0
requires top.ShrSet.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv4<N0
  {
(!((top.Chan2[p__Inv4].Cmd == Empty) && (top.ShrSet[p__Inv4] == true) && (top.Cache[p__Inv4].State == I) && (top.CurCmd == ReqS) && (top.ExGntd == false)))
}


predicate  inv__45(top:TopC,N0:nat,p__Inv4:nat)
  reads top
  reads Cache_State[p
reads Chan2_Cmd[p
  requires top.Cache.Length ==N0
 requires N0>0
requires top.Chan2.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv4<N0
  {
(!((top.Chan2[p__Inv4].Cmd == Inv) && (top.Cache[p__Inv4].State == I)))
}


predicate  inv__46(top:TopC,N0:nat,p__Inv4:nat)
  reads top
  reads Chan3_Cmd[p
reads InvSet[p
  requires top.Chan3.Length ==N0
 requires N0>0
requires top.InvSet.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv4<N0
  {
(!((top.InvSet[p__Inv4] == true) && (top.Chan3[p__Inv4].Cmd == InvAck)))
}


predicate  inv__47(top:TopC,N0:nat,p__Inv4:nat)
  reads top
  reads Chan3_Cmd[p
reads CurCmd
  requires top.Chan3.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv4<N0
  {
(!((top.Chan3[p__Inv4].Cmd == InvAck) && (top.CurCmd == Empty)))
}


predicate  inv__48(top:TopC,N0:nat,p__Inv4:nat)
  reads top
  reads Chan2_Cmd[p
reads CurCmd
reads ExGntd
  requires top.Chan2.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv4<N0
  {
(!((top.CurCmd == ReqS) && (top.ExGntd == false) && (top.Chan2[p__Inv4].Cmd == Inv)))
}


predicate  inv__49(top:TopC,N0:nat,p__Inv3:nat, p__Inv4:nat)
  reads top
  reads Chan3_Cmd[p
reads Chan3_Cmd[p
reads CurCmd
  requires top.Chan3.Length ==N0
 requires N0>0
requires top.Chan3.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv3<N0
 requires 0<= p__Inv4<N0
  {
(!((top.Chan3[p__Inv3].Cmd == InvAck) && (top.CurCmd == ReqS) && (top.Chan3[p__Inv4].Cmd == InvAck)))
}


predicate  inv__50(top:TopC,N0:nat,p__Inv3:nat, p__Inv4:nat)
  reads top
  reads Chan2_Cmd[p
reads ShrSet[p
  requires top.Chan2.Length ==N0
 requires N0>0
requires top.ShrSet.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv3<N0
 requires 0<= p__Inv4<N0
  {
(!((top.ShrSet[p__Inv4] == true) && (top.Chan2[p__Inv3].Cmd == GntE)))
}


predicate  inv__51(top:TopC,N0:nat,p__Inv3:nat, p__Inv4:nat)
  reads top
  reads Chan3_Cmd[p
reads CurCmd
reads ShrSet[p
  requires top.Chan3.Length ==N0
 requires N0>0
requires top.ShrSet.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv3<N0
 requires 0<= p__Inv4<N0
  {
(!((top.ShrSet[p__Inv3] == true) && (top.CurCmd == ReqS) && (top.Chan3[p__Inv4].Cmd == InvAck)))
}


predicate  inv__52(top:TopC,N0:nat,p__Inv4:nat)
  reads top
  reads Cache_State[p
reads Chan2_Cmd[p
reads InvSet[p
  requires top.Cache.Length ==N0
 requires N0>0
requires top.Chan2.Length ==N0
 requires N0>0
requires top.InvSet.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv4<N0
  {
(!((top.Cache[p__Inv4].State == I) && (top.Chan2[p__Inv4].Cmd == Empty) && (top.InvSet[p__Inv4] == true)))
}


predicate  inv__53(top:TopC,N0:nat,p__Inv3:nat, p__Inv4:nat)
  reads top
  reads Chan2_Cmd[p
reads Chan3_Cmd[p
reads CurCmd
  requires top.Chan2.Length ==N0
 requires N0>0
requires top.Chan3.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv3<N0
 requires 0<= p__Inv4<N0
  {
(!((top.CurCmd == ReqS) && (top.Chan2[p__Inv3].Cmd == Inv) && (top.Chan3[p__Inv4].Cmd == InvAck)))
}


predicate  inv__54(top:TopC,N0:nat,p__Inv3:nat, p__Inv4:nat)
  reads top
  reads Chan2_Cmd[p
reads CurCmd
reads ShrSet[p
  requires top.Chan2.Length ==N0
 requires N0>0
requires top.ShrSet.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv3<N0
 requires 0<= p__Inv4<N0
  {
(!((top.ShrSet[p__Inv4] == true) && (top.CurCmd == ReqS) && (top.Chan2[p__Inv3].Cmd == Inv)))
}


predicate  inv__55(top:TopC,N0:nat,p__Inv3:nat, p__Inv4:nat)
  reads top
  reads Chan3_Cmd[p
reads CurCmd
reads InvSet[p
  requires top.Chan3.Length ==N0
 requires N0>0
requires top.InvSet.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv3<N0
 requires 0<= p__Inv4<N0
  {
(!((top.CurCmd == ReqS) && (top.Chan3[p__Inv3].Cmd == InvAck) && (top.InvSet[p__Inv4] == true)))
}


predicate  inv__56(top:TopC,N0:nat,p__Inv3:nat, p__Inv4:nat)
  reads top
  reads Chan2_Cmd[p
reads Chan2_Cmd[p
reads CurCmd
  requires top.Chan2.Length ==N0
 requires N0>0
requires top.Chan2.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv3<N0
 requires 0<= p__Inv4<N0
  {
(!((top.CurCmd == ReqS) && (top.Chan2[p__Inv4].Cmd == Inv) && (top.Chan2[p__Inv3].Cmd == Inv)))
}


predicate  inv__57(top:TopC,N0:nat,p__Inv3:nat, p__Inv4:nat)
  reads top
  reads ExGntd
reads InvSet[p
reads ShrSet[p
  requires top.InvSet.Length ==N0
 requires N0>0
requires top.ShrSet.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv3<N0
 requires 0<= p__Inv4<N0
  {
(!((top.ShrSet[p__Inv3] == true) && (top.ExGntd == true) && (top.InvSet[p__Inv4] == true)))
}


predicate  inv__58(top:TopC,N0:nat,p__Inv3:nat, p__Inv4:nat)
  reads top
  reads Chan2_Cmd[p
reads CurCmd
reads InvSet[p
  requires top.Chan2.Length ==N0
 requires N0>0
requires top.InvSet.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv3<N0
 requires 0<= p__Inv4<N0
  {
(!((top.CurCmd == ReqS) && (top.InvSet[p__Inv3] == true) && (top.Chan2[p__Inv4].Cmd == Inv)))
}


predicate  inv__59(top:TopC,N0:nat,p__Inv3:nat, p__Inv4:nat)
  reads top
  reads ExGntd
reads ShrSet[p
reads ShrSet[p
  requires top.ShrSet.Length ==N0
 requires N0>0
requires top.ShrSet.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv3<N0
 requires 0<= p__Inv4<N0
  {
(!((top.ShrSet[p__Inv4] == true) && (top.ExGntd == true) && (top.ShrSet[p__Inv3] == true)))
}


predicate  inv__60(top:TopC,N0:nat,p__Inv3:nat, p__Inv4:nat)
  reads top
  reads ExGntd
reads InvSet[p
reads InvSet[p
  requires top.InvSet.Length ==N0
 requires N0>0
requires top.InvSet.Length ==N0
 requires N0>0
 
  requires 0<= p__Inv3<N0
 requires 0<= p__Inv4<N0
  {
(!((top.InvSet[p__Inv4] == true) && (top.ExGntd == true) && (top.InvSet[p__Inv3] == true)))
}

