  datatype CACHE_STATE = I| S| E
  datatype MSG_CMD = Empty| ReqS| ReqE| Inv| InvAck| GntS| GntE
  type NODE=nat
  type AUX_NODE=nat
  type ALL_NODE=nat
  type DATA=nat
type boolean=bool

class  class_0  {
var 
State : CACHE_STATE,
Data : DATA
}


class  class_1  {
var 
Cmd : MSG_CMD,
Data : DATA
}


class TopC{
var Cache_1 : class_0  ,
Chan1_1 : class_1  ,
Chan2_1 : class_1  ,
Chan3_1 : class_1  ,
ShrSet_1 : boolean,
InvSet_1 : boolean,
ACache_1 : class_0  ,
AChan1_1 : class_1  ,
AChan2_1 : class_1  ,
AChan3_1 : class_1  ,
AShrSet_1 : boolean,
AInvSet_1 : boolean,
ExGntd : boolean,
CurCmd : MSG_CMD,
CurPtr : ALL_NODE,
MemData : DATA,
AuxData : DATA}

predicate  inv__1(top:TopC,,)
  reads top
  
   
  
  {
(!((top.Cache_1.State == E) && (top.ACache_1.State == E)))
}


predicate  inv__2(top:TopC,,)
  reads top
  
   
  
  {
(!((top.ExGntd == false) && (!(top.MemData == top.AuxData))))
}


predicate  inv__3(top:TopC,,)
  reads top
  
   
  
  {
(!((!(top.Cache_1.State == I)) && (!(top.Cache_1.Data == top.AuxData))))
}


predicate  inv__4(top:TopC,,)
  reads top
  
   
  
  {
(!((top.ExGntd == false) && (!(top.MemData == top.AuxData))))
}


predicate  inv__5(top:TopC,,)
  reads top
  
   
  
  {
(!((!(top.ACache_1.State == I)) && (!(top.ACache_1.Data == top.AuxData))))
}


predicate  inv__6(top:TopC,,)
  reads top
  
   
  
  {
(!((top.ACache_1.State == E) && (top.Chan2_1.Cmd == GntE)))
}


predicate  inv__7(top:TopC,,)
  reads top
  
   
  
  {
(!((top.Cache_1.State == E) && (top.AChan2_1.Cmd == GntE)))
}


predicate  inv__8(top:TopC,,)
  reads top
  
   
  
  {
(!((top.ExGntd == false) && (top.Cache_1.State == E)))
}


predicate  inv__9(top:TopC,,)
  reads top
  
   
  
  {
(!((top.ExGntd == false) && (top.ACache_1.State == E)))
}


predicate  inv__10(top:TopC,,)
  reads top
  
   
  
  {
(!((!(top.Chan3_1.Data == top.AuxData)) && (top.ExGntd == true) && (top.Chan3_1.Cmd == InvAck)))
}


predicate  inv__11(top:TopC,,)
  reads top
  
   
  
  {
(!((!(top.AChan3_1.Data == top.AuxData)) && (top.ExGntd == true) && (top.AChan3_1.Cmd == InvAck)))
}


predicate  inv__12(top:TopC,,)
  reads top
  
   
  
  {
(!((!(top.Cache_1.State == I)) && (top.ACache_1.State == E)))
}


predicate  inv__13(top:TopC,,)
  reads top
  
   
  
  {
(!((!(top.Chan2_1.Data == top.AuxData)) && (top.Chan2_1.Cmd == GntS)))
}


predicate  inv__14(top:TopC,,)
  reads top
  
   
  
  {
(!((!(top.Chan2_1.Data == top.AuxData)) && (top.Chan2_1.Cmd == GntE)))
}


predicate  inv__15(top:TopC,,)
  reads top
  
   
  
  {
(!((!(top.ACache_1.State == I)) && (top.Cache_1.State == E)))
}


predicate  inv__16(top:TopC,,)
  reads top
  
   
  
  {
(!((!(top.AChan2_1.Data == top.AuxData)) && (top.AChan2_1.Cmd == GntS)))
}


predicate  inv__17(top:TopC,,)
  reads top
  
   
  
  {
(!((!(top.AChan2_1.Data == top.AuxData)) && (top.AChan2_1.Cmd == GntE)))
}


predicate  inv__18(top:TopC,,)
  reads top
  
   
  
  {
(!((top.ACache_1.State == E) && (top.AShrSet_1 == false)))
}


predicate  inv__19(top:TopC,,)
  reads top
  
   
  
  {
(!((top.Chan2_1.Cmd == GntE) && (top.AChan2_1.Cmd == GntE)))
}


predicate  inv__20(top:TopC,,)
  reads top
  
   
  
  {
(!((top.Chan3_1.Cmd == InvAck) && (top.Cache_1.State == E)))
}


predicate  inv__21(top:TopC,,)
  reads top
  
   
  
  {
(!((top.Chan3_1.Cmd == InvAck) && (top.ACache_1.State == E)))
}


predicate  inv__22(top:TopC,,)
  reads top
  
   
  
  {
(!((top.ExGntd == true) && (!(top.Cache_1.State == E)) && (top.Chan2_1.Cmd == Inv)))
}


predicate  inv__23(top:TopC,,)
  reads top
  
   
  
  {
(!((top.Chan3_1.Cmd == InvAck) && (top.ShrSet_1 == false)))
}


predicate  inv__24(top:TopC,,)
  reads top
  
   
  
  {
(!((top.AChan3_1.Cmd == InvAck) && (top.Cache_1.State == E)))
}


predicate  inv__25(top:TopC,,)
  reads top
  
   
  
  {
(!((top.AChan3_1.Cmd == InvAck) && (top.ACache_1.State == E)))
}


predicate  inv__26(top:TopC,,)
  reads top
  
   
  
  {
(!((top.AChan3_1.Cmd == InvAck) && (top.AShrSet_1 == false)))
}


predicate  inv__27(top:TopC,,)
  reads top
  
   
  
  {
(!((top.ExGntd == true) && (!(top.ACache_1.State == E)) && (top.AChan2_1.Cmd == Inv)))
}


predicate  inv__28(top:TopC,,)
  reads top
  
   
  
  {
(!((top.ExGntd == false) && (top.Chan2_1.Cmd == GntE)))
}


predicate  inv__29(top:TopC,,)
  reads top
  
   
  
  {
(!((top.ExGntd == false) && (top.AChan2_1.Cmd == GntE)))
}


predicate  inv__30(top:TopC,,)
  reads top
  
   
  
  {
(!((top.ACache_1.State == E) && (top.Chan2_1.Cmd == GntS)))
}


predicate  inv__31(top:TopC,,)
  reads top
  
   
  
  {
(!((!(top.Cache_1.State == I)) && (top.AChan2_1.Cmd == GntE)))
}


predicate  inv__32(top:TopC,,)
  reads top
  
   
  
  {
(!((top.Chan2_1.Cmd == GntS) && (top.Cache_1.State == E)))
}


predicate  inv__33(top:TopC,,)
  reads top
  
   
  
  {
(!((top.Chan2_1.Cmd == GntE) && (top.Cache_1.State == E)))
}


predicate  inv__34(top:TopC,,)
  reads top
  
   
  
  {
(!((!(top.ACache_1.State == I)) && (top.Chan2_1.Cmd == GntE)))
}


predicate  inv__35(top:TopC,,)
  reads top
  
   
  
  {
(!((top.Cache_1.State == E) && (top.AChan2_1.Cmd == GntS)))
}


predicate  inv__36(top:TopC,,)
  reads top
  
   
  
  {
(!((top.AChan2_1.Cmd == GntS) && (top.ACache_1.State == E)))
}


predicate  inv__37(top:TopC,,)
  reads top
  
   
  
  {
(!((top.AChan2_1.Cmd == GntE) && (top.ACache_1.State == E)))
}


predicate  inv__38(top:TopC,,)
  reads top
  
   
  
  {
(!((top.AShrSet_1 == false) && (top.AChan2_1.Cmd == GntE)))
}


predicate  inv__39(top:TopC,,)
  reads top
  
   
  
  {
(!((top.Chan3_1.Cmd == InvAck) && (top.Chan2_1.Cmd == GntE)))
}


predicate  inv__40(top:TopC,,)
  reads top
  
   
  
  {
(!((top.ACache_1.State == E) && (top.Chan2_1.Cmd == Inv)))
}


predicate  inv__41(top:TopC,,)
  reads top
  
   
  
  {
(!((top.Chan3_1.Cmd == InvAck) && (top.AChan2_1.Cmd == GntE)))
}


predicate  inv__42(top:TopC,,)
  reads top
  
   
  
  {
(!((top.ExGntd == true) && (!(top.Cache_1.State == E)) && (top.Chan2_1.Cmd == Empty) && (top.InvSet_1 == true)))
}


predicate  inv__43(top:TopC,,)
  reads top
  
   
  
  {
(!((top.Chan2_1.Cmd == Inv) && (top.ShrSet_1 == false)))
}


predicate  inv__44(top:TopC,,)
  reads top
  
   
  
  {
(!((top.AChan3_1.Cmd == InvAck) && (top.Chan2_1.Cmd == GntE)))
}


predicate  inv__45(top:TopC,,)
  reads top
  
   
  
  {
(!((top.Cache_1.State == E) && (top.AChan2_1.Cmd == Inv)))
}


predicate  inv__46(top:TopC,,)
  reads top
  
   
  
  {
(!((top.AChan3_1.Cmd == InvAck) && (top.AChan2_1.Cmd == GntE)))
}


predicate  inv__47(top:TopC,,)
  reads top
  
   
  
  {
(!((top.AShrSet_1 == false) && (top.AChan2_1.Cmd == Inv)))
}


predicate  inv__48(top:TopC,,)
  reads top
  
   
  
  {
(!((top.ExGntd == true) && (!(top.ACache_1.State == E)) && (top.AChan2_1.Cmd == Empty) && (top.AInvSet_1 == true)))
}


predicate  inv__49(top:TopC,,)
  reads top
  
   
  
  {
(!((top.Chan2_1.Cmd == GntS) && (top.AChan2_1.Cmd == GntE)))
}


predicate  inv__50(top:TopC,,)
  reads top
  
   
  
  {
(!((!(top.Cache_1.State == I)) && (top.ShrSet_1 == false)))
}


predicate  inv__51(top:TopC,,)
  reads top
  
   
  
  {
(!((!(top.ACache_1.State == I)) && (top.AShrSet_1 == false)))
}


predicate  inv__52(top:TopC,,)
  reads top
  
   
  
  {
(!((top.Chan2_1.Cmd == GntE) && (top.AChan2_1.Cmd == GntS)))
}


predicate  inv__53(top:TopC,,)
  reads top
  
   
  
  {
(!((top.ACache_1.State == E) && (top.InvSet_1 == true)))
}


predicate  inv__54(top:TopC,,)
  reads top
  
   
  
  {
(!((top.Chan2_1.Cmd == Inv) && (top.AChan2_1.Cmd == GntE)))
}


predicate  inv__55(top:TopC,,)
  reads top
  
   
  
  {
(!((top.ExGntd == true) && (!(top.Cache_1.State == E)) && (top.Chan2_1.Cmd == Empty) && (top.ShrSet_1 == true) && (top.CurCmd == Empty)))
}


predicate  inv__56(top:TopC,,)
  reads top
  
   
  
  {
(!((top.InvSet_1 == true) && (top.Chan2_1.Cmd == Inv)))
}


predicate  inv__57(top:TopC,,)
  reads top
  
   
  
  {
(!((top.ExGntd == true) && (top.Chan2_1.Cmd == GntS)))
}


predicate  inv__58(top:TopC,,)
  reads top
  
   
  
  {
(!((top.InvSet_1 == true) && (top.ShrSet_1 == false)))
}


predicate  inv__59(top:TopC,,)
  reads top
  
   
  
  {
(!((top.Chan2_1.Cmd == Inv) && (top.Chan3_1.Cmd == InvAck)))
}


predicate  inv__60(top:TopC,,)
  reads top
  
   
  
  {
(!((top.Chan2_1.Cmd == GntE) && (top.AChan2_1.Cmd == Inv)))
}


predicate  inv__61(top:TopC,,)
  reads top
  
   
  
  {
(!((top.Cache_1.State == E) && (top.AInvSet_1 == true)))
}


predicate  inv__62(top:TopC,,)
  reads top
  
   
  
  {
(!((top.AShrSet_1 == false) && (top.AInvSet_1 == true)))
}


predicate  inv__63(top:TopC,,)
  reads top
  
   
  
  {
(!((top.AChan2_1.Cmd == Inv) && (top.AChan3_1.Cmd == InvAck)))
}


predicate  inv__64(top:TopC,,)
  reads top
  
   
  
  {
(!((top.ExGntd == true) && (!(top.ACache_1.State == E)) && (top.AChan2_1.Cmd == Empty) && (top.AShrSet_1 == true) && (top.CurCmd == Empty)))
}


predicate  inv__65(top:TopC,,)
  reads top
  
   
  
  {
(!((top.AInvSet_1 == true) && (top.AChan2_1.Cmd == Inv)))
}


predicate  inv__66(top:TopC,,)
  reads top
  
   
  
  {
(!((top.ExGntd == true) && (top.AChan2_1.Cmd == GntS)))
}


predicate  inv__67(top:TopC,,)
  reads top
  
   
  
  {
(!((top.Chan2_1.Cmd == GntS) && (top.ShrSet_1 == false)))
}


predicate  inv__68(top:TopC,,)
  reads top
  
   
  
  {
(!((!(top.Cache_1.State == I)) && (top.Chan3_1.Cmd == InvAck)))
}


predicate  inv__69(top:TopC,,)
  reads top
  
   
  
  {
(!((top.ShrSet_1 == false) && (top.Chan2_1.Cmd == GntE)))
}


predicate  inv__70(top:TopC,,)
  reads top
  
   
  
  {
(!((!(top.ACache_1.State == I)) && (top.AChan3_1.Cmd == InvAck)))
}


predicate  inv__71(top:TopC,,)
  reads top
  
   
  
  {
(!((top.AShrSet_1 == false) && (top.AChan2_1.Cmd == GntS)))
}


predicate  inv__72(top:TopC,,)
  reads top
  
   
  
  {
(!((top.ACache_1.State == E) && (top.ShrSet_1 == true)))
}


predicate  inv__73(top:TopC,,)
  reads top
  
   
  
  {
(!((top.InvSet_1 == true) && (top.AChan2_1.Cmd == GntE)))
}


predicate  inv__74(top:TopC,,)
  reads top
  
   
  
  {
(!((top.CurCmd == Empty) && (top.Chan2_1.Cmd == Inv)))
}


predicate  inv__75(top:TopC,,)
  reads top
  
   
  
  {
(!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))
}


predicate  inv__76(top:TopC,,)
  reads top
  
   
  
  {
(!((top.Chan2_1.Cmd == GntE) && (top.AInvSet_1 == true)))
}


predicate  inv__77(top:TopC,,)
  reads top
  
   
  
  {
(!((top.Cache_1.State == E) && (top.AShrSet_1 == true)))
}


predicate  inv__78(top:TopC,,)
  reads top
  
   
  
  {
(!((top.AInvSet_1 == true) && (top.AChan3_1.Cmd == InvAck)))
}


predicate  inv__79(top:TopC,,)
  reads top
  
   
  
  {
(!((top.CurCmd == Empty) && (top.AChan2_1.Cmd == Inv)))
}


predicate  inv__80(top:TopC,,)
  reads top
  
   
  
  {
(!((top.Chan2_1.Cmd == GntS) && (top.Chan3_1.Cmd == InvAck)))
}


predicate  inv__81(top:TopC,,)
  reads top
  
   
  
  {
(!((top.AChan3_1.Cmd == InvAck) && (top.AChan2_1.Cmd == GntS)))
}


predicate  inv__82(top:TopC,,)
  reads top
  
   
  
  {
(!((top.ShrSet_1 == true) && (top.AChan2_1.Cmd == GntE)))
}


predicate  inv__83(top:TopC,,)
  reads top
  
   
  
  {
(!((top.Chan2_1.Cmd == Inv) && (top.CurCmd == ReqS) && (top.ExGntd == false)))
}


predicate  inv__84(top:TopC,,)
  reads top
  
   
  
  {
(!((top.Chan3_1.Cmd == InvAck) && (top.CurCmd == Empty)))
}


predicate  inv__85(top:TopC,,)
  reads top
  
   
  
  {
(!((top.Chan2_1.Cmd == GntE) && (top.AShrSet_1 == true)))
}


predicate  inv__86(top:TopC,,)
  reads top
  
   
  
  {
(!((top.AChan3_1.Cmd == InvAck) && (top.CurCmd == Empty)))
}


predicate  inv__87(top:TopC,,)
  reads top
  
   
  
  {
(!((top.AChan2_1.Cmd == Inv) && (top.CurCmd == ReqS) && (top.ExGntd == false)))
}


predicate  inv__88(top:TopC,,)
  reads top
  
   
  
  {
(!((top.Chan3_1.Cmd == InvAck) && (top.CurCmd == ReqS) && (top.ExGntd == false)))
}


predicate  inv__89(top:TopC,,)
  reads top
  
   
  
  {
(!((top.AChan3_1.Cmd == InvAck) && (top.CurCmd == ReqS) && (top.ExGntd == false)))
}


predicate  inv__90(top:TopC,,)
  reads top
  
   
  
  {
(!((top.Chan2_1.Cmd == Inv) && (top.CurCmd == ReqS) && (top.AChan3_1.Cmd == InvAck)))
}


predicate  inv__91(top:TopC,,)
  reads top
  
   
  
  {
(!((top.AChan2_1.Cmd == Inv) && (top.CurCmd == ReqS) && (top.Chan3_1.Cmd == InvAck)))
}


predicate  inv__92(top:TopC,,)
  reads top
  
   
  
  {
(!((top.Chan3_1.Cmd == InvAck) && (top.CurCmd == ReqS) && (top.AChan3_1.Cmd == InvAck)))
}


predicate  inv__93(top:TopC,,)
  reads top
  
   
  
  {
(!((top.CurCmd == ReqS) && (top.AChan3_1.Cmd == InvAck) && (top.InvSet_1 == true)))
}


predicate  inv__94(top:TopC,,)
  reads top
  
   
  
  {
(!((top.Chan2_1.Cmd == Inv) && (top.CurCmd == ReqS) && (top.AChan2_1.Cmd == Inv)))
}


predicate  inv__95(top:TopC,,)
  reads top
  
   
  
  {
(!((top.CurCmd == ReqS) && (top.Chan3_1.Cmd == InvAck) && (top.AInvSet_1 == true)))
}


predicate  inv__96(top:TopC,,)
  reads top
  
   
  
  {
(!((top.CurCmd == ReqS) && (top.InvSet_1 == true) && (top.AChan2_1.Cmd == Inv)))
}


predicate  inv__97(top:TopC,,)
  reads top
  
   
  
  {
(!((top.Chan2_1.Cmd == Inv) && (top.CurCmd == ReqS) && (top.AInvSet_1 == true)))
}


predicate  inv__98(top:TopC,,)
  reads top
  
   
  
  {
(!((top.InvSet_1 == true) && (top.AInvSet_1 == true) && (top.ExGntd == true)))
}


predicate  inv__99(top:TopC,,)
  reads top
  
   
  
  {
(!((top.ShrSet_1 == true) && (top.AShrSet_1 == true) && (top.ExGntd == true)))
}

