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

method n_n_RecvReq_i1(top:TopC)
requires 

requires (!((top.Chan3_1.Cmd == InvAck) && (top.CurCmd == Empty)))//3//guard condition
requires   ((top.CurCmd == Empty) && (!(top.Chan1_1.Cmd == Empty)));
ensures   (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))

modifies top
{
  top.CurCmd := top.Chan1_1.Cmd;
  top.Chan1_1.Cmd := Empty;
  top.CurPtr := 1;
  top.InvSet_1 := top.ShrSet_1;
  top.AInvSet_1 := top.AShrSet_1;
};

method n_n_SendInvE_i1(top:TopC)
requires 

//1//guard condition
requires   ((top.Chan2_1.Cmd == Empty) && (top.CurCmd == ReqE) && (top.InvSet_1 == true));
ensures   (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))

modifies top
{
  top.Chan2_1.Cmd := Inv;
  top.InvSet_1 := false;
};

method n_n_SendInvS_i1(top:TopC)
requires 

//1//guard condition
requires   ((top.Chan2_1.Cmd == Empty) && (top.CurCmd == ReqS) && (top.ExGntd == true) && (top.InvSet_1 == true));
ensures   (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))

modifies top
{
  top.Chan2_1.Cmd := Inv;
  top.InvSet_1 := false;
};

method n_n_SendInvAck_i1(top:TopC)
requires 

requires (!((top.InvSet_1 == true) && (top.Chan2_1.Cmd == Inv)))//3//guard condition
requires   ((top.Chan2_1.Cmd == Inv) && (top.Chan3_1.Cmd == Empty));
ensures   (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))

modifies top
{
  top.Chan2_1.Cmd := Empty;
  top.Chan3_1.Cmd := InvAck;
  if (top.Cache_1.State == E) {
    top.Chan3_1.Data := top.Cache_1.Data;
  }
  top.Cache_1.State := I;
};

method n_n_RecvInvAck_i1(top:TopC)
requires 

//1//guard condition
requires   ((top.Chan3_1.Cmd == InvAck) && (!(top.CurCmd == Empty)));
ensures   (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))

modifies top
{
  top.ShrSet_1 := false;
  if (top.ExGntd == true) {
    top.ExGntd := false;
    top.MemData := top.Chan3_1.Data;
  }
  top.Chan3_1.Cmd := Empty;
};

method n_n_ARecvReq_i1(top:TopC)
requires 

requires (!((top.Chan3_1.Cmd == InvAck) && (top.CurCmd == Empty)))//3//guard condition
requires   ((top.CurCmd == Empty) && (!(top.AChan1_1.Cmd == Empty)));
ensures   (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))

modifies top
{
  top.CurCmd := top.AChan1_1.Cmd;
  top.AChan1_1.Cmd := Empty;
  top.CurPtr := 1;
  top.InvSet_1 := top.ShrSet_1;
  top.AInvSet_1 := top.AShrSet_1;
};

method n_n_SendReqEI_i1(top:TopC)
requires 
requires (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))//statement has nothing with prop--it guranttee itself
//guard condition
requires   ((top.Cache_1.State == I) && (top.Chan1_1.Cmd == Empty));
ensures   (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))

modifies top
{
  top.Chan1_1.Cmd := ReqE;
};

method n_n_ASendReqEI_i1(top:TopC)
requires 
requires (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))//statement has nothing with prop--it guranttee itself
//guard condition
requires   ((top.ACache_1.State == I) && (top.AChan1_1.Cmd == Empty));
ensures   (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))

modifies top
{
  top.AChan1_1.Cmd := ReqE;
};

method n_n_ASendReqIS_j1(top:TopC)
requires 
requires (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))//statement has nothing with prop--it guranttee itself
//guard condition
requires   ((top.ACache_1.State == I) && (top.AChan1_1.Cmd == Empty));
ensures   (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))

modifies top
{
  top.AChan1_1.Cmd := ReqS;
};

method n_n_SendGntE_i1(top:TopC)
requires 
requires (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))//statement has nothing with prop--it guranttee itself
//guard condition
requires   ((top.AShrSet_1 == false) && (top.Chan2_1.Cmd == Empty) && (top.CurCmd == ReqE) && (top.CurPtr == 1) && (top.ExGntd == false) && (top.ShrSet_1 == false));
ensures   (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))

modifies top
{
  top.ShrSet_1 := true;
  top.CurCmd := Empty;
  top.ExGntd := true;
  top.Chan2_1.Cmd := GntE;
  top.Chan2_1.Data := top.MemData;
};

method n_n_ASendReqES_i1(top:TopC)
requires 
requires (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))//statement has nothing with prop--it guranttee itself
//guard condition
requires   ((top.ACache_1.State == S) && (top.AChan1_1.Cmd == Empty));
ensures   (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))

modifies top
{
  top.AChan1_1.Cmd := ReqE;
};

method n_n_ARecvGntE_i1(top:TopC)
requires 
requires (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))//statement has nothing with prop--it guranttee itself
//guard condition
requires   (top.AChan2_1.Cmd == GntE);
ensures   (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))

modifies top
{
  top.ACache_1.State := E;
  top.AChan2_1.Cmd := Empty;
  top.ACache_1.Data := top.AChan2_1.Data;
};

method n_n_ASendGntS_i1(top:TopC)
requires 
requires (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))//statement has nothing with prop--it guranttee itself
//guard condition
requires   ((top.AChan2_1.Cmd == Empty) && (top.CurCmd == ReqS) && (top.CurPtr == 1) && (top.ExGntd == false));
ensures   (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))

modifies top
{
  top.AShrSet_1 := true;
  top.CurCmd := Empty;
  top.AChan2_1.Cmd := GntS;
  top.AChan2_1.Data := top.MemData;
};

method n_n_ARecvGntS_i1(top:TopC)
requires 
requires (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))//statement has nothing with prop--it guranttee itself
//guard condition
requires   (top.AChan2_1.Cmd == GntS);
ensures   (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))

modifies top
{
  top.ACache_1.State := S;
  top.AChan2_1.Cmd := Empty;
  top.ACache_1.Data := top.AChan2_1.Data;
};

method n_n_ASendInvE_i1(top:TopC)
requires 
requires (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))//statement has nothing with prop--it guranttee itself
//guard condition
requires   ((top.AChan2_1.Cmd == Empty) && (top.AInvSet_1 == true) && (top.CurCmd == ReqE));
ensures   (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))

modifies top
{
  top.AChan2_1.Cmd := Inv;
  top.AInvSet_1 := false;
};

method n_n_SendGntS_i1(top:TopC)
requires 
requires (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))//statement has nothing with prop--it guranttee itself
//guard condition
requires   ((top.Chan2_1.Cmd == Empty) && (top.CurCmd == ReqS) && (top.CurPtr == 1) && (top.ExGntd == false));
ensures   (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))

modifies top
{
  top.ShrSet_1 := true;
  top.CurCmd := Empty;
  top.Chan2_1.Cmd := GntS;
  top.Chan2_1.Data := top.MemData;
};

method n_n_ASendInvS_i1(top:TopC)
requires 
requires (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))//statement has nothing with prop--it guranttee itself
//guard condition
requires   ((top.AChan2_1.Cmd == Empty) && (top.AInvSet_1 == true) && (top.CurCmd == ReqS) && (top.ExGntd == true));
ensures   (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))

modifies top
{
  top.AChan2_1.Cmd := Inv;
  top.AInvSet_1 := false;
};

method n_n_SendReqES_i1(top:TopC)
requires 
requires (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))//statement has nothing with prop--it guranttee itself
//guard condition
requires   ((top.Cache_1.State == S) && (top.Chan1_1.Cmd == Empty));
ensures   (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))

modifies top
{
  top.Chan1_1.Cmd := ReqE;
};

method n_n_ASendReqSE_j1(top:TopC)
requires 
requires (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))//statement has nothing with prop--it guranttee itself
//guard condition
requires   ((top.ACache_1.State == E) && (top.AChan1_1.Cmd == Empty));
ensures   (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))

modifies top
{
  top.AChan1_1.Cmd := ReqS;
};

method n_n_RecvGntS_i1(top:TopC)
requires 
requires (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))//statement has nothing with prop--it guranttee itself
//guard condition
requires   (top.Chan2_1.Cmd == GntS);
ensures   (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))

modifies top
{
  top.Cache_1.State := S;
  top.Chan2_1.Cmd := Empty;
  top.Cache_1.Data := top.Chan2_1.Data;
};

method n_n_SendReqEE_i1(top:TopC)
requires 
requires (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))//statement has nothing with prop--it guranttee itself
//guard condition
requires   ((top.ACache_1.State == E) && (top.AChan1_1.Cmd == Empty));
ensures   (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))

modifies top
{
  top.AChan1_1.Cmd := ReqE;
};

method n_n_RecvGntE_i1(top:TopC)
requires 
requires (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))//statement has nothing with prop--it guranttee itself
//guard condition
requires   (top.Chan2_1.Cmd == GntE);
ensures   (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))

modifies top
{
  top.Cache_1.State := E;
  top.Chan2_1.Cmd := Empty;
  top.Cache_1.Data := top.Chan2_1.Data;
};

method n_n_Store_i1inv__75_0(top:TopC,d:nat, N4:nat )
requires 0<= d<N4




requires 
requires (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))//statement has nothing with prop--it guranttee itself

//guard condition
requires   (top.Cache_1.State == E)

ensures   (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))

modifies top


{
  top.Cache_1.Data := d;
  top.AuxData := d;
}


method n_n_AStore_i1inv__75_0(top:TopC,d:nat, N4:nat )
requires 0<= d<N4




requires 
requires (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))//statement has nothing with prop--it guranttee itself

//guard condition
requires   (top.ACache_1.State == E)

ensures   (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))

modifies top


{
  top.ACache_1.Data := d;
  top.AuxData := d;
}


method n_n_SendReqS_j1(top:TopC)
requires 
requires (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))//statement has nothing with prop--it guranttee itself
//guard condition
requires   ((top.Cache_1.State == I) && (top.Chan1_1.Cmd == Empty));
ensures   (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))

modifies top
{
  top.Chan1_1.Cmd := ReqS;
};

method n_n_ARecvInvAck_i1(top:TopC)
requires 
requires (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))//statement has nothing with prop--it guranttee itself
//guard condition
requires   ((top.AChan3_1.Cmd == InvAck) && (!(top.CurCmd == Empty)));
ensures   (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))

modifies top
{
  top.AShrSet_1 := false;
  if (top.ExGntd == true) {
    top.ExGntd := false;
    top.MemData := top.AChan3_1.Data;
  }
  top.AChan3_1.Cmd := Empty;
};

method n_n_ASendInvAck_i1(top:TopC)
requires 
requires (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))//statement has nothing with prop--it guranttee itself
//guard condition
requires   ((top.AChan2_1.Cmd == Inv) && (top.AChan3_1.Cmd == Empty));
ensures   (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))

modifies top
{
  top.AChan2_1.Cmd := Empty;
  top.AChan3_1.Cmd := InvAck;
  if (top.ACache_1.State == E) {
    top.AChan3_1.Data := top.ACache_1.Data;
  }
  top.ACache_1.State := I;
};

method n_n_ASendGntE_i1(top:TopC)
requires 
requires (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))//statement has nothing with prop--it guranttee itself
//guard condition
requires   ((top.AChan2_1.Cmd == Empty) && (top.AShrSet_1 == false) && (top.CurCmd == ReqE) && (top.CurPtr == 1) && (top.ExGntd == false) && (top.ShrSet_1 == false));
ensures   (!((top.InvSet_1 == true) && (top.Chan3_1.Cmd == InvAck)))

modifies top
{
  top.AShrSet_1 := true;
  top.CurCmd := Empty;
  top.ExGntd := true;
  top.AChan2_1.Cmd := GntE;
  top.AChan2_1.Data := top.MemData;
};

