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

method n_Storeinv__4_0(AuxData:array<DATA>,   Cache_Data:array<DATA>,   Cache_State:array<CACHE_STATE>,i:nat, N0:nat,d:nat, N1:nat,p__Inv4:nat)

requires AuxData.Length==N0


requires Cache_Data.Length==N0


requires Cache_State.Length==N0
requires 0<= i<N0

requires 0<= d<N1

requires  p__Inv4<N0
requires i==p__Inv4
//1
//guard condition
requires (Cache_State[i] == E)

ensures   (!((!(Cache_State[p__Inv4] == I)) && (!(Cache_Data[p__Inv4] == AuxData[0]))))
modifies AuxData
modifies Cache_Data
{
  Cache_Data[i] := d;
  AuxData[0] := d;
}

method n_Storeinv__4_1(AuxData:array<DATA>,   Cache_Data:array<DATA>,   Cache_State:array<CACHE_STATE>,i:nat, N0:nat,d:nat, N1:nat,p__Inv4:nat)

requires AuxData.Length==N0


requires Cache_Data.Length==N0


requires Cache_State.Length==N0
requires 0<= i<N0

requires 0<= d<N1

requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((Cache_State[i] == E) && (!(Cache_State[p__Inv4] == I))))//3
//guard condition
requires (Cache_State[i] == E)

ensures   (!((!(Cache_State[p__Inv4] == I)) && (!(Cache_Data[p__Inv4] == AuxData[0]))))
modifies AuxData
modifies Cache_Data
{
  Cache_Data[i] := d;
  AuxData[0] := d;
}


method n_SendInvAckinv__4_0(AuxData:array<DATA>,   Cache_Data:array<DATA>,   Cache_State:array<CACHE_STATE>, Chan2_Cmd:array<MSG_CMD>, Chan3_Cmd:array<MSG_CMD>, Chan3_Data:array<DATA>,i:nat, N0:nat,p__Inv4:nat)

requires AuxData.Length==N0


requires Cache_Data.Length==N0


requires Cache_State.Length==N0
requires Chan2_Cmd.Length==N0
requires Chan3_Cmd.Length==N0
requires Chan3_Data.Length==N0
requires 0<= i<N0

requires  p__Inv4<N0
requires i==p__Inv4
//1
//guard condition
requires ((Chan2_Cmd[i] == Inv) && (Chan3_Cmd[i] == Empty))

ensures   (!((!(Cache_State[p__Inv4] == I)) && (!(Cache_Data[p__Inv4] == AuxData[0]))))
modifies Cache_Data
modifies Cache_State
modifies Chan2_Cmd
modifies Chan3_Cmd
modifies Chan3_Data
{
  Chan2_Cmd[i] := Empty;
  Chan3_Cmd[i] := InvAck;
  if (Cache_State[i] == E) {
    Chan3_Data[i] := Cache_Data[i];
  }
  Cache_State[i] := I;
}

method n_SendInvAckinv__4_1(AuxData:array<DATA>,   Cache_Data:array<DATA>,   Cache_State:array<CACHE_STATE>, Chan2_Cmd:array<MSG_CMD>, Chan3_Cmd:array<MSG_CMD>, Chan3_Data:array<DATA>,i:nat, N0:nat,p__Inv4:nat)

requires AuxData.Length==N0


requires Cache_Data.Length==N0


requires Cache_State.Length==N0
requires Chan2_Cmd.Length==N0
requires Chan3_Cmd.Length==N0
requires Chan3_Data.Length==N0
requires 0<= i<N0

requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((!(Cache_State[p__Inv4] == I)) && (!(Cache_Data[p__Inv4] == AuxData[0]))))//2
//guard condition
requires ((Chan2_Cmd[i] == Inv) && (Chan3_Cmd[i] == Empty))

ensures   (!((!(Cache_State[p__Inv4] == I)) && (!(Cache_Data[p__Inv4] == AuxData[0]))))
modifies Cache_Data
modifies Cache_State
modifies Chan2_Cmd
modifies Chan3_Cmd
modifies Chan3_Data
{
  Chan2_Cmd[i] := Empty;
  Chan3_Cmd[i] := InvAck;
  if (Cache_State[i] == E) {
    Chan3_Data[i] := Cache_Data[i];
  }
  Cache_State[i] := I;
}


method n_RecvGntSinv__4_0(AuxData:array<DATA>,   Cache_Data:array<DATA>,   Cache_State:array<CACHE_STATE>, Chan2_Cmd:array<MSG_CMD>, Chan2_Data:array<DATA>,i:nat, N0:nat,p__Inv4:nat)

requires AuxData.Length==N0


requires Cache_Data.Length==N0


requires Cache_State.Length==N0
requires Chan2_Cmd.Length==N0
requires Chan2_Data.Length==N0
requires 0<= i<N0

requires  p__Inv4<N0
requires i==p__Inv4
requires (!((!(Chan2_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == GntS)))//3
//guard condition
requires (Chan2_Cmd[i] == GntS)

ensures   (!((!(Cache_State[p__Inv4] == I)) && (!(Cache_Data[p__Inv4] == AuxData[0]))))
modifies Cache_Data
modifies Cache_State
modifies Chan2_Cmd
modifies Chan2_Data
{
  Cache_State[i] := S;
  Cache_Data[i] := Chan2_Data[i];
  Chan2_Cmd[i] := Empty;
}

method n_RecvGntSinv__4_1(AuxData:array<DATA>,   Cache_Data:array<DATA>,   Cache_State:array<CACHE_STATE>, Chan2_Cmd:array<MSG_CMD>, Chan2_Data:array<DATA>,i:nat, N0:nat,p__Inv4:nat)

requires AuxData.Length==N0


requires Cache_Data.Length==N0


requires Cache_State.Length==N0
requires Chan2_Cmd.Length==N0
requires Chan2_Data.Length==N0
requires 0<= i<N0

requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((!(Cache_State[p__Inv4] == I)) && (!(Cache_Data[p__Inv4] == AuxData[0]))))//2
//guard condition
requires (Chan2_Cmd[i] == GntS)

ensures   (!((!(Cache_State[p__Inv4] == I)) && (!(Cache_Data[p__Inv4] == AuxData[0]))))
modifies Cache_Data
modifies Cache_State
modifies Chan2_Cmd
modifies Chan2_Data
{
  Cache_State[i] := S;
  Cache_Data[i] := Chan2_Data[i];
  Chan2_Cmd[i] := Empty;
}


method n_RecvGntEinv__4_0(AuxData:array<DATA>,   Cache_Data:array<DATA>,   Cache_State:array<CACHE_STATE>, Chan2_Cmd:array<MSG_CMD>, Chan2_Data:array<DATA>,i:nat, N0:nat,p__Inv4:nat)

requires AuxData.Length==N0


requires Cache_Data.Length==N0


requires Cache_State.Length==N0
requires Chan2_Cmd.Length==N0
requires Chan2_Data.Length==N0
requires 0<= i<N0

requires  p__Inv4<N0
requires i==p__Inv4
requires (!((!(Chan2_Data[p__Inv4] == AuxData[0])) && (Chan2_Cmd[p__Inv4] == GntE)))//3
//guard condition
requires (Chan2_Cmd[i] == GntE)

ensures   (!((!(Cache_State[p__Inv4] == I)) && (!(Cache_Data[p__Inv4] == AuxData[0]))))
modifies Cache_Data
modifies Cache_State
modifies Chan2_Cmd
modifies Chan2_Data
{
  Cache_State[i] := E;
  Cache_Data[i] := Chan2_Data[i];
  Chan2_Cmd[i] := Empty;
}

method n_RecvGntEinv__4_1(AuxData:array<DATA>,   Cache_Data:array<DATA>,   Cache_State:array<CACHE_STATE>, Chan2_Cmd:array<MSG_CMD>, Chan2_Data:array<DATA>,i:nat, N0:nat,p__Inv4:nat)

requires AuxData.Length==N0


requires Cache_Data.Length==N0


requires Cache_State.Length==N0
requires Chan2_Cmd.Length==N0
requires Chan2_Data.Length==N0
requires 0<= i<N0

requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((!(Cache_State[p__Inv4] == I)) && (!(Cache_Data[p__Inv4] == AuxData[0]))))//2
//guard condition
requires (Chan2_Cmd[i] == GntE)

ensures   (!((!(Cache_State[p__Inv4] == I)) && (!(Cache_Data[p__Inv4] == AuxData[0]))))
modifies Cache_Data
modifies Cache_State
modifies Chan2_Cmd
modifies Chan2_Data
{
  Cache_State[i] := E;
  Cache_Data[i] := Chan2_Data[i];
  Chan2_Cmd[i] := Empty;
}


method n_RecvInvAckinv__4_0(AuxData:array<DATA>,   Cache_Data:array<DATA>,  Cache_State:array<CACHE_STATE>, Chan3_Cmd:array<MSG_CMD>,  Chan3_Data:array<DATA>, CurCmd:array<MSG_CMD>, ExGntd:array<boolean>, MemData:array<DATA>, ShrSet:array<boolean>,i:nat, N0:nat,p__Inv4:nat)

requires AuxData.Length==N0


requires Cache_Data.Length==N0

requires Cache_State.Length==N0
requires Chan3_Cmd.Length==N0

requires Chan3_Data.Length==N0
requires CurCmd.Length==N0
requires ExGntd.Length==N0
requires MemData.Length==N0
requires ShrSet.Length==N0
requires 0<= i<N0

requires  p__Inv4<N0
requires (!((!(Cache_State[p__Inv4] == I)) && (!(Cache_Data[p__Inv4] == AuxData[0]))))//statement has nothing with prop--it guranttee itself

//guard condition
requires ((Chan3_Cmd[i] == InvAck) && (!(CurCmd[0] == Empty)))

ensures   (!((!(Cache_State[p__Inv4] == I)) && (!(Cache_Data[p__Inv4] == AuxData[0]))))
modifies Chan3_Cmd
modifies Chan3_Data
modifies ExGntd
modifies MemData
modifies ShrSet
{
  Chan3_Cmd[i] := Empty;
  ShrSet[i] := false;
  if (ExGntd[0] == true) {
    ExGntd[0] := false;
    MemData[0] := Chan3_Data[i];
  }
}


method n_SendGntSinv__4_0(AuxData:array<DATA>,   Cache_Data:array<DATA>,  Cache_State:array<CACHE_STATE>, Chan2_Cmd:array<MSG_CMD>,  Chan2_Data:array<DATA>, CurCmd:array<MSG_CMD>, CurPtr:array<NODE>, ExGntd:array<boolean>, MemData:array<DATA>, ShrSet:array<boolean>,i:nat, N0:nat,p__Inv4:nat)

requires AuxData.Length==N0


requires Cache_Data.Length==N0

requires Cache_State.Length==N0
requires Chan2_Cmd.Length==N0

requires Chan2_Data.Length==N0
requires CurCmd.Length==N0
requires CurPtr.Length==N0
requires ExGntd.Length==N0
requires MemData.Length==N0
requires ShrSet.Length==N0
requires 0<= i<N0

requires  p__Inv4<N0
requires (!((!(Cache_State[p__Inv4] == I)) && (!(Cache_Data[p__Inv4] == AuxData[0]))))//statement has nothing with prop--it guranttee itself

//guard condition
requires ((Chan2_Cmd[i] == Empty) && (CurCmd[0] == ReqS) && (CurPtr[0] == i) && (ExGntd[0] == false))

ensures   (!((!(Cache_State[p__Inv4] == I)) && (!(Cache_Data[p__Inv4] == AuxData[0]))))
modifies Chan2_Cmd
modifies Chan2_Data
modifies CurCmd
modifies MemData
modifies ShrSet
{
  Chan2_Cmd[i] := GntS;
  Chan2_Data[i] := MemData[0];
  ShrSet[i] := true;
  CurCmd[0] := Empty;
}


method n_RecvReqE__part__0inv__4_0(AuxData:array<DATA>,   Cache_Data:array<DATA>,  Cache_State:array<CACHE_STATE>,  CurCmd:array<MSG_CMD>, CurPtr:array<NODE>, InvSet:array<boolean>,  ShrSet:array<boolean>,i:nat, N0:nat,p__Inv4:nat)

requires AuxData.Length==N0


requires Cache_Data.Length==N0

requires Cache_State.Length==N0

requires CurCmd.Length==N0
requires CurPtr.Length==N0
requires InvSet.Length==N0

requires ShrSet.Length==N0
requires 0<= i<N0

requires  p__Inv4<N0
requires (!((!(Cache_State[p__Inv4] == I)) && (!(Cache_Data[p__Inv4] == AuxData[0]))))//statement has nothing with prop--it guranttee itself

//guard condition
requires ((CurCmd[0] == Empty) && (Cache_State[i] == I))

ensures   (!((!(Cache_State[p__Inv4] == I)) && (!(Cache_Data[p__Inv4] == AuxData[0]))))
modifies CurCmd
modifies CurPtr
modifies InvSet
modifies ShrSet
{
  CurCmd[0] := ReqE;
  CurPtr[0] := i;
  forall j  |0<= j<N0 {
    InvSet[j] := ShrSet[j];
  }
}


method n_SendInv__part__0inv__4_0(AuxData:array<DATA>,   Cache_Data:array<DATA>,  Cache_State:array<CACHE_STATE>, Chan2_Cmd:array<MSG_CMD>,  CurCmd:array<MSG_CMD>, InvSet:array<boolean>,i:nat, N0:nat,p__Inv4:nat)

requires AuxData.Length==N0


requires Cache_Data.Length==N0

requires Cache_State.Length==N0
requires Chan2_Cmd.Length==N0

requires CurCmd.Length==N0
requires InvSet.Length==N0
requires 0<= i<N0

requires  p__Inv4<N0
requires (!((!(Cache_State[p__Inv4] == I)) && (!(Cache_Data[p__Inv4] == AuxData[0]))))//statement has nothing with prop--it guranttee itself

//guard condition
requires ((Chan2_Cmd[i] == Empty) && (InvSet[i] == true) && (CurCmd[0] == ReqE))

ensures   (!((!(Cache_State[p__Inv4] == I)) && (!(Cache_Data[p__Inv4] == AuxData[0]))))
modifies Chan2_Cmd
modifies InvSet
{
  Chan2_Cmd[i] := Inv;
  InvSet[i] := false;
}


method n_SendInv__part__1inv__4_0(AuxData:array<DATA>,   Cache_Data:array<DATA>,  Cache_State:array<CACHE_STATE>, Chan2_Cmd:array<MSG_CMD>,  CurCmd:array<MSG_CMD>, ExGntd:array<boolean>, InvSet:array<boolean>,i:nat, N0:nat,p__Inv4:nat)

requires AuxData.Length==N0


requires Cache_Data.Length==N0

requires Cache_State.Length==N0
requires Chan2_Cmd.Length==N0

requires CurCmd.Length==N0
requires ExGntd.Length==N0
requires InvSet.Length==N0
requires 0<= i<N0

requires  p__Inv4<N0
requires (!((!(Cache_State[p__Inv4] == I)) && (!(Cache_Data[p__Inv4] == AuxData[0]))))//statement has nothing with prop--it guranttee itself

//guard condition
requires ((Chan2_Cmd[i] == Empty) && (InvSet[i] == true) && ((CurCmd[0] == ReqS) && (ExGntd[0] == true)))

ensures   (!((!(Cache_State[p__Inv4] == I)) && (!(Cache_Data[p__Inv4] == AuxData[0]))))
modifies Chan2_Cmd
modifies InvSet
{
  Chan2_Cmd[i] := Inv;
  InvSet[i] := false;
}


method n_SendGntEinv__4_0(AuxData:array<DATA>,   Cache_Data:array<DATA>,  Cache_State:array<CACHE_STATE>, Chan2_Cmd:array<MSG_CMD>,  Chan2_Data:array<DATA>, CurCmd:array<MSG_CMD>, CurPtr:array<NODE>, ExGntd:array<boolean>, MemData:array<DATA>, ShrSet:array<boolean>,     i:nat, N0:nat,p__Inv4:nat)

requires AuxData.Length==N0


requires Cache_Data.Length==N0

requires Cache_State.Length==N0
requires Chan2_Cmd.Length==N0

requires Chan2_Data.Length==N0
requires CurCmd.Length==N0
requires CurPtr.Length==N0
requires ExGntd.Length==N0
requires MemData.Length==N0
requires ShrSet.Length==N0





requires 0<= i<N0

requires  p__Inv4<N0
requires (!((!(Cache_State[p__Inv4] == I)) && (!(Cache_Data[p__Inv4] == AuxData[0]))))//statement has nothing with prop--it guranttee itself

//guard condition
requires ((Chan2_Cmd[i] == Empty) && (CurCmd[0] == ReqE) && (CurPtr[0] == i) && (ExGntd[0] == false) && (forall j  |0<= j<N0 :: (ShrSet[j] == false) ))

ensures   (!((!(Cache_State[p__Inv4] == I)) && (!(Cache_Data[p__Inv4] == AuxData[0]))))
modifies Chan2_Cmd
modifies Chan2_Data
modifies CurCmd
modifies ExGntd
modifies MemData
modifies ShrSet
{
  Chan2_Cmd[i] := GntE;
  Chan2_Data[i] := MemData[0];
  ShrSet[i] := true;
  ExGntd[0] := true;
  CurCmd[0] := Empty;
}


method n_RecvReqE__part__1inv__4_0(AuxData:array<DATA>,   Cache_Data:array<DATA>,  Cache_State:array<CACHE_STATE>,  CurCmd:array<MSG_CMD>, CurPtr:array<NODE>, InvSet:array<boolean>,  ShrSet:array<boolean>,i:nat, N0:nat,p__Inv4:nat)

requires AuxData.Length==N0


requires Cache_Data.Length==N0

requires Cache_State.Length==N0

requires CurCmd.Length==N0
requires CurPtr.Length==N0
requires InvSet.Length==N0

requires ShrSet.Length==N0
requires 0<= i<N0

requires  p__Inv4<N0
requires (!((!(Cache_State[p__Inv4] == I)) && (!(Cache_Data[p__Inv4] == AuxData[0]))))//statement has nothing with prop--it guranttee itself

//guard condition
requires ((CurCmd[0] == Empty) && (Cache_State[i] == S))

ensures   (!((!(Cache_State[p__Inv4] == I)) && (!(Cache_Data[p__Inv4] == AuxData[0]))))
modifies CurCmd
modifies CurPtr
modifies InvSet
modifies ShrSet
{
  CurCmd[0] := ReqE;
  CurPtr[0] := i;
  forall j  |0<= j<N0 {
    InvSet[j] := ShrSet[j];
  }
}


method n_RecvReqSinv__4_0(AuxData:array<DATA>,   Cache_Data:array<DATA>,  Cache_State:array<CACHE_STATE>,  CurCmd:array<MSG_CMD>, CurPtr:array<NODE>, InvSet:array<boolean>,  ShrSet:array<boolean>,i:nat, N0:nat,p__Inv4:nat)

requires AuxData.Length==N0


requires Cache_Data.Length==N0

requires Cache_State.Length==N0

requires CurCmd.Length==N0
requires CurPtr.Length==N0
requires InvSet.Length==N0

requires ShrSet.Length==N0
requires 0<= i<N0

requires  p__Inv4<N0
requires (!((!(Cache_State[p__Inv4] == I)) && (!(Cache_Data[p__Inv4] == AuxData[0]))))//statement has nothing with prop--it guranttee itself

//guard condition
requires ((Cache_State[i] == I) && (CurCmd[0] == Empty))

ensures   (!((!(Cache_State[p__Inv4] == I)) && (!(Cache_Data[p__Inv4] == AuxData[0]))))
modifies CurCmd
modifies CurPtr
modifies InvSet
modifies ShrSet
{
  CurCmd[0] := ReqS;
  CurPtr[0] := i;
  forall j  |0<= j<N0 {
    InvSet[j] := ShrSet[j];
  }
}


