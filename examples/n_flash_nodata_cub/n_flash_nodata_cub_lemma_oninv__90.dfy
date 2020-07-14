datatype CACHE_STATE = CACHE_I| CACHE_S| CACHE_E
datatype NODE_CMD = NODE_None| NODE_Get| NODE_GetX
datatype UNI_CMD = UNI_None| UNI_Get| UNI_GetX| UNI_Put| UNI_PutX| UNI_Nak
datatype INV_CMD = INV_None| INV_Inv| INV_InvAck
datatype RP_CMD = RP_None| RP_Replace
datatype WB_CMD = WB_None| WB_Wb
datatype SHWB_CMD = SHWB_None| SHWB_ShWb| SHWB_FAck
datatype NAKC_CMD = NAKC_None| NAKC_Nakc
type NODE=nat
type boolean=bool




method n_NI_Remote_Get_Nakinv__90_0(Sta_HomeUniMsg_Cmd:array<UNI_CMD>,   Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_Proc_CacheState:array<CACHE_STATE>,  Sta_UniMsg_Cmd:array<UNI_CMD>,  Sta_UniMsg_HomeProc:array<boolean>, Sta_UniMsg_Proc:array<NODE>,
N0:nat,src:nat,dst:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0
requires N0>0

requires Sta_HomeUniMsg_Cmd.Length==N0


requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_Proc_CacheState.Length==N0

requires Sta_UniMsg_Cmd.Length==N0

requires Sta_UniMsg_HomeProc.Length==N0
requires Sta_UniMsg_Proc.Length==N0
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]


requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_Proc_CacheState.Length&&0<=j<Sta_Proc_CacheState.Length==>Sta_Proc_CacheState[i]!=Sta_Proc_CacheState[j]

requires forall i,j::0<=i<Sta_UniMsg_Cmd.Length&&0<=j<Sta_UniMsg_Cmd.Length==>Sta_UniMsg_Cmd[i]!=Sta_UniMsg_Cmd[j]

requires forall i,j::0<=i<Sta_UniMsg_HomeProc.Length&&0<=j<Sta_UniMsg_HomeProc.Length==>Sta_UniMsg_HomeProc[i]!=Sta_UniMsg_HomeProc[j]
requires forall i,j::0<=i<Sta_UniMsg_Proc.Length&&0<=j<Sta_UniMsg_Proc.Length==>Sta_UniMsg_Proc[i]!=Sta_UniMsg_Proc[j]
requires 0<=src<N0
requires 0<=dst<N0

requires ((Sta_UniMsg_Cmd[src] == UNI_Get) && (Sta_UniMsg_HomeProc[src] == false) && (Sta_UniMsg_Proc[src] == dst) && (!(Sta_Proc_CacheState[dst] == CACHE_E)) && (!(src == dst))) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_NakcMsg_Cmd
modifies Sta_UniMsg_Cmd

{
  Sta_UniMsg_Cmd[src] := UNI_Nak;
  Sta_NakcMsg_Cmd[0] := NAKC_Nakc;
}


method n_NI_Remote_Get_Nak_Homeinv__90_0(Sta_HomeUniMsg_Cmd:array<UNI_CMD>,   Sta_HomeUniMsg_HomeProc:array<boolean>, Sta_HomeUniMsg_Proc:array<NODE>, Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_Proc_CacheState:array<CACHE_STATE>, 
N0:nat,dst:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_HomeUniMsg_Cmd.Length==N0


requires Sta_HomeUniMsg_HomeProc.Length==N0
requires Sta_HomeUniMsg_Proc.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_Proc_CacheState.Length==N0

requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]


requires forall i,j::0<=i<Sta_HomeUniMsg_HomeProc.Length&&0<=j<Sta_HomeUniMsg_HomeProc.Length==>Sta_HomeUniMsg_HomeProc[i]!=Sta_HomeUniMsg_HomeProc[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Proc.Length&&0<=j<Sta_HomeUniMsg_Proc.Length==>Sta_HomeUniMsg_Proc[i]!=Sta_HomeUniMsg_Proc[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_Proc_CacheState.Length&&0<=j<Sta_Proc_CacheState.Length==>Sta_Proc_CacheState[i]!=Sta_Proc_CacheState[j]

requires 0<=dst<N0

requires ((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_HomeUniMsg_HomeProc[0] == false) && (Sta_HomeUniMsg_Proc[0] == dst) && (!(Sta_Proc_CacheState[dst] == CACHE_E))) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_HomeUniMsg_Cmd
modifies Sta_NakcMsg_Cmd

{
  Sta_HomeUniMsg_Cmd[0] := UNI_Nak;
  Sta_NakcMsg_Cmd[0] := NAKC_Nakc;
}


method n_NI_Remote_Get_Put_Homeinv__90_0(Sta_HomeUniMsg_Cmd:array<UNI_CMD>,   Sta_HomeUniMsg_HomeProc:array<boolean>, Sta_HomeUniMsg_Proc:array<NODE>, Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_Proc_CacheState:array<CACHE_STATE>, 
N0:nat,dst:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_HomeUniMsg_Cmd.Length==N0


requires Sta_HomeUniMsg_HomeProc.Length==N0
requires Sta_HomeUniMsg_Proc.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_Proc_CacheState.Length==N0

requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]


requires forall i,j::0<=i<Sta_HomeUniMsg_HomeProc.Length&&0<=j<Sta_HomeUniMsg_HomeProc.Length==>Sta_HomeUniMsg_HomeProc[i]!=Sta_HomeUniMsg_HomeProc[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Proc.Length&&0<=j<Sta_HomeUniMsg_Proc.Length==>Sta_HomeUniMsg_Proc[i]!=Sta_HomeUniMsg_Proc[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_Proc_CacheState.Length&&0<=j<Sta_Proc_CacheState.Length==>Sta_Proc_CacheState[i]!=Sta_Proc_CacheState[j]

requires 0<=dst<N0

requires ((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_HomeUniMsg_HomeProc[0] == false) && (Sta_HomeUniMsg_Proc[0] == dst) && (Sta_Proc_CacheState[dst] == CACHE_E)) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_HomeUniMsg_Cmd
modifies Sta_Proc_CacheState

{
  Sta_Proc_CacheState[dst] := CACHE_S;
  Sta_HomeUniMsg_Cmd[0] := UNI_Put;
}


method n_NI_Remote_GetX_Nakinv__90_0(Sta_HomeUniMsg_Cmd:array<UNI_CMD>,   Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_Proc_CacheState:array<CACHE_STATE>,  Sta_UniMsg_Cmd:array<UNI_CMD>,  Sta_UniMsg_HomeProc:array<boolean>, Sta_UniMsg_Proc:array<NODE>,
N0:nat,src:nat,dst:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0
requires N0>0

requires Sta_HomeUniMsg_Cmd.Length==N0


requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_Proc_CacheState.Length==N0

requires Sta_UniMsg_Cmd.Length==N0

requires Sta_UniMsg_HomeProc.Length==N0
requires Sta_UniMsg_Proc.Length==N0
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]


requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_Proc_CacheState.Length&&0<=j<Sta_Proc_CacheState.Length==>Sta_Proc_CacheState[i]!=Sta_Proc_CacheState[j]

requires forall i,j::0<=i<Sta_UniMsg_Cmd.Length&&0<=j<Sta_UniMsg_Cmd.Length==>Sta_UniMsg_Cmd[i]!=Sta_UniMsg_Cmd[j]

requires forall i,j::0<=i<Sta_UniMsg_HomeProc.Length&&0<=j<Sta_UniMsg_HomeProc.Length==>Sta_UniMsg_HomeProc[i]!=Sta_UniMsg_HomeProc[j]
requires forall i,j::0<=i<Sta_UniMsg_Proc.Length&&0<=j<Sta_UniMsg_Proc.Length==>Sta_UniMsg_Proc[i]!=Sta_UniMsg_Proc[j]
requires 0<=src<N0
requires 0<=dst<N0

requires ((Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == false) && (Sta_UniMsg_Proc[src] == dst) && (!(Sta_Proc_CacheState[dst] == CACHE_E)) && (!(src == dst))) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_NakcMsg_Cmd
modifies Sta_UniMsg_Cmd

{
  Sta_UniMsg_Cmd[src] := UNI_Nak;
  Sta_NakcMsg_Cmd[0] := NAKC_Nakc;
}


method n_NI_Remote_GetX_Nak_Homeinv__90_0(Sta_HomeUniMsg_Cmd:array<UNI_CMD>,   Sta_HomeUniMsg_HomeProc:array<boolean>, Sta_HomeUniMsg_Proc:array<NODE>, Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_Proc_CacheState:array<CACHE_STATE>, 
N0:nat,dst:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_HomeUniMsg_Cmd.Length==N0


requires Sta_HomeUniMsg_HomeProc.Length==N0
requires Sta_HomeUniMsg_Proc.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_Proc_CacheState.Length==N0

requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]


requires forall i,j::0<=i<Sta_HomeUniMsg_HomeProc.Length&&0<=j<Sta_HomeUniMsg_HomeProc.Length==>Sta_HomeUniMsg_HomeProc[i]!=Sta_HomeUniMsg_HomeProc[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Proc.Length&&0<=j<Sta_HomeUniMsg_Proc.Length==>Sta_HomeUniMsg_Proc[i]!=Sta_HomeUniMsg_Proc[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_Proc_CacheState.Length&&0<=j<Sta_Proc_CacheState.Length==>Sta_Proc_CacheState[i]!=Sta_Proc_CacheState[j]

requires 0<=dst<N0

requires ((Sta_HomeUniMsg_Cmd[0] == UNI_GetX) && (Sta_HomeUniMsg_HomeProc[0] == false) && (Sta_HomeUniMsg_Proc[0] == dst) && (!(Sta_Proc_CacheState[dst] == CACHE_E))) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_HomeUniMsg_Cmd
modifies Sta_NakcMsg_Cmd

{
  Sta_HomeUniMsg_Cmd[0] := UNI_Nak;
  Sta_NakcMsg_Cmd[0] := NAKC_Nakc;
}


method n_NI_Remote_GetX_PutX_Homeinv__90_0(Sta_HomeUniMsg_Cmd:array<UNI_CMD>,   Sta_HomeUniMsg_HomeProc:array<boolean>, Sta_HomeUniMsg_Proc:array<NODE>, Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_Proc_CacheState:array<CACHE_STATE>, 
N0:nat,dst:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_HomeUniMsg_Cmd.Length==N0


requires Sta_HomeUniMsg_HomeProc.Length==N0
requires Sta_HomeUniMsg_Proc.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_Proc_CacheState.Length==N0

requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]


requires forall i,j::0<=i<Sta_HomeUniMsg_HomeProc.Length&&0<=j<Sta_HomeUniMsg_HomeProc.Length==>Sta_HomeUniMsg_HomeProc[i]!=Sta_HomeUniMsg_HomeProc[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Proc.Length&&0<=j<Sta_HomeUniMsg_Proc.Length==>Sta_HomeUniMsg_Proc[i]!=Sta_HomeUniMsg_Proc[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_Proc_CacheState.Length&&0<=j<Sta_Proc_CacheState.Length==>Sta_Proc_CacheState[i]!=Sta_Proc_CacheState[j]

requires 0<=dst<N0

requires ((Sta_HomeUniMsg_Cmd[0] == UNI_GetX) && (Sta_HomeUniMsg_HomeProc[0] == false) && (Sta_HomeUniMsg_Proc[0] == dst) && (Sta_Proc_CacheState[dst] == CACHE_E)) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_HomeUniMsg_Cmd
modifies Sta_Proc_CacheState

{
  Sta_Proc_CacheState[dst] := CACHE_I;
  Sta_HomeUniMsg_Cmd[0] := UNI_PutX;
}



method n_PI_Local_Get_Getinv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_HeadPtr:array<NODE>, Sta_Dir_HomeHeadPtr:array<boolean>, Sta_Dir_Pending:array<boolean>, Sta_HomeProc_CacheState:array<CACHE_STATE>, Sta_HomeProc_ProcCmd:array<NODE_CMD>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_HomeUniMsg_HomeProc:array<boolean>, Sta_HomeUniMsg_Proc:array<NODE>, Sta_NakcMsg_Cmd:array<NAKC_CMD>,
N0:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0
requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_HeadPtr.Length==N0
requires Sta_Dir_HomeHeadPtr.Length==N0
requires Sta_Dir_Pending.Length==N0
requires Sta_HomeProc_CacheState.Length==N0
requires Sta_HomeProc_ProcCmd.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_HomeUniMsg_HomeProc.Length==N0
requires Sta_HomeUniMsg_Proc.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_HeadPtr.Length&&0<=j<Sta_Dir_HeadPtr.Length==>Sta_Dir_HeadPtr[i]!=Sta_Dir_HeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HomeHeadPtr.Length&&0<=j<Sta_Dir_HomeHeadPtr.Length==>Sta_Dir_HomeHeadPtr[i]!=Sta_Dir_HomeHeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_HomeProc_CacheState.Length&&0<=j<Sta_HomeProc_CacheState.Length==>Sta_HomeProc_CacheState[i]!=Sta_HomeProc_CacheState[j]
requires forall i,j::0<=i<Sta_HomeProc_ProcCmd.Length&&0<=j<Sta_HomeProc_ProcCmd.Length==>Sta_HomeProc_ProcCmd[i]!=Sta_HomeProc_ProcCmd[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_HomeProc.Length&&0<=j<Sta_HomeUniMsg_HomeProc.Length==>Sta_HomeUniMsg_HomeProc[i]!=Sta_HomeUniMsg_HomeProc[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Proc.Length&&0<=j<Sta_HomeUniMsg_Proc.Length==>Sta_HomeUniMsg_Proc[i]!=Sta_HomeUniMsg_Proc[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
//guard condition
requires   ((Sta_Dir_Dirty[0] == true) && (Sta_Dir_Pending[0] == false) && (Sta_HomeProc_CacheState[0] == CACHE_I) && (Sta_HomeProc_ProcCmd[0] == NODE_None))
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_Pending
modifies Sta_HomeProc_ProcCmd
modifies Sta_HomeUniMsg_Cmd
modifies Sta_HomeUniMsg_HomeProc
modifies Sta_HomeUniMsg_Proc
{
  Sta_HomeProc_ProcCmd[0] := NODE_Get;
  Sta_Dir_Pending[0] := true;
  Sta_HomeUniMsg_Cmd[0] := UNI_Get;
  Sta_HomeUniMsg_Proc[0] := Sta_Dir_HeadPtr[0];
  Sta_HomeUniMsg_HomeProc[0] := Sta_Dir_HomeHeadPtr[0];
}


method n_PI_Local_GetX_GetX__part__0inv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_HeadPtr:array<NODE>, Sta_Dir_HomeHeadPtr:array<boolean>, Sta_Dir_Pending:array<boolean>, Sta_HomeProc_CacheState:array<CACHE_STATE>, Sta_HomeProc_ProcCmd:array<NODE_CMD>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_HomeUniMsg_HomeProc:array<boolean>, Sta_HomeUniMsg_Proc:array<NODE>, Sta_NakcMsg_Cmd:array<NAKC_CMD>,
N0:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0
requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_HeadPtr.Length==N0
requires Sta_Dir_HomeHeadPtr.Length==N0
requires Sta_Dir_Pending.Length==N0
requires Sta_HomeProc_CacheState.Length==N0
requires Sta_HomeProc_ProcCmd.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_HomeUniMsg_HomeProc.Length==N0
requires Sta_HomeUniMsg_Proc.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_HeadPtr.Length&&0<=j<Sta_Dir_HeadPtr.Length==>Sta_Dir_HeadPtr[i]!=Sta_Dir_HeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HomeHeadPtr.Length&&0<=j<Sta_Dir_HomeHeadPtr.Length==>Sta_Dir_HomeHeadPtr[i]!=Sta_Dir_HomeHeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_HomeProc_CacheState.Length&&0<=j<Sta_HomeProc_CacheState.Length==>Sta_HomeProc_CacheState[i]!=Sta_HomeProc_CacheState[j]
requires forall i,j::0<=i<Sta_HomeProc_ProcCmd.Length&&0<=j<Sta_HomeProc_ProcCmd.Length==>Sta_HomeProc_ProcCmd[i]!=Sta_HomeProc_ProcCmd[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_HomeProc.Length&&0<=j<Sta_HomeUniMsg_HomeProc.Length==>Sta_HomeUniMsg_HomeProc[i]!=Sta_HomeUniMsg_HomeProc[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Proc.Length&&0<=j<Sta_HomeUniMsg_Proc.Length==>Sta_HomeUniMsg_Proc[i]!=Sta_HomeUniMsg_Proc[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
//guard condition
requires   ((Sta_Dir_Dirty[0] == true) && (Sta_Dir_Pending[0] == false) && (Sta_HomeProc_ProcCmd[0] == NODE_None) && (Sta_HomeProc_CacheState[0] == CACHE_I))
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_Pending
modifies Sta_HomeProc_ProcCmd
modifies Sta_HomeUniMsg_Cmd
modifies Sta_HomeUniMsg_HomeProc
modifies Sta_HomeUniMsg_Proc
{
  Sta_HomeProc_ProcCmd[0] := NODE_GetX;
  Sta_Dir_Pending[0] := true;
  Sta_HomeUniMsg_Cmd[0] := UNI_GetX;
  Sta_HomeUniMsg_Proc[0] := Sta_Dir_HeadPtr[0];
  Sta_HomeUniMsg_HomeProc[0] := Sta_Dir_HomeHeadPtr[0];
}


method n_PI_Local_GetX_GetX__part__1inv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_HeadPtr:array<NODE>, Sta_Dir_HomeHeadPtr:array<boolean>, Sta_Dir_Pending:array<boolean>, Sta_HomeProc_CacheState:array<CACHE_STATE>, Sta_HomeProc_ProcCmd:array<NODE_CMD>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_HomeUniMsg_HomeProc:array<boolean>, Sta_HomeUniMsg_Proc:array<NODE>, Sta_NakcMsg_Cmd:array<NAKC_CMD>,
N0:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0
requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_HeadPtr.Length==N0
requires Sta_Dir_HomeHeadPtr.Length==N0
requires Sta_Dir_Pending.Length==N0
requires Sta_HomeProc_CacheState.Length==N0
requires Sta_HomeProc_ProcCmd.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_HomeUniMsg_HomeProc.Length==N0
requires Sta_HomeUniMsg_Proc.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_HeadPtr.Length&&0<=j<Sta_Dir_HeadPtr.Length==>Sta_Dir_HeadPtr[i]!=Sta_Dir_HeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HomeHeadPtr.Length&&0<=j<Sta_Dir_HomeHeadPtr.Length==>Sta_Dir_HomeHeadPtr[i]!=Sta_Dir_HomeHeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_HomeProc_CacheState.Length&&0<=j<Sta_HomeProc_CacheState.Length==>Sta_HomeProc_CacheState[i]!=Sta_HomeProc_CacheState[j]
requires forall i,j::0<=i<Sta_HomeProc_ProcCmd.Length&&0<=j<Sta_HomeProc_ProcCmd.Length==>Sta_HomeProc_ProcCmd[i]!=Sta_HomeProc_ProcCmd[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_HomeProc.Length&&0<=j<Sta_HomeUniMsg_HomeProc.Length==>Sta_HomeUniMsg_HomeProc[i]!=Sta_HomeUniMsg_HomeProc[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Proc.Length&&0<=j<Sta_HomeUniMsg_Proc.Length==>Sta_HomeUniMsg_Proc[i]!=Sta_HomeUniMsg_Proc[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
//guard condition
requires   ((Sta_Dir_Dirty[0] == true) && (Sta_Dir_Pending[0] == false) && (Sta_HomeProc_ProcCmd[0] == NODE_None) && (Sta_HomeProc_CacheState[0] == CACHE_S))
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_Pending
modifies Sta_HomeProc_ProcCmd
modifies Sta_HomeUniMsg_Cmd
modifies Sta_HomeUniMsg_HomeProc
modifies Sta_HomeUniMsg_Proc
{
  Sta_HomeProc_ProcCmd[0] := NODE_GetX;
  Sta_Dir_Pending[0] := true;
  Sta_HomeUniMsg_Cmd[0] := UNI_GetX;
  Sta_HomeUniMsg_Proc[0] := Sta_Dir_HeadPtr[0];
  Sta_HomeUniMsg_HomeProc[0] := Sta_Dir_HomeHeadPtr[0];
}


method n_NI_Nak_Homeinv__90_0(Sta_HomeProc_InvMarked:array<boolean>,   Sta_HomeProc_ProcCmd:array<NODE_CMD>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>,
N0:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0
requires Sta_HomeProc_InvMarked.Length==N0


requires Sta_HomeProc_ProcCmd.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires forall i,j::0<=i<Sta_HomeProc_InvMarked.Length&&0<=j<Sta_HomeProc_InvMarked.Length==>Sta_HomeProc_InvMarked[i]!=Sta_HomeProc_InvMarked[j]


requires forall i,j::0<=i<Sta_HomeProc_ProcCmd.Length&&0<=j<Sta_HomeProc_ProcCmd.Length==>Sta_HomeProc_ProcCmd[i]!=Sta_HomeProc_ProcCmd[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
//guard condition
requires   (Sta_HomeUniMsg_Cmd[0] == UNI_Nak)
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_HomeUniMsg_Cmd
{
  Sta_HomeUniMsg_Cmd[0] := UNI_None;
  Sta_HomeProc_ProcCmd[0] := NODE_None;
  Sta_HomeProc_InvMarked[0] := false;
}


method n_NI_Nak_Clearinv__90_0(Sta_Dir_Pending:array<boolean>,   Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>,
N0:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0
requires Sta_Dir_Pending.Length==N0


requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]


requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
//guard condition
requires   (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_Pending
modifies Sta_NakcMsg_Cmd
{
  Sta_NakcMsg_Cmd[0] := NAKC_None;
  Sta_Dir_Pending[0] := false;
}


method n_NI_Local_Putinv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_Local:array<boolean>, Sta_Dir_Pending:array<boolean>, Sta_HomeProc_CacheState:array<CACHE_STATE>, Sta_HomeProc_InvMarked:array<boolean>, Sta_HomeProc_ProcCmd:array<NODE_CMD>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>,
N0:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0
requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_Local.Length==N0
requires Sta_Dir_Pending.Length==N0
requires Sta_HomeProc_CacheState.Length==N0
requires Sta_HomeProc_InvMarked.Length==N0
requires Sta_HomeProc_ProcCmd.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_Local.Length&&0<=j<Sta_Dir_Local.Length==>Sta_Dir_Local[i]!=Sta_Dir_Local[j]
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_HomeProc_CacheState.Length&&0<=j<Sta_HomeProc_CacheState.Length==>Sta_HomeProc_CacheState[i]!=Sta_HomeProc_CacheState[j]
requires forall i,j::0<=i<Sta_HomeProc_InvMarked.Length&&0<=j<Sta_HomeProc_InvMarked.Length==>Sta_HomeProc_InvMarked[i]!=Sta_HomeProc_InvMarked[j]
requires forall i,j::0<=i<Sta_HomeProc_ProcCmd.Length&&0<=j<Sta_HomeProc_ProcCmd.Length==>Sta_HomeProc_ProcCmd[i]!=Sta_HomeProc_ProcCmd[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
//guard condition
requires   (Sta_HomeUniMsg_Cmd[0] == UNI_Put)
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_HomeUniMsg_Cmd
{
  Sta_HomeUniMsg_Cmd[0] := UNI_None;
  Sta_Dir_Pending[0] := false;
  Sta_Dir_Dirty[0] := false;
  Sta_Dir_Local[0] := true;
  Sta_HomeProc_ProcCmd[0] := NODE_None;
  if (Sta_HomeProc_InvMarked[0] == true) {
    Sta_HomeProc_InvMarked[0] := false;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    Sta_HomeProc_CacheState[0] := CACHE_S;
  }
}


method n_NI_Local_PutXAcksDoneinv__90_0(Sta_Dir_HeadVld:array<boolean>,   Sta_Dir_Local:array<boolean>, Sta_Dir_Pending:array<boolean>, Sta_HomeProc_CacheState:array<CACHE_STATE>, Sta_HomeProc_InvMarked:array<boolean>, Sta_HomeProc_ProcCmd:array<NODE_CMD>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>,
N0:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0
requires Sta_Dir_HeadVld.Length==N0


requires Sta_Dir_Local.Length==N0
requires Sta_Dir_Pending.Length==N0
requires Sta_HomeProc_CacheState.Length==N0
requires Sta_HomeProc_InvMarked.Length==N0
requires Sta_HomeProc_ProcCmd.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires forall i,j::0<=i<Sta_Dir_HeadVld.Length&&0<=j<Sta_Dir_HeadVld.Length==>Sta_Dir_HeadVld[i]!=Sta_Dir_HeadVld[j]


requires forall i,j::0<=i<Sta_Dir_Local.Length&&0<=j<Sta_Dir_Local.Length==>Sta_Dir_Local[i]!=Sta_Dir_Local[j]
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_HomeProc_CacheState.Length&&0<=j<Sta_HomeProc_CacheState.Length==>Sta_HomeProc_CacheState[i]!=Sta_HomeProc_CacheState[j]
requires forall i,j::0<=i<Sta_HomeProc_InvMarked.Length&&0<=j<Sta_HomeProc_InvMarked.Length==>Sta_HomeProc_InvMarked[i]!=Sta_HomeProc_InvMarked[j]
requires forall i,j::0<=i<Sta_HomeProc_ProcCmd.Length&&0<=j<Sta_HomeProc_ProcCmd.Length==>Sta_HomeProc_ProcCmd[i]!=Sta_HomeProc_ProcCmd[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
//guard condition
requires   (Sta_HomeUniMsg_Cmd[0] == UNI_PutX)
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_HeadVld
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_HomeUniMsg_Cmd
{
  Sta_HomeUniMsg_Cmd[0] := UNI_None;
  Sta_Dir_Pending[0] := false;
  Sta_Dir_Local[0] := true;
  Sta_Dir_HeadVld[0] := false;
  Sta_HomeProc_ProcCmd[0] := NODE_None;
  Sta_HomeProc_InvMarked[0] := false;
  Sta_HomeProc_CacheState[0] := CACHE_E;
}

method n_NI_Local_Get_Get__part__1inv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_HeadPtr:array<NODE>, Sta_Dir_HomeHeadPtr:array<boolean>, Sta_Dir_Local:array<boolean>, Sta_Dir_Pending:array<boolean>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_RpMsg_Cmd:array<RP_CMD>,  Sta_UniMsg_Cmd:array<UNI_CMD>, Sta_UniMsg_HomeProc:array<boolean>, Sta_UniMsg_Proc:array<NODE>,
N0:nat,src:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_HeadPtr.Length==N0
requires Sta_Dir_HomeHeadPtr.Length==N0
requires Sta_Dir_Local.Length==N0
requires Sta_Dir_Pending.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_RpMsg_Cmd.Length==N0

requires Sta_UniMsg_Cmd.Length==N0
requires Sta_UniMsg_HomeProc.Length==N0
requires Sta_UniMsg_Proc.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_HeadPtr.Length&&0<=j<Sta_Dir_HeadPtr.Length==>Sta_Dir_HeadPtr[i]!=Sta_Dir_HeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HomeHeadPtr.Length&&0<=j<Sta_Dir_HomeHeadPtr.Length==>Sta_Dir_HomeHeadPtr[i]!=Sta_Dir_HomeHeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_Local.Length&&0<=j<Sta_Dir_Local.Length==>Sta_Dir_Local[i]!=Sta_Dir_Local[j]
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_RpMsg_Cmd.Length&&0<=j<Sta_RpMsg_Cmd.Length==>Sta_RpMsg_Cmd[i]!=Sta_RpMsg_Cmd[j]

requires forall i,j::0<=i<Sta_UniMsg_Cmd.Length&&0<=j<Sta_UniMsg_Cmd.Length==>Sta_UniMsg_Cmd[i]!=Sta_UniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_UniMsg_HomeProc.Length&&0<=j<Sta_UniMsg_HomeProc.Length==>Sta_UniMsg_HomeProc[i]!=Sta_UniMsg_HomeProc[j]
requires forall i,j::0<=i<Sta_UniMsg_Proc.Length&&0<=j<Sta_UniMsg_Proc.Length==>Sta_UniMsg_Proc[i]!=Sta_UniMsg_Proc[j]
requires 0<=src<N0

requires ((Sta_Dir_Dirty[0] == true) && (Sta_Dir_Local[0] == false) && (Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_Get) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_RpMsg_Cmd[src] == RP_Replace)) && (!(Sta_Dir_HeadPtr[0] == src))) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_Pending
modifies Sta_UniMsg_Cmd
modifies Sta_UniMsg_HomeProc
modifies Sta_UniMsg_Proc

{
  Sta_Dir_Pending[0] := true;
  Sta_UniMsg_Cmd[src] := UNI_Get;
  Sta_UniMsg_Proc[src] := Sta_Dir_HeadPtr[0];
  Sta_UniMsg_HomeProc[src] := Sta_Dir_HomeHeadPtr[0];
}


method n_PI_Remote_Getinv__90_0(Sta_HomeUniMsg_Cmd:array<UNI_CMD>,   Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_Proc_CacheState:array<CACHE_STATE>,  Sta_Proc_ProcCmd:array<NODE_CMD>, Sta_UniMsg_Cmd:array<UNI_CMD>, Sta_UniMsg_HomeProc:array<boolean>,
N0:nat,src:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_HomeUniMsg_Cmd.Length==N0


requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_Proc_CacheState.Length==N0

requires Sta_Proc_ProcCmd.Length==N0
requires Sta_UniMsg_Cmd.Length==N0
requires Sta_UniMsg_HomeProc.Length==N0
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]


requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_Proc_CacheState.Length&&0<=j<Sta_Proc_CacheState.Length==>Sta_Proc_CacheState[i]!=Sta_Proc_CacheState[j]

requires forall i,j::0<=i<Sta_Proc_ProcCmd.Length&&0<=j<Sta_Proc_ProcCmd.Length==>Sta_Proc_ProcCmd[i]!=Sta_Proc_ProcCmd[j]
requires forall i,j::0<=i<Sta_UniMsg_Cmd.Length&&0<=j<Sta_UniMsg_Cmd.Length==>Sta_UniMsg_Cmd[i]!=Sta_UniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_UniMsg_HomeProc.Length&&0<=j<Sta_UniMsg_HomeProc.Length==>Sta_UniMsg_HomeProc[i]!=Sta_UniMsg_HomeProc[j]
requires 0<=src<N0

requires ((Sta_Proc_CacheState[src] == CACHE_I) && (Sta_Proc_ProcCmd[src] == NODE_None)) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Proc_ProcCmd
modifies Sta_UniMsg_Cmd
modifies Sta_UniMsg_HomeProc

{
  Sta_Proc_ProcCmd[src] := NODE_Get;
  Sta_UniMsg_Cmd[src] := UNI_Get;
  Sta_UniMsg_HomeProc[src] := true;
}


method n_NI_Local_GetX_PutX_9__part__0inv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_HeadPtr:array<NODE>, Sta_Dir_HeadVld:array<boolean>, Sta_Dir_HomeHeadPtr:array<boolean>, Sta_Dir_HomeInvSet:array<boolean>, Sta_Dir_HomeShrSet:array<boolean>, Sta_Dir_InvSet:array<boolean>,  Sta_Dir_Local:array<boolean>, Sta_Dir_Pending:array<boolean>, Sta_Dir_ShrSet:array<boolean>, Sta_Dir_ShrVld:array<boolean>, Sta_HomeInvMsg_Cmd:array<INV_CMD>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_InvMsg_Cmd:array<INV_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_UniMsg_Cmd:array<UNI_CMD>,  Sta_UniMsg_HomeProc:array<boolean>,
N0:nat,src:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_HeadPtr.Length==N0
requires Sta_Dir_HeadVld.Length==N0
requires Sta_Dir_HomeHeadPtr.Length==N0
requires Sta_Dir_HomeInvSet.Length==N0
requires Sta_Dir_HomeShrSet.Length==N0
requires Sta_Dir_InvSet.Length==N0

requires Sta_Dir_Local.Length==N0
requires Sta_Dir_Pending.Length==N0
requires Sta_Dir_ShrSet.Length==N0
requires Sta_Dir_ShrVld.Length==N0
requires Sta_HomeInvMsg_Cmd.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_InvMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_UniMsg_Cmd.Length==N0

requires Sta_UniMsg_HomeProc.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_HeadPtr.Length&&0<=j<Sta_Dir_HeadPtr.Length==>Sta_Dir_HeadPtr[i]!=Sta_Dir_HeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HeadVld.Length&&0<=j<Sta_Dir_HeadVld.Length==>Sta_Dir_HeadVld[i]!=Sta_Dir_HeadVld[j]
requires forall i,j::0<=i<Sta_Dir_HomeHeadPtr.Length&&0<=j<Sta_Dir_HomeHeadPtr.Length==>Sta_Dir_HomeHeadPtr[i]!=Sta_Dir_HomeHeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HomeInvSet.Length&&0<=j<Sta_Dir_HomeInvSet.Length==>Sta_Dir_HomeInvSet[i]!=Sta_Dir_HomeInvSet[j]
requires forall i,j::0<=i<Sta_Dir_HomeShrSet.Length&&0<=j<Sta_Dir_HomeShrSet.Length==>Sta_Dir_HomeShrSet[i]!=Sta_Dir_HomeShrSet[j]
requires forall i,j::0<=i<Sta_Dir_InvSet.Length&&0<=j<Sta_Dir_InvSet.Length==>Sta_Dir_InvSet[i]!=Sta_Dir_InvSet[j]

requires forall i,j::0<=i<Sta_Dir_Local.Length&&0<=j<Sta_Dir_Local.Length==>Sta_Dir_Local[i]!=Sta_Dir_Local[j]
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_Dir_ShrSet.Length&&0<=j<Sta_Dir_ShrSet.Length==>Sta_Dir_ShrSet[i]!=Sta_Dir_ShrSet[j]
requires forall i,j::0<=i<Sta_Dir_ShrVld.Length&&0<=j<Sta_Dir_ShrVld.Length==>Sta_Dir_ShrVld[i]!=Sta_Dir_ShrVld[j]
requires forall i,j::0<=i<Sta_HomeInvMsg_Cmd.Length&&0<=j<Sta_HomeInvMsg_Cmd.Length==>Sta_HomeInvMsg_Cmd[i]!=Sta_HomeInvMsg_Cmd[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_InvMsg_Cmd.Length&&0<=j<Sta_InvMsg_Cmd.Length==>Sta_InvMsg_Cmd[i]!=Sta_InvMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_UniMsg_Cmd.Length&&0<=j<Sta_UniMsg_Cmd.Length==>Sta_UniMsg_Cmd[i]!=Sta_UniMsg_Cmd[j]

requires forall i,j::0<=i<Sta_UniMsg_HomeProc.Length&&0<=j<Sta_UniMsg_HomeProc.Length==>Sta_UniMsg_HomeProc[i]!=Sta_UniMsg_HomeProc[j]
requires 0<=src<N0

requires ((Sta_Dir_Dirty[0] == false) && (Sta_Dir_HeadVld[0] == true) && (Sta_Dir_Local[0] == false) && (Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (Sta_Dir_HomeHeadPtr[0] == true)) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd

{
  Sta_Dir_Pending[0] := true;
  Sta_Dir_Local[0] := false;
  Sta_Dir_Dirty[0] := true;
  Sta_Dir_HeadVld[0] := true;
  Sta_Dir_HeadPtr[0] := src;
  Sta_Dir_HomeHeadPtr[0] := false;
  Sta_Dir_ShrVld[0] := false;
  var p:=0;
  while(p<N0)
    decreases N0-p
 {
    Sta_Dir_ShrSet[p] := false;
    if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
      Sta_Dir_InvSet[p] := true;
      Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
      Sta_Dir_InvSet[p] := false;
      Sta_InvMsg_Cmd[p] := INV_None;
    }
  
 p:=p+1;
}
  Sta_Dir_HomeShrSet[0] := false;
  Sta_Dir_HomeInvSet[0] := false;
  Sta_HomeInvMsg_Cmd[0] := INV_None;
  Sta_UniMsg_Cmd[src] := UNI_PutX;
}



method n_PI_Local_GetX_PutX__part__0inv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_HeadVld:array<boolean>, Sta_Dir_Local:array<boolean>, Sta_Dir_Pending:array<boolean>, Sta_HomeProc_CacheState:array<CACHE_STATE>, Sta_HomeProc_InvMarked:array<boolean>, Sta_HomeProc_ProcCmd:array<NODE_CMD>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>,
N0:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0
requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_HeadVld.Length==N0
requires Sta_Dir_Local.Length==N0
requires Sta_Dir_Pending.Length==N0
requires Sta_HomeProc_CacheState.Length==N0
requires Sta_HomeProc_InvMarked.Length==N0
requires Sta_HomeProc_ProcCmd.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_HeadVld.Length&&0<=j<Sta_Dir_HeadVld.Length==>Sta_Dir_HeadVld[i]!=Sta_Dir_HeadVld[j]
requires forall i,j::0<=i<Sta_Dir_Local.Length&&0<=j<Sta_Dir_Local.Length==>Sta_Dir_Local[i]!=Sta_Dir_Local[j]
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_HomeProc_CacheState.Length&&0<=j<Sta_HomeProc_CacheState.Length==>Sta_HomeProc_CacheState[i]!=Sta_HomeProc_CacheState[j]
requires forall i,j::0<=i<Sta_HomeProc_InvMarked.Length&&0<=j<Sta_HomeProc_InvMarked.Length==>Sta_HomeProc_InvMarked[i]!=Sta_HomeProc_InvMarked[j]
requires forall i,j::0<=i<Sta_HomeProc_ProcCmd.Length&&0<=j<Sta_HomeProc_ProcCmd.Length==>Sta_HomeProc_ProcCmd[i]!=Sta_HomeProc_ProcCmd[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
//guard condition
requires   ((Sta_Dir_Dirty[0] == false) && (Sta_Dir_HeadVld[0] == false) && (Sta_Dir_Pending[0] == false) && (Sta_HomeProc_ProcCmd[0] == NODE_None) && (Sta_HomeProc_CacheState[0] == CACHE_I))
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_Local
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
{
  Sta_Dir_Local[0] := true;
  Sta_Dir_Dirty[0] := true;
  Sta_HomeProc_ProcCmd[0] := NODE_None;
  Sta_HomeProc_InvMarked[0] := false;
  Sta_HomeProc_CacheState[0] := CACHE_E;
}


method n_NI_Wbinv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_HeadVld:array<boolean>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_WbMsg_Cmd:array<WB_CMD>,
N0:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0
requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_HeadVld.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_WbMsg_Cmd.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_HeadVld.Length&&0<=j<Sta_Dir_HeadVld.Length==>Sta_Dir_HeadVld[i]!=Sta_Dir_HeadVld[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_WbMsg_Cmd.Length&&0<=j<Sta_WbMsg_Cmd.Length==>Sta_WbMsg_Cmd[i]!=Sta_WbMsg_Cmd[j]
//guard condition
requires   (Sta_WbMsg_Cmd[0] == WB_Wb)
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadVld
modifies Sta_WbMsg_Cmd
{
  Sta_WbMsg_Cmd[0] := WB_None;
  Sta_Dir_Dirty[0] := false;
  Sta_Dir_HeadVld[0] := false;
}

method n_NI_Local_GetX_PutX_5inv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_HeadPtr:array<NODE>, Sta_Dir_HeadVld:array<boolean>, Sta_Dir_HomeHeadPtr:array<boolean>, Sta_Dir_HomeInvSet:array<boolean>, Sta_Dir_HomeShrSet:array<boolean>, Sta_Dir_InvSet:array<boolean>,  Sta_Dir_Local:array<boolean>, Sta_Dir_Pending:array<boolean>, Sta_Dir_ShrSet:array<boolean>,      Sta_Dir_ShrVld:array<boolean>, Sta_HomeProc_CacheState:array<CACHE_STATE>, Sta_HomeProc_ProcCmd:array<NODE_CMD>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_UniMsg_Cmd:array<UNI_CMD>,  Sta_UniMsg_HomeProc:array<boolean>,
N0:nat,src:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_HeadPtr.Length==N0
requires Sta_Dir_HeadVld.Length==N0
requires Sta_Dir_HomeHeadPtr.Length==N0
requires Sta_Dir_HomeInvSet.Length==N0
requires Sta_Dir_HomeShrSet.Length==N0
requires Sta_Dir_InvSet.Length==N0

requires Sta_Dir_Local.Length==N0
requires Sta_Dir_Pending.Length==N0
requires Sta_Dir_ShrSet.Length==N0





requires Sta_Dir_ShrVld.Length==N0
requires Sta_HomeProc_CacheState.Length==N0
requires Sta_HomeProc_ProcCmd.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_UniMsg_Cmd.Length==N0

requires Sta_UniMsg_HomeProc.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_HeadPtr.Length&&0<=j<Sta_Dir_HeadPtr.Length==>Sta_Dir_HeadPtr[i]!=Sta_Dir_HeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HeadVld.Length&&0<=j<Sta_Dir_HeadVld.Length==>Sta_Dir_HeadVld[i]!=Sta_Dir_HeadVld[j]
requires forall i,j::0<=i<Sta_Dir_HomeHeadPtr.Length&&0<=j<Sta_Dir_HomeHeadPtr.Length==>Sta_Dir_HomeHeadPtr[i]!=Sta_Dir_HomeHeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HomeInvSet.Length&&0<=j<Sta_Dir_HomeInvSet.Length==>Sta_Dir_HomeInvSet[i]!=Sta_Dir_HomeInvSet[j]
requires forall i,j::0<=i<Sta_Dir_HomeShrSet.Length&&0<=j<Sta_Dir_HomeShrSet.Length==>Sta_Dir_HomeShrSet[i]!=Sta_Dir_HomeShrSet[j]
requires forall i,j::0<=i<Sta_Dir_InvSet.Length&&0<=j<Sta_Dir_InvSet.Length==>Sta_Dir_InvSet[i]!=Sta_Dir_InvSet[j]

requires forall i,j::0<=i<Sta_Dir_Local.Length&&0<=j<Sta_Dir_Local.Length==>Sta_Dir_Local[i]!=Sta_Dir_Local[j]
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_Dir_ShrSet.Length&&0<=j<Sta_Dir_ShrSet.Length==>Sta_Dir_ShrSet[i]!=Sta_Dir_ShrSet[j]





requires forall i,j::0<=i<Sta_Dir_ShrVld.Length&&0<=j<Sta_Dir_ShrVld.Length==>Sta_Dir_ShrVld[i]!=Sta_Dir_ShrVld[j]
requires forall i,j::0<=i<Sta_HomeProc_CacheState.Length&&0<=j<Sta_HomeProc_CacheState.Length==>Sta_HomeProc_CacheState[i]!=Sta_HomeProc_CacheState[j]
requires forall i,j::0<=i<Sta_HomeProc_ProcCmd.Length&&0<=j<Sta_HomeProc_ProcCmd.Length==>Sta_HomeProc_ProcCmd[i]!=Sta_HomeProc_ProcCmd[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_UniMsg_Cmd.Length&&0<=j<Sta_UniMsg_Cmd.Length==>Sta_UniMsg_Cmd[i]!=Sta_UniMsg_Cmd[j]

requires forall i,j::0<=i<Sta_UniMsg_HomeProc.Length&&0<=j<Sta_UniMsg_HomeProc.Length==>Sta_UniMsg_HomeProc[i]!=Sta_UniMsg_HomeProc[j]
requires 0<=src<N0

requires ((Sta_Dir_Dirty[0] == false) && (Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false) && (Sta_Dir_HomeShrSet[0] == false) && (Sta_Dir_Local[0] == true) && (Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_HomeProc_ProcCmd[0] == NODE_Get)) && (forall p  |0<= p<N0 :: ((Sta_Dir_ShrSet[p] == false) || (p == src)) )) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeProc_CacheState
modifies Sta_UniMsg_Cmd

{
  Sta_Dir_Local[0] := false;
  Sta_Dir_Dirty[0] := true;
  Sta_Dir_HeadVld[0] := true;
  Sta_Dir_HeadPtr[0] := src;
  Sta_Dir_HomeHeadPtr[0] := false;
  Sta_Dir_ShrVld[0] := false;
  var p:=0;
  while(p<N0)
    decreases N0-p
 {
    Sta_Dir_ShrSet[p] := false;
    Sta_Dir_InvSet[p] := false;
  
 p:=p+1;
}
  Sta_Dir_HomeShrSet[0] := false;
  Sta_Dir_HomeInvSet[0] := false;
  Sta_UniMsg_Cmd[src] := UNI_PutX;
  Sta_HomeProc_CacheState[0] := CACHE_I;
}


method n_NI_Local_GetX_GetX__part__1inv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_HeadPtr:array<NODE>, Sta_Dir_HomeHeadPtr:array<boolean>, Sta_Dir_Local:array<boolean>, Sta_Dir_Pending:array<boolean>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_UniMsg_Cmd:array<UNI_CMD>,  Sta_UniMsg_HomeProc:array<boolean>, Sta_UniMsg_Proc:array<NODE>,
N0:nat,src:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_HeadPtr.Length==N0
requires Sta_Dir_HomeHeadPtr.Length==N0
requires Sta_Dir_Local.Length==N0
requires Sta_Dir_Pending.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_UniMsg_Cmd.Length==N0

requires Sta_UniMsg_HomeProc.Length==N0
requires Sta_UniMsg_Proc.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_HeadPtr.Length&&0<=j<Sta_Dir_HeadPtr.Length==>Sta_Dir_HeadPtr[i]!=Sta_Dir_HeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HomeHeadPtr.Length&&0<=j<Sta_Dir_HomeHeadPtr.Length==>Sta_Dir_HomeHeadPtr[i]!=Sta_Dir_HomeHeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_Local.Length&&0<=j<Sta_Dir_Local.Length==>Sta_Dir_Local[i]!=Sta_Dir_Local[j]
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_UniMsg_Cmd.Length&&0<=j<Sta_UniMsg_Cmd.Length==>Sta_UniMsg_Cmd[i]!=Sta_UniMsg_Cmd[j]

requires forall i,j::0<=i<Sta_UniMsg_HomeProc.Length&&0<=j<Sta_UniMsg_HomeProc.Length==>Sta_UniMsg_HomeProc[i]!=Sta_UniMsg_HomeProc[j]
requires forall i,j::0<=i<Sta_UniMsg_Proc.Length&&0<=j<Sta_UniMsg_Proc.Length==>Sta_UniMsg_Proc[i]!=Sta_UniMsg_Proc[j]
requires 0<=src<N0

requires ((Sta_Dir_Dirty[0] == true) && (Sta_Dir_Local[0] == false) && (Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_HeadPtr[0] == src))) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_Pending
modifies Sta_UniMsg_Cmd
modifies Sta_UniMsg_HomeProc
modifies Sta_UniMsg_Proc

{
  Sta_Dir_Pending[0] := true;
  Sta_UniMsg_Cmd[src] := UNI_GetX;
  Sta_UniMsg_Proc[src] := Sta_Dir_HeadPtr[0];
  Sta_UniMsg_HomeProc[src] := Sta_Dir_HomeHeadPtr[0];
}


method n_NI_InvAck_3inv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_HomeInvSet:array<boolean>, Sta_Dir_InvSet:array<boolean>,       Sta_Dir_Pending:array<boolean>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_InvMsg_Cmd:array<INV_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>,
N0:nat,src:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_HomeInvSet.Length==N0
requires Sta_Dir_InvSet.Length==N0






requires Sta_Dir_Pending.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_InvMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_HomeInvSet.Length&&0<=j<Sta_Dir_HomeInvSet.Length==>Sta_Dir_HomeInvSet[i]!=Sta_Dir_HomeInvSet[j]
requires forall i,j::0<=i<Sta_Dir_InvSet.Length&&0<=j<Sta_Dir_InvSet.Length==>Sta_Dir_InvSet[i]!=Sta_Dir_InvSet[j]






requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_InvMsg_Cmd.Length&&0<=j<Sta_InvMsg_Cmd.Length==>Sta_InvMsg_Cmd[i]!=Sta_InvMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires 0<=src<N0

requires ((Sta_Dir_Dirty[0] == true) && (Sta_Dir_HomeInvSet[0] == false) && (Sta_Dir_InvSet[src] == true) && (Sta_Dir_Pending[0] == true) && (Sta_InvMsg_Cmd[src] == INV_InvAck) && (forall p  |0<= p<N0 :: ((Sta_Dir_InvSet[p] == false) || (p == src)) )) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_InvSet
modifies Sta_Dir_Pending
modifies Sta_InvMsg_Cmd

{
  Sta_InvMsg_Cmd[src] := INV_None;
  Sta_Dir_InvSet[src] := false;
  Sta_Dir_Pending[0] := false;
}


method n_NI_Local_GetX_PutX_8_Home_NODE_Getinv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_HeadPtr:array<NODE>, Sta_Dir_HeadVld:array<boolean>, Sta_Dir_HomeHeadPtr:array<boolean>, Sta_Dir_HomeInvSet:array<boolean>, Sta_Dir_HomeShrSet:array<boolean>, Sta_Dir_InvSet:array<boolean>,  Sta_Dir_Local:array<boolean>, Sta_Dir_Pending:array<boolean>, Sta_Dir_ShrSet:array<boolean>, Sta_Dir_ShrVld:array<boolean>, Sta_HomeInvMsg_Cmd:array<INV_CMD>, Sta_HomeProc_CacheState:array<CACHE_STATE>, Sta_HomeProc_InvMarked:array<boolean>, Sta_HomeProc_ProcCmd:array<NODE_CMD>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_InvMsg_Cmd:array<INV_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_UniMsg_Cmd:array<UNI_CMD>,  Sta_UniMsg_HomeProc:array<boolean>,
N0:nat,src:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_HeadPtr.Length==N0
requires Sta_Dir_HeadVld.Length==N0
requires Sta_Dir_HomeHeadPtr.Length==N0
requires Sta_Dir_HomeInvSet.Length==N0
requires Sta_Dir_HomeShrSet.Length==N0
requires Sta_Dir_InvSet.Length==N0

requires Sta_Dir_Local.Length==N0
requires Sta_Dir_Pending.Length==N0
requires Sta_Dir_ShrSet.Length==N0
requires Sta_Dir_ShrVld.Length==N0
requires Sta_HomeInvMsg_Cmd.Length==N0
requires Sta_HomeProc_CacheState.Length==N0
requires Sta_HomeProc_InvMarked.Length==N0
requires Sta_HomeProc_ProcCmd.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_InvMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_UniMsg_Cmd.Length==N0

requires Sta_UniMsg_HomeProc.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_HeadPtr.Length&&0<=j<Sta_Dir_HeadPtr.Length==>Sta_Dir_HeadPtr[i]!=Sta_Dir_HeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HeadVld.Length&&0<=j<Sta_Dir_HeadVld.Length==>Sta_Dir_HeadVld[i]!=Sta_Dir_HeadVld[j]
requires forall i,j::0<=i<Sta_Dir_HomeHeadPtr.Length&&0<=j<Sta_Dir_HomeHeadPtr.Length==>Sta_Dir_HomeHeadPtr[i]!=Sta_Dir_HomeHeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HomeInvSet.Length&&0<=j<Sta_Dir_HomeInvSet.Length==>Sta_Dir_HomeInvSet[i]!=Sta_Dir_HomeInvSet[j]
requires forall i,j::0<=i<Sta_Dir_HomeShrSet.Length&&0<=j<Sta_Dir_HomeShrSet.Length==>Sta_Dir_HomeShrSet[i]!=Sta_Dir_HomeShrSet[j]
requires forall i,j::0<=i<Sta_Dir_InvSet.Length&&0<=j<Sta_Dir_InvSet.Length==>Sta_Dir_InvSet[i]!=Sta_Dir_InvSet[j]

requires forall i,j::0<=i<Sta_Dir_Local.Length&&0<=j<Sta_Dir_Local.Length==>Sta_Dir_Local[i]!=Sta_Dir_Local[j]
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_Dir_ShrSet.Length&&0<=j<Sta_Dir_ShrSet.Length==>Sta_Dir_ShrSet[i]!=Sta_Dir_ShrSet[j]
requires forall i,j::0<=i<Sta_Dir_ShrVld.Length&&0<=j<Sta_Dir_ShrVld.Length==>Sta_Dir_ShrVld[i]!=Sta_Dir_ShrVld[j]
requires forall i,j::0<=i<Sta_HomeInvMsg_Cmd.Length&&0<=j<Sta_HomeInvMsg_Cmd.Length==>Sta_HomeInvMsg_Cmd[i]!=Sta_HomeInvMsg_Cmd[j]
requires forall i,j::0<=i<Sta_HomeProc_CacheState.Length&&0<=j<Sta_HomeProc_CacheState.Length==>Sta_HomeProc_CacheState[i]!=Sta_HomeProc_CacheState[j]
requires forall i,j::0<=i<Sta_HomeProc_InvMarked.Length&&0<=j<Sta_HomeProc_InvMarked.Length==>Sta_HomeProc_InvMarked[i]!=Sta_HomeProc_InvMarked[j]
requires forall i,j::0<=i<Sta_HomeProc_ProcCmd.Length&&0<=j<Sta_HomeProc_ProcCmd.Length==>Sta_HomeProc_ProcCmd[i]!=Sta_HomeProc_ProcCmd[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_InvMsg_Cmd.Length&&0<=j<Sta_InvMsg_Cmd.Length==>Sta_InvMsg_Cmd[i]!=Sta_InvMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_UniMsg_Cmd.Length&&0<=j<Sta_UniMsg_Cmd.Length==>Sta_UniMsg_Cmd[i]!=Sta_UniMsg_Cmd[j]

requires forall i,j::0<=i<Sta_UniMsg_HomeProc.Length&&0<=j<Sta_UniMsg_HomeProc.Length==>Sta_UniMsg_HomeProc[i]!=Sta_UniMsg_HomeProc[j]
requires 0<=src<N0

requires ((Sta_Dir_Dirty[0] == false) && (Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HomeHeadPtr[0] == false) && (Sta_Dir_HomeShrSet[0] == true) && (Sta_Dir_Local[0] == true) && (Sta_Dir_Pending[0] == false) && (Sta_HomeProc_ProcCmd[0] == NODE_Get) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true)) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd

{
  Sta_Dir_Pending[0] := true;
  Sta_Dir_Local[0] := false;
  Sta_Dir_Dirty[0] := true;
  Sta_Dir_HeadVld[0] := true;
  Sta_Dir_HeadPtr[0] := src;
  Sta_Dir_HomeHeadPtr[0] := false;
  Sta_Dir_ShrVld[0] := false;
  var p:=0;
  while(p<N0)
    decreases N0-p
 {
    Sta_Dir_ShrSet[p] := false;
    if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
      Sta_Dir_InvSet[p] := true;
      Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
      Sta_Dir_InvSet[p] := false;
      Sta_InvMsg_Cmd[p] := INV_None;
    }
  
 p:=p+1;
}
  Sta_Dir_HomeShrSet[0] := false;
  Sta_Dir_HomeInvSet[0] := false;
  Sta_HomeInvMsg_Cmd[0] := INV_None;
  Sta_UniMsg_Cmd[src] := UNI_PutX;
  Sta_HomeProc_CacheState[0] := CACHE_I;
  Sta_HomeProc_InvMarked[0] := true;
}


method n_NI_Local_GetX_PutX_7_NODE_Get__part__1inv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_HeadPtr:array<NODE>, Sta_Dir_HeadVld:array<boolean>, Sta_Dir_HomeHeadPtr:array<boolean>, Sta_Dir_HomeInvSet:array<boolean>, Sta_Dir_HomeShrSet:array<boolean>, Sta_Dir_InvSet:array<boolean>,  Sta_Dir_Local:array<boolean>, Sta_Dir_Pending:array<boolean>, Sta_Dir_ShrSet:array<boolean>, Sta_Dir_ShrVld:array<boolean>, Sta_HomeInvMsg_Cmd:array<INV_CMD>, Sta_HomeProc_CacheState:array<CACHE_STATE>, Sta_HomeProc_InvMarked:array<boolean>, Sta_HomeProc_ProcCmd:array<NODE_CMD>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_InvMsg_Cmd:array<INV_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_UniMsg_Cmd:array<UNI_CMD>,  Sta_UniMsg_HomeProc:array<boolean>,
N0:nat,src:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_HeadPtr.Length==N0
requires Sta_Dir_HeadVld.Length==N0
requires Sta_Dir_HomeHeadPtr.Length==N0
requires Sta_Dir_HomeInvSet.Length==N0
requires Sta_Dir_HomeShrSet.Length==N0
requires Sta_Dir_InvSet.Length==N0

requires Sta_Dir_Local.Length==N0
requires Sta_Dir_Pending.Length==N0
requires Sta_Dir_ShrSet.Length==N0
requires Sta_Dir_ShrVld.Length==N0
requires Sta_HomeInvMsg_Cmd.Length==N0
requires Sta_HomeProc_CacheState.Length==N0
requires Sta_HomeProc_InvMarked.Length==N0
requires Sta_HomeProc_ProcCmd.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_InvMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_UniMsg_Cmd.Length==N0

requires Sta_UniMsg_HomeProc.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_HeadPtr.Length&&0<=j<Sta_Dir_HeadPtr.Length==>Sta_Dir_HeadPtr[i]!=Sta_Dir_HeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HeadVld.Length&&0<=j<Sta_Dir_HeadVld.Length==>Sta_Dir_HeadVld[i]!=Sta_Dir_HeadVld[j]
requires forall i,j::0<=i<Sta_Dir_HomeHeadPtr.Length&&0<=j<Sta_Dir_HomeHeadPtr.Length==>Sta_Dir_HomeHeadPtr[i]!=Sta_Dir_HomeHeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HomeInvSet.Length&&0<=j<Sta_Dir_HomeInvSet.Length==>Sta_Dir_HomeInvSet[i]!=Sta_Dir_HomeInvSet[j]
requires forall i,j::0<=i<Sta_Dir_HomeShrSet.Length&&0<=j<Sta_Dir_HomeShrSet.Length==>Sta_Dir_HomeShrSet[i]!=Sta_Dir_HomeShrSet[j]
requires forall i,j::0<=i<Sta_Dir_InvSet.Length&&0<=j<Sta_Dir_InvSet.Length==>Sta_Dir_InvSet[i]!=Sta_Dir_InvSet[j]

requires forall i,j::0<=i<Sta_Dir_Local.Length&&0<=j<Sta_Dir_Local.Length==>Sta_Dir_Local[i]!=Sta_Dir_Local[j]
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_Dir_ShrSet.Length&&0<=j<Sta_Dir_ShrSet.Length==>Sta_Dir_ShrSet[i]!=Sta_Dir_ShrSet[j]
requires forall i,j::0<=i<Sta_Dir_ShrVld.Length&&0<=j<Sta_Dir_ShrVld.Length==>Sta_Dir_ShrVld[i]!=Sta_Dir_ShrVld[j]
requires forall i,j::0<=i<Sta_HomeInvMsg_Cmd.Length&&0<=j<Sta_HomeInvMsg_Cmd.Length==>Sta_HomeInvMsg_Cmd[i]!=Sta_HomeInvMsg_Cmd[j]
requires forall i,j::0<=i<Sta_HomeProc_CacheState.Length&&0<=j<Sta_HomeProc_CacheState.Length==>Sta_HomeProc_CacheState[i]!=Sta_HomeProc_CacheState[j]
requires forall i,j::0<=i<Sta_HomeProc_InvMarked.Length&&0<=j<Sta_HomeProc_InvMarked.Length==>Sta_HomeProc_InvMarked[i]!=Sta_HomeProc_InvMarked[j]
requires forall i,j::0<=i<Sta_HomeProc_ProcCmd.Length&&0<=j<Sta_HomeProc_ProcCmd.Length==>Sta_HomeProc_ProcCmd[i]!=Sta_HomeProc_ProcCmd[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_InvMsg_Cmd.Length&&0<=j<Sta_InvMsg_Cmd.Length==>Sta_InvMsg_Cmd[i]!=Sta_InvMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_UniMsg_Cmd.Length&&0<=j<Sta_UniMsg_Cmd.Length==>Sta_UniMsg_Cmd[i]!=Sta_UniMsg_Cmd[j]

requires forall i,j::0<=i<Sta_UniMsg_HomeProc.Length&&0<=j<Sta_UniMsg_HomeProc.Length==>Sta_UniMsg_HomeProc[i]!=Sta_UniMsg_HomeProc[j]
requires 0<=src<N0

requires ((Sta_Dir_Dirty[0] == false) && (Sta_Dir_HeadVld[0] == true) && (Sta_Dir_Local[0] == true) && (Sta_Dir_Pending[0] == false) && (Sta_HomeProc_ProcCmd[0] == NODE_Get) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_HeadPtr[0] == src))) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd

{
  Sta_Dir_Pending[0] := true;
  Sta_Dir_Local[0] := false;
  Sta_Dir_Dirty[0] := true;
  Sta_Dir_HeadVld[0] := true;
  Sta_Dir_HeadPtr[0] := src;
  Sta_Dir_HomeHeadPtr[0] := false;
  Sta_Dir_ShrVld[0] := false;
  var p:=0;
  while(p<N0)
    decreases N0-p
 {
    Sta_Dir_ShrSet[p] := false;
    if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
      Sta_Dir_InvSet[p] := true;
      Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
      Sta_Dir_InvSet[p] := false;
      Sta_InvMsg_Cmd[p] := INV_None;
    }
  
 p:=p+1;
}
  Sta_Dir_HomeShrSet[0] := false;
  Sta_Dir_HomeInvSet[0] := false;
  Sta_HomeInvMsg_Cmd[0] := INV_None;
  Sta_UniMsg_Cmd[src] := UNI_PutX;
  Sta_HomeProc_CacheState[0] := CACHE_I;
  Sta_HomeProc_InvMarked[0] := true;
}


method n_NI_InvAck_1inv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_HomeInvSet:array<boolean>, Sta_Dir_InvSet:array<boolean>,       Sta_Dir_Local:array<boolean>, Sta_Dir_Pending:array<boolean>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_InvMsg_Cmd:array<INV_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>,
N0:nat,src:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_HomeInvSet.Length==N0
requires Sta_Dir_InvSet.Length==N0






requires Sta_Dir_Local.Length==N0
requires Sta_Dir_Pending.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_InvMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_HomeInvSet.Length&&0<=j<Sta_Dir_HomeInvSet.Length==>Sta_Dir_HomeInvSet[i]!=Sta_Dir_HomeInvSet[j]
requires forall i,j::0<=i<Sta_Dir_InvSet.Length&&0<=j<Sta_Dir_InvSet.Length==>Sta_Dir_InvSet[i]!=Sta_Dir_InvSet[j]






requires forall i,j::0<=i<Sta_Dir_Local.Length&&0<=j<Sta_Dir_Local.Length==>Sta_Dir_Local[i]!=Sta_Dir_Local[j]
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_InvMsg_Cmd.Length&&0<=j<Sta_InvMsg_Cmd.Length==>Sta_InvMsg_Cmd[i]!=Sta_InvMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires 0<=src<N0

requires ((Sta_Dir_Dirty[0] == false) && (Sta_Dir_HomeInvSet[0] == false) && (Sta_Dir_InvSet[src] == true) && (Sta_Dir_Local[0] == true) && (Sta_Dir_Pending[0] == true) && (Sta_InvMsg_Cmd[src] == INV_InvAck) && (forall p  |0<= p<N0 :: ((Sta_Dir_InvSet[p] == false) || (p == src)) )) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_InvMsg_Cmd

{
  Sta_InvMsg_Cmd[src] := INV_None;
  Sta_Dir_InvSet[src] := false;
  Sta_Dir_Pending[0] := false;
  Sta_Dir_Local[0] := false;
}


method n_PI_Remote_Replaceinv__90_0(Sta_HomeUniMsg_Cmd:array<UNI_CMD>,   Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_Proc_CacheState:array<CACHE_STATE>,  Sta_Proc_ProcCmd:array<NODE_CMD>, Sta_RpMsg_Cmd:array<RP_CMD>,
N0:nat,src:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_HomeUniMsg_Cmd.Length==N0


requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_Proc_CacheState.Length==N0

requires Sta_Proc_ProcCmd.Length==N0
requires Sta_RpMsg_Cmd.Length==N0
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]


requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_Proc_CacheState.Length&&0<=j<Sta_Proc_CacheState.Length==>Sta_Proc_CacheState[i]!=Sta_Proc_CacheState[j]

requires forall i,j::0<=i<Sta_Proc_ProcCmd.Length&&0<=j<Sta_Proc_ProcCmd.Length==>Sta_Proc_ProcCmd[i]!=Sta_Proc_ProcCmd[j]
requires forall i,j::0<=i<Sta_RpMsg_Cmd.Length&&0<=j<Sta_RpMsg_Cmd.Length==>Sta_RpMsg_Cmd[i]!=Sta_RpMsg_Cmd[j]
requires 0<=src<N0

requires ((Sta_Proc_CacheState[src] == CACHE_S) && (Sta_Proc_ProcCmd[src] == NODE_None)) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Proc_CacheState
modifies Sta_RpMsg_Cmd

{
  Sta_Proc_CacheState[src] := CACHE_I;
  Sta_RpMsg_Cmd[src] := RP_Replace;
}


method n_NI_Local_GetX_PutX_3inv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_HeadPtr:array<NODE>, Sta_Dir_HeadVld:array<boolean>, Sta_Dir_HomeHeadPtr:array<boolean>, Sta_Dir_HomeInvSet:array<boolean>, Sta_Dir_HomeShrSet:array<boolean>, Sta_Dir_InvSet:array<boolean>,  Sta_Dir_Local:array<boolean>, Sta_Dir_Pending:array<boolean>, Sta_Dir_ShrSet:array<boolean>, Sta_Dir_ShrVld:array<boolean>, Sta_HomeProc_CacheState:array<CACHE_STATE>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_UniMsg_Cmd:array<UNI_CMD>,  Sta_UniMsg_HomeProc:array<boolean>,
N0:nat,src:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_HeadPtr.Length==N0
requires Sta_Dir_HeadVld.Length==N0
requires Sta_Dir_HomeHeadPtr.Length==N0
requires Sta_Dir_HomeInvSet.Length==N0
requires Sta_Dir_HomeShrSet.Length==N0
requires Sta_Dir_InvSet.Length==N0

requires Sta_Dir_Local.Length==N0
requires Sta_Dir_Pending.Length==N0
requires Sta_Dir_ShrSet.Length==N0
requires Sta_Dir_ShrVld.Length==N0
requires Sta_HomeProc_CacheState.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_UniMsg_Cmd.Length==N0

requires Sta_UniMsg_HomeProc.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_HeadPtr.Length&&0<=j<Sta_Dir_HeadPtr.Length==>Sta_Dir_HeadPtr[i]!=Sta_Dir_HeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HeadVld.Length&&0<=j<Sta_Dir_HeadVld.Length==>Sta_Dir_HeadVld[i]!=Sta_Dir_HeadVld[j]
requires forall i,j::0<=i<Sta_Dir_HomeHeadPtr.Length&&0<=j<Sta_Dir_HomeHeadPtr.Length==>Sta_Dir_HomeHeadPtr[i]!=Sta_Dir_HomeHeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HomeInvSet.Length&&0<=j<Sta_Dir_HomeInvSet.Length==>Sta_Dir_HomeInvSet[i]!=Sta_Dir_HomeInvSet[j]
requires forall i,j::0<=i<Sta_Dir_HomeShrSet.Length&&0<=j<Sta_Dir_HomeShrSet.Length==>Sta_Dir_HomeShrSet[i]!=Sta_Dir_HomeShrSet[j]
requires forall i,j::0<=i<Sta_Dir_InvSet.Length&&0<=j<Sta_Dir_InvSet.Length==>Sta_Dir_InvSet[i]!=Sta_Dir_InvSet[j]

requires forall i,j::0<=i<Sta_Dir_Local.Length&&0<=j<Sta_Dir_Local.Length==>Sta_Dir_Local[i]!=Sta_Dir_Local[j]
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_Dir_ShrSet.Length&&0<=j<Sta_Dir_ShrSet.Length==>Sta_Dir_ShrSet[i]!=Sta_Dir_ShrSet[j]
requires forall i,j::0<=i<Sta_Dir_ShrVld.Length&&0<=j<Sta_Dir_ShrVld.Length==>Sta_Dir_ShrVld[i]!=Sta_Dir_ShrVld[j]
requires forall i,j::0<=i<Sta_HomeProc_CacheState.Length&&0<=j<Sta_HomeProc_CacheState.Length==>Sta_HomeProc_CacheState[i]!=Sta_HomeProc_CacheState[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_UniMsg_Cmd.Length&&0<=j<Sta_UniMsg_Cmd.Length==>Sta_UniMsg_Cmd[i]!=Sta_UniMsg_Cmd[j]

requires forall i,j::0<=i<Sta_UniMsg_HomeProc.Length&&0<=j<Sta_UniMsg_HomeProc.Length==>Sta_UniMsg_HomeProc[i]!=Sta_UniMsg_HomeProc[j]
requires 0<=src<N0

requires ((Sta_Dir_Dirty[0] == false) && (Sta_Dir_HeadVld[0] == false) && (Sta_Dir_Local[0] == false) && (Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true)) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeProc_CacheState
modifies Sta_UniMsg_Cmd

{
  Sta_Dir_Local[0] := false;
  Sta_Dir_Dirty[0] := true;
  Sta_Dir_HeadVld[0] := true;
  Sta_Dir_HeadPtr[0] := src;
  Sta_Dir_HomeHeadPtr[0] := false;
  Sta_Dir_ShrVld[0] := false;
  var p:=0;
  while(p<N0)
    decreases N0-p
 {
    Sta_Dir_ShrSet[p] := false;
    Sta_Dir_InvSet[p] := false;
  
 p:=p+1;
}
  Sta_Dir_HomeShrSet[0] := false;
  Sta_Dir_HomeInvSet[0] := false;
  Sta_UniMsg_Cmd[src] := UNI_PutX;
  Sta_HomeProc_CacheState[0] := CACHE_I;
}



method n_PI_Local_Replaceinv__90_0(Sta_Dir_Local:array<boolean>,   Sta_HomeProc_CacheState:array<CACHE_STATE>, Sta_HomeProc_ProcCmd:array<NODE_CMD>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>,
N0:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0
requires Sta_Dir_Local.Length==N0


requires Sta_HomeProc_CacheState.Length==N0
requires Sta_HomeProc_ProcCmd.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires forall i,j::0<=i<Sta_Dir_Local.Length&&0<=j<Sta_Dir_Local.Length==>Sta_Dir_Local[i]!=Sta_Dir_Local[j]


requires forall i,j::0<=i<Sta_HomeProc_CacheState.Length&&0<=j<Sta_HomeProc_CacheState.Length==>Sta_HomeProc_CacheState[i]!=Sta_HomeProc_CacheState[j]
requires forall i,j::0<=i<Sta_HomeProc_ProcCmd.Length&&0<=j<Sta_HomeProc_ProcCmd.Length==>Sta_HomeProc_ProcCmd[i]!=Sta_HomeProc_ProcCmd[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
//guard condition
requires   ((Sta_HomeProc_CacheState[0] == CACHE_S) && (Sta_HomeProc_ProcCmd[0] == NODE_None))
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_Local
modifies Sta_HomeProc_CacheState
{
  Sta_Dir_Local[0] := false;
  Sta_HomeProc_CacheState[0] := CACHE_I;
}

method n_NI_Local_GetX_Nak__part__1inv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_HeadPtr:array<NODE>, Sta_Dir_HomeHeadPtr:array<boolean>, Sta_Dir_Local:array<boolean>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_UniMsg_Cmd:array<UNI_CMD>,  Sta_UniMsg_HomeProc:array<boolean>,
N0:nat,src:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_HeadPtr.Length==N0
requires Sta_Dir_HomeHeadPtr.Length==N0
requires Sta_Dir_Local.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_UniMsg_Cmd.Length==N0

requires Sta_UniMsg_HomeProc.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_HeadPtr.Length&&0<=j<Sta_Dir_HeadPtr.Length==>Sta_Dir_HeadPtr[i]!=Sta_Dir_HeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HomeHeadPtr.Length&&0<=j<Sta_Dir_HomeHeadPtr.Length==>Sta_Dir_HomeHeadPtr[i]!=Sta_Dir_HomeHeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_Local.Length&&0<=j<Sta_Dir_Local.Length==>Sta_Dir_Local[i]!=Sta_Dir_Local[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_UniMsg_Cmd.Length&&0<=j<Sta_UniMsg_Cmd.Length==>Sta_UniMsg_Cmd[i]!=Sta_UniMsg_Cmd[j]

requires forall i,j::0<=i<Sta_UniMsg_HomeProc.Length&&0<=j<Sta_UniMsg_HomeProc.Length==>Sta_UniMsg_HomeProc[i]!=Sta_UniMsg_HomeProc[j]
requires 0<=src<N0

requires ((Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Dirty[0] == true) && (Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false) && (Sta_Dir_Local[0] == false))) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_UniMsg_Cmd

{
  Sta_UniMsg_Cmd[src] := UNI_Nak;
}


method n_NI_Local_Get_Nak__part__1inv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_HeadPtr:array<NODE>, Sta_Dir_HomeHeadPtr:array<boolean>, Sta_Dir_Local:array<boolean>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_RpMsg_Cmd:array<RP_CMD>,  Sta_UniMsg_Cmd:array<UNI_CMD>, Sta_UniMsg_HomeProc:array<boolean>,
N0:nat,src:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_HeadPtr.Length==N0
requires Sta_Dir_HomeHeadPtr.Length==N0
requires Sta_Dir_Local.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_RpMsg_Cmd.Length==N0

requires Sta_UniMsg_Cmd.Length==N0
requires Sta_UniMsg_HomeProc.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_HeadPtr.Length&&0<=j<Sta_Dir_HeadPtr.Length==>Sta_Dir_HeadPtr[i]!=Sta_Dir_HeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HomeHeadPtr.Length&&0<=j<Sta_Dir_HomeHeadPtr.Length==>Sta_Dir_HomeHeadPtr[i]!=Sta_Dir_HomeHeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_Local.Length&&0<=j<Sta_Dir_Local.Length==>Sta_Dir_Local[i]!=Sta_Dir_Local[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_RpMsg_Cmd.Length&&0<=j<Sta_RpMsg_Cmd.Length==>Sta_RpMsg_Cmd[i]!=Sta_RpMsg_Cmd[j]

requires forall i,j::0<=i<Sta_UniMsg_Cmd.Length&&0<=j<Sta_UniMsg_Cmd.Length==>Sta_UniMsg_Cmd[i]!=Sta_UniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_UniMsg_HomeProc.Length&&0<=j<Sta_UniMsg_HomeProc.Length==>Sta_UniMsg_HomeProc[i]!=Sta_UniMsg_HomeProc[j]
requires 0<=src<N0

requires ((Sta_UniMsg_Cmd[src] == UNI_Get) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_RpMsg_Cmd[src] == RP_Replace)) && ((Sta_Dir_Dirty[0] == true) && (Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false) && (Sta_Dir_Local[0] == false))) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_UniMsg_Cmd

{
  Sta_UniMsg_Cmd[src] := UNI_Nak;
}


method n_NI_Local_Get_Get__part__0inv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_HeadPtr:array<NODE>, Sta_Dir_HomeHeadPtr:array<boolean>, Sta_Dir_Local:array<boolean>, Sta_Dir_Pending:array<boolean>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_RpMsg_Cmd:array<RP_CMD>,  Sta_UniMsg_Cmd:array<UNI_CMD>, Sta_UniMsg_HomeProc:array<boolean>, Sta_UniMsg_Proc:array<NODE>,
N0:nat,src:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_HeadPtr.Length==N0
requires Sta_Dir_HomeHeadPtr.Length==N0
requires Sta_Dir_Local.Length==N0
requires Sta_Dir_Pending.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_RpMsg_Cmd.Length==N0

requires Sta_UniMsg_Cmd.Length==N0
requires Sta_UniMsg_HomeProc.Length==N0
requires Sta_UniMsg_Proc.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_HeadPtr.Length&&0<=j<Sta_Dir_HeadPtr.Length==>Sta_Dir_HeadPtr[i]!=Sta_Dir_HeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HomeHeadPtr.Length&&0<=j<Sta_Dir_HomeHeadPtr.Length==>Sta_Dir_HomeHeadPtr[i]!=Sta_Dir_HomeHeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_Local.Length&&0<=j<Sta_Dir_Local.Length==>Sta_Dir_Local[i]!=Sta_Dir_Local[j]
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_RpMsg_Cmd.Length&&0<=j<Sta_RpMsg_Cmd.Length==>Sta_RpMsg_Cmd[i]!=Sta_RpMsg_Cmd[j]

requires forall i,j::0<=i<Sta_UniMsg_Cmd.Length&&0<=j<Sta_UniMsg_Cmd.Length==>Sta_UniMsg_Cmd[i]!=Sta_UniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_UniMsg_HomeProc.Length&&0<=j<Sta_UniMsg_HomeProc.Length==>Sta_UniMsg_HomeProc[i]!=Sta_UniMsg_HomeProc[j]
requires forall i,j::0<=i<Sta_UniMsg_Proc.Length&&0<=j<Sta_UniMsg_Proc.Length==>Sta_UniMsg_Proc[i]!=Sta_UniMsg_Proc[j]
requires 0<=src<N0

requires ((Sta_Dir_Dirty[0] == true) && (Sta_Dir_Local[0] == false) && (Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_Get) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_RpMsg_Cmd[src] == RP_Replace)) && (Sta_Dir_HomeHeadPtr[0] == true)) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_Pending
modifies Sta_UniMsg_Cmd
modifies Sta_UniMsg_HomeProc
modifies Sta_UniMsg_Proc

{
  Sta_Dir_Pending[0] := true;
  Sta_UniMsg_Cmd[src] := UNI_Get;
  Sta_UniMsg_Proc[src] := Sta_Dir_HeadPtr[0];
  Sta_UniMsg_HomeProc[src] := Sta_Dir_HomeHeadPtr[0];
}


method n_NI_InvAck_existsinv__90_0(Sta_Dir_InvSet:array<boolean>,    Sta_Dir_Pending:array<boolean>,  Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_InvMsg_Cmd:array<INV_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>,
N0:nat,src:nat,pp:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0
requires N0>0

requires Sta_Dir_InvSet.Length==N0



requires Sta_Dir_Pending.Length==N0

requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_InvMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires forall i,j::0<=i<Sta_Dir_InvSet.Length&&0<=j<Sta_Dir_InvSet.Length==>Sta_Dir_InvSet[i]!=Sta_Dir_InvSet[j]



requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]

requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_InvMsg_Cmd.Length&&0<=j<Sta_InvMsg_Cmd.Length==>Sta_InvMsg_Cmd[i]!=Sta_InvMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires 0<=src<N0
requires 0<=pp<N0

requires ((Sta_Dir_InvSet[pp] == true) && (Sta_Dir_InvSet[src] == true) && (Sta_Dir_Pending[0] == true) && (Sta_InvMsg_Cmd[src] == INV_InvAck) && (!(pp == src))) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_InvSet
modifies Sta_InvMsg_Cmd

{
  Sta_InvMsg_Cmd[src] := INV_None;
  Sta_Dir_InvSet[src] := false;
}


method n_NI_Local_GetX_Nak__part__2inv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_Local:array<boolean>, Sta_HomeProc_CacheState:array<CACHE_STATE>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_UniMsg_Cmd:array<UNI_CMD>,  Sta_UniMsg_HomeProc:array<boolean>,
N0:nat,src:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_Local.Length==N0
requires Sta_HomeProc_CacheState.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_UniMsg_Cmd.Length==N0

requires Sta_UniMsg_HomeProc.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_Local.Length&&0<=j<Sta_Dir_Local.Length==>Sta_Dir_Local[i]!=Sta_Dir_Local[j]
requires forall i,j::0<=i<Sta_HomeProc_CacheState.Length&&0<=j<Sta_HomeProc_CacheState.Length==>Sta_HomeProc_CacheState[i]!=Sta_HomeProc_CacheState[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_UniMsg_Cmd.Length&&0<=j<Sta_UniMsg_Cmd.Length==>Sta_UniMsg_Cmd[i]!=Sta_UniMsg_Cmd[j]

requires forall i,j::0<=i<Sta_UniMsg_HomeProc.Length&&0<=j<Sta_UniMsg_HomeProc.Length==>Sta_UniMsg_HomeProc[i]!=Sta_UniMsg_HomeProc[j]
requires 0<=src<N0

requires ((Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && ((Sta_Dir_Dirty[0] == true) && (Sta_Dir_Local[0] == true) && (!(Sta_HomeProc_CacheState[0] == CACHE_E)))) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_UniMsg_Cmd

{
  Sta_UniMsg_Cmd[src] := UNI_Nak;
}


method n_PI_Remote_PutXinv__90_0(Sta_HomeUniMsg_Cmd:array<UNI_CMD>,   Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_Proc_CacheState:array<CACHE_STATE>,  Sta_Proc_ProcCmd:array<NODE_CMD>, Sta_WbMsg_Cmd:array<WB_CMD>, Sta_WbMsg_HomeProc:array<boolean>, Sta_WbMsg_Proc:array<NODE>,
N0:nat,dst:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_HomeUniMsg_Cmd.Length==N0


requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_Proc_CacheState.Length==N0

requires Sta_Proc_ProcCmd.Length==N0
requires Sta_WbMsg_Cmd.Length==N0
requires Sta_WbMsg_HomeProc.Length==N0
requires Sta_WbMsg_Proc.Length==N0
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]


requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_Proc_CacheState.Length&&0<=j<Sta_Proc_CacheState.Length==>Sta_Proc_CacheState[i]!=Sta_Proc_CacheState[j]

requires forall i,j::0<=i<Sta_Proc_ProcCmd.Length&&0<=j<Sta_Proc_ProcCmd.Length==>Sta_Proc_ProcCmd[i]!=Sta_Proc_ProcCmd[j]
requires forall i,j::0<=i<Sta_WbMsg_Cmd.Length&&0<=j<Sta_WbMsg_Cmd.Length==>Sta_WbMsg_Cmd[i]!=Sta_WbMsg_Cmd[j]
requires forall i,j::0<=i<Sta_WbMsg_HomeProc.Length&&0<=j<Sta_WbMsg_HomeProc.Length==>Sta_WbMsg_HomeProc[i]!=Sta_WbMsg_HomeProc[j]
requires forall i,j::0<=i<Sta_WbMsg_Proc.Length&&0<=j<Sta_WbMsg_Proc.Length==>Sta_WbMsg_Proc[i]!=Sta_WbMsg_Proc[j]
requires 0<=dst<N0

requires ((Sta_Proc_CacheState[dst] == CACHE_E) && (Sta_Proc_ProcCmd[dst] == NODE_None)) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Proc_CacheState
modifies Sta_WbMsg_Cmd
modifies Sta_WbMsg_HomeProc
modifies Sta_WbMsg_Proc

{
  Sta_Proc_CacheState[dst] := CACHE_I;
  Sta_WbMsg_Cmd[0] := WB_Wb;
  Sta_WbMsg_Proc[0] := dst;
  Sta_WbMsg_HomeProc[0] := false;
}


method n_NI_Local_Get_Put_Headinv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_HeadVld:array<boolean>, Sta_Dir_HomeInvSet:array<boolean>, Sta_Dir_HomeShrSet:array<boolean>, Sta_Dir_InvSet:array<boolean>,  Sta_Dir_Pending:array<boolean>, Sta_Dir_ShrSet:array<boolean>,  Sta_Dir_ShrVld:array<boolean>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_RpMsg_Cmd:array<RP_CMD>, Sta_UniMsg_Cmd:array<UNI_CMD>, Sta_UniMsg_HomeProc:array<boolean>,
N0:nat,src:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_HeadVld.Length==N0
requires Sta_Dir_HomeInvSet.Length==N0
requires Sta_Dir_HomeShrSet.Length==N0
requires Sta_Dir_InvSet.Length==N0

requires Sta_Dir_Pending.Length==N0
requires Sta_Dir_ShrSet.Length==N0

requires Sta_Dir_ShrVld.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_RpMsg_Cmd.Length==N0
requires Sta_UniMsg_Cmd.Length==N0
requires Sta_UniMsg_HomeProc.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_HeadVld.Length&&0<=j<Sta_Dir_HeadVld.Length==>Sta_Dir_HeadVld[i]!=Sta_Dir_HeadVld[j]
requires forall i,j::0<=i<Sta_Dir_HomeInvSet.Length&&0<=j<Sta_Dir_HomeInvSet.Length==>Sta_Dir_HomeInvSet[i]!=Sta_Dir_HomeInvSet[j]
requires forall i,j::0<=i<Sta_Dir_HomeShrSet.Length&&0<=j<Sta_Dir_HomeShrSet.Length==>Sta_Dir_HomeShrSet[i]!=Sta_Dir_HomeShrSet[j]
requires forall i,j::0<=i<Sta_Dir_InvSet.Length&&0<=j<Sta_Dir_InvSet.Length==>Sta_Dir_InvSet[i]!=Sta_Dir_InvSet[j]

requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_Dir_ShrSet.Length&&0<=j<Sta_Dir_ShrSet.Length==>Sta_Dir_ShrSet[i]!=Sta_Dir_ShrSet[j]

requires forall i,j::0<=i<Sta_Dir_ShrVld.Length&&0<=j<Sta_Dir_ShrVld.Length==>Sta_Dir_ShrVld[i]!=Sta_Dir_ShrVld[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_RpMsg_Cmd.Length&&0<=j<Sta_RpMsg_Cmd.Length==>Sta_RpMsg_Cmd[i]!=Sta_RpMsg_Cmd[j]
requires forall i,j::0<=i<Sta_UniMsg_Cmd.Length&&0<=j<Sta_UniMsg_Cmd.Length==>Sta_UniMsg_Cmd[i]!=Sta_UniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_UniMsg_HomeProc.Length&&0<=j<Sta_UniMsg_HomeProc.Length==>Sta_UniMsg_HomeProc[i]!=Sta_UniMsg_HomeProc[j]
requires 0<=src<N0

requires ((Sta_Dir_Dirty[0] == false) && (Sta_Dir_HeadVld[0] == true) && (Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_Get) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_RpMsg_Cmd[src] == RP_Replace))) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_UniMsg_Cmd

{
  Sta_Dir_ShrVld[0] := true;
  Sta_Dir_ShrSet[src] := true;
  var p:=0;
  while(p<N0)
    decreases N0-p
 {
    if (p == src) {
      Sta_Dir_InvSet[p] := true;}
else{
      Sta_Dir_InvSet[p] := Sta_Dir_ShrSet[p];
    }
  
 p:=p+1;
}
  Sta_Dir_HomeInvSet[0] := Sta_Dir_HomeShrSet[0];
  Sta_UniMsg_Cmd[src] := UNI_Put;
}


method n_NI_Invinv__90_0(Sta_HomeUniMsg_Cmd:array<UNI_CMD>,   Sta_InvMsg_Cmd:array<INV_CMD>,  Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_Proc_CacheState:array<CACHE_STATE>, Sta_Proc_InvMarked:array<boolean>, Sta_Proc_ProcCmd:array<NODE_CMD>,
N0:nat,dst:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_HomeUniMsg_Cmd.Length==N0


requires Sta_InvMsg_Cmd.Length==N0

requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_Proc_CacheState.Length==N0
requires Sta_Proc_InvMarked.Length==N0
requires Sta_Proc_ProcCmd.Length==N0
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]


requires forall i,j::0<=i<Sta_InvMsg_Cmd.Length&&0<=j<Sta_InvMsg_Cmd.Length==>Sta_InvMsg_Cmd[i]!=Sta_InvMsg_Cmd[j]

requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_Proc_CacheState.Length&&0<=j<Sta_Proc_CacheState.Length==>Sta_Proc_CacheState[i]!=Sta_Proc_CacheState[j]
requires forall i,j::0<=i<Sta_Proc_InvMarked.Length&&0<=j<Sta_Proc_InvMarked.Length==>Sta_Proc_InvMarked[i]!=Sta_Proc_InvMarked[j]
requires forall i,j::0<=i<Sta_Proc_ProcCmd.Length&&0<=j<Sta_Proc_ProcCmd.Length==>Sta_Proc_ProcCmd[i]!=Sta_Proc_ProcCmd[j]
requires 0<=dst<N0

requires (Sta_InvMsg_Cmd[dst] == INV_Inv) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_InvMsg_Cmd
modifies Sta_Proc_CacheState
modifies Sta_Proc_InvMarked
modifies Sta_Proc_ProcCmd

{
  Sta_InvMsg_Cmd[dst] := INV_InvAck;
  Sta_Proc_CacheState[dst] := CACHE_I;
  if (Sta_Proc_ProcCmd[dst] == NODE_Get) {
    Sta_Proc_InvMarked[dst] := true;
  }
}



method n_PI_Local_PutXinv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_Local:array<boolean>, Sta_Dir_Pending:array<boolean>, Sta_HomeProc_CacheState:array<CACHE_STATE>, Sta_HomeProc_ProcCmd:array<NODE_CMD>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>,
N0:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0
requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_Local.Length==N0
requires Sta_Dir_Pending.Length==N0
requires Sta_HomeProc_CacheState.Length==N0
requires Sta_HomeProc_ProcCmd.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_Local.Length&&0<=j<Sta_Dir_Local.Length==>Sta_Dir_Local[i]!=Sta_Dir_Local[j]
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_HomeProc_CacheState.Length&&0<=j<Sta_HomeProc_CacheState.Length==>Sta_HomeProc_CacheState[i]!=Sta_HomeProc_CacheState[j]
requires forall i,j::0<=i<Sta_HomeProc_ProcCmd.Length&&0<=j<Sta_HomeProc_ProcCmd.Length==>Sta_HomeProc_ProcCmd[i]!=Sta_HomeProc_ProcCmd[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
//guard condition
requires   ((Sta_HomeProc_CacheState[0] == CACHE_E) && (Sta_HomeProc_ProcCmd[0] == NODE_None))
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_HomeProc_CacheState
{
  if (Sta_Dir_Pending[0] == true) {
    Sta_HomeProc_CacheState[0] := CACHE_I;
    Sta_Dir_Dirty[0] := false;}
else{
    Sta_HomeProc_CacheState[0] := CACHE_I;
    Sta_Dir_Local[0] := false;
    Sta_Dir_Dirty[0] := false;
  }
}

method n_NI_Local_Get_Nak__part__2inv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_Local:array<boolean>, Sta_HomeProc_CacheState:array<CACHE_STATE>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_RpMsg_Cmd:array<RP_CMD>,  Sta_UniMsg_Cmd:array<UNI_CMD>, Sta_UniMsg_HomeProc:array<boolean>,
N0:nat,src:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_Local.Length==N0
requires Sta_HomeProc_CacheState.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_RpMsg_Cmd.Length==N0

requires Sta_UniMsg_Cmd.Length==N0
requires Sta_UniMsg_HomeProc.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_Local.Length&&0<=j<Sta_Dir_Local.Length==>Sta_Dir_Local[i]!=Sta_Dir_Local[j]
requires forall i,j::0<=i<Sta_HomeProc_CacheState.Length&&0<=j<Sta_HomeProc_CacheState.Length==>Sta_HomeProc_CacheState[i]!=Sta_HomeProc_CacheState[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_RpMsg_Cmd.Length&&0<=j<Sta_RpMsg_Cmd.Length==>Sta_RpMsg_Cmd[i]!=Sta_RpMsg_Cmd[j]

requires forall i,j::0<=i<Sta_UniMsg_Cmd.Length&&0<=j<Sta_UniMsg_Cmd.Length==>Sta_UniMsg_Cmd[i]!=Sta_UniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_UniMsg_HomeProc.Length&&0<=j<Sta_UniMsg_HomeProc.Length==>Sta_UniMsg_HomeProc[i]!=Sta_UniMsg_HomeProc[j]
requires 0<=src<N0

requires ((Sta_UniMsg_Cmd[src] == UNI_Get) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_RpMsg_Cmd[src] == RP_Replace)) && ((Sta_Dir_Dirty[0] == true) && (Sta_Dir_Local[0] == true) && (!(Sta_HomeProc_CacheState[0] == CACHE_E)))) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_UniMsg_Cmd

{
  Sta_UniMsg_Cmd[src] := UNI_Nak;
}


method n_NI_Local_GetX_GetX__part__0inv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_HeadPtr:array<NODE>, Sta_Dir_HomeHeadPtr:array<boolean>, Sta_Dir_Local:array<boolean>, Sta_Dir_Pending:array<boolean>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_UniMsg_Cmd:array<UNI_CMD>,  Sta_UniMsg_HomeProc:array<boolean>, Sta_UniMsg_Proc:array<NODE>,
N0:nat,src:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_HeadPtr.Length==N0
requires Sta_Dir_HomeHeadPtr.Length==N0
requires Sta_Dir_Local.Length==N0
requires Sta_Dir_Pending.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_UniMsg_Cmd.Length==N0

requires Sta_UniMsg_HomeProc.Length==N0
requires Sta_UniMsg_Proc.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_HeadPtr.Length&&0<=j<Sta_Dir_HeadPtr.Length==>Sta_Dir_HeadPtr[i]!=Sta_Dir_HeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HomeHeadPtr.Length&&0<=j<Sta_Dir_HomeHeadPtr.Length==>Sta_Dir_HomeHeadPtr[i]!=Sta_Dir_HomeHeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_Local.Length&&0<=j<Sta_Dir_Local.Length==>Sta_Dir_Local[i]!=Sta_Dir_Local[j]
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_UniMsg_Cmd.Length&&0<=j<Sta_UniMsg_Cmd.Length==>Sta_UniMsg_Cmd[i]!=Sta_UniMsg_Cmd[j]

requires forall i,j::0<=i<Sta_UniMsg_HomeProc.Length&&0<=j<Sta_UniMsg_HomeProc.Length==>Sta_UniMsg_HomeProc[i]!=Sta_UniMsg_HomeProc[j]
requires forall i,j::0<=i<Sta_UniMsg_Proc.Length&&0<=j<Sta_UniMsg_Proc.Length==>Sta_UniMsg_Proc[i]!=Sta_UniMsg_Proc[j]
requires 0<=src<N0

requires ((Sta_Dir_Dirty[0] == true) && (Sta_Dir_Local[0] == false) && (Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (Sta_Dir_HomeHeadPtr[0] == true)) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_Pending
modifies Sta_UniMsg_Cmd
modifies Sta_UniMsg_HomeProc
modifies Sta_UniMsg_Proc

{
  Sta_Dir_Pending[0] := true;
  Sta_UniMsg_Cmd[src] := UNI_GetX;
  Sta_UniMsg_Proc[src] := Sta_Dir_HeadPtr[0];
  Sta_UniMsg_HomeProc[src] := Sta_Dir_HomeHeadPtr[0];
}


method n_NI_Local_GetX_PutX_6inv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_HeadPtr:array<NODE>, Sta_Dir_HeadVld:array<boolean>, Sta_Dir_HomeHeadPtr:array<boolean>, Sta_Dir_HomeInvSet:array<boolean>, Sta_Dir_HomeShrSet:array<boolean>, Sta_Dir_InvSet:array<boolean>,  Sta_Dir_Local:array<boolean>, Sta_Dir_Pending:array<boolean>, Sta_Dir_ShrSet:array<boolean>,      Sta_Dir_ShrVld:array<boolean>, Sta_HomeProc_CacheState:array<CACHE_STATE>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_UniMsg_Cmd:array<UNI_CMD>,  Sta_UniMsg_HomeProc:array<boolean>,
N0:nat,src:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_HeadPtr.Length==N0
requires Sta_Dir_HeadVld.Length==N0
requires Sta_Dir_HomeHeadPtr.Length==N0
requires Sta_Dir_HomeInvSet.Length==N0
requires Sta_Dir_HomeShrSet.Length==N0
requires Sta_Dir_InvSet.Length==N0

requires Sta_Dir_Local.Length==N0
requires Sta_Dir_Pending.Length==N0
requires Sta_Dir_ShrSet.Length==N0





requires Sta_Dir_ShrVld.Length==N0
requires Sta_HomeProc_CacheState.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_UniMsg_Cmd.Length==N0

requires Sta_UniMsg_HomeProc.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_HeadPtr.Length&&0<=j<Sta_Dir_HeadPtr.Length==>Sta_Dir_HeadPtr[i]!=Sta_Dir_HeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HeadVld.Length&&0<=j<Sta_Dir_HeadVld.Length==>Sta_Dir_HeadVld[i]!=Sta_Dir_HeadVld[j]
requires forall i,j::0<=i<Sta_Dir_HomeHeadPtr.Length&&0<=j<Sta_Dir_HomeHeadPtr.Length==>Sta_Dir_HomeHeadPtr[i]!=Sta_Dir_HomeHeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HomeInvSet.Length&&0<=j<Sta_Dir_HomeInvSet.Length==>Sta_Dir_HomeInvSet[i]!=Sta_Dir_HomeInvSet[j]
requires forall i,j::0<=i<Sta_Dir_HomeShrSet.Length&&0<=j<Sta_Dir_HomeShrSet.Length==>Sta_Dir_HomeShrSet[i]!=Sta_Dir_HomeShrSet[j]
requires forall i,j::0<=i<Sta_Dir_InvSet.Length&&0<=j<Sta_Dir_InvSet.Length==>Sta_Dir_InvSet[i]!=Sta_Dir_InvSet[j]

requires forall i,j::0<=i<Sta_Dir_Local.Length&&0<=j<Sta_Dir_Local.Length==>Sta_Dir_Local[i]!=Sta_Dir_Local[j]
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_Dir_ShrSet.Length&&0<=j<Sta_Dir_ShrSet.Length==>Sta_Dir_ShrSet[i]!=Sta_Dir_ShrSet[j]





requires forall i,j::0<=i<Sta_Dir_ShrVld.Length&&0<=j<Sta_Dir_ShrVld.Length==>Sta_Dir_ShrVld[i]!=Sta_Dir_ShrVld[j]
requires forall i,j::0<=i<Sta_HomeProc_CacheState.Length&&0<=j<Sta_HomeProc_CacheState.Length==>Sta_HomeProc_CacheState[i]!=Sta_HomeProc_CacheState[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_UniMsg_Cmd.Length&&0<=j<Sta_UniMsg_Cmd.Length==>Sta_UniMsg_Cmd[i]!=Sta_UniMsg_Cmd[j]

requires forall i,j::0<=i<Sta_UniMsg_HomeProc.Length&&0<=j<Sta_UniMsg_HomeProc.Length==>Sta_UniMsg_HomeProc[i]!=Sta_UniMsg_HomeProc[j]
requires 0<=src<N0

requires ((Sta_Dir_Dirty[0] == false) && (Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false) && (Sta_Dir_HomeShrSet[0] == false) && (Sta_Dir_Local[0] == false) && (Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (forall p  |0<= p<N0 :: ((Sta_Dir_ShrSet[p] == false) || (p == src)) )) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeProc_CacheState
modifies Sta_UniMsg_Cmd

{
  Sta_Dir_Local[0] := false;
  Sta_Dir_Dirty[0] := true;
  Sta_Dir_HeadVld[0] := true;
  Sta_Dir_HeadPtr[0] := src;
  Sta_Dir_HomeHeadPtr[0] := false;
  Sta_Dir_ShrVld[0] := false;
  var p:=0;
  while(p<N0)
    decreases N0-p
 {
    Sta_Dir_ShrSet[p] := false;
    Sta_Dir_InvSet[p] := false;
  
 p:=p+1;
}
  Sta_Dir_HomeShrSet[0] := false;
  Sta_Dir_HomeInvSet[0] := false;
  Sta_UniMsg_Cmd[src] := UNI_PutX;
  Sta_HomeProc_CacheState[0] := CACHE_I;
}



method n_PI_Local_Get_Putinv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_Local:array<boolean>, Sta_Dir_Pending:array<boolean>, Sta_HomeProc_CacheState:array<CACHE_STATE>, Sta_HomeProc_InvMarked:array<boolean>, Sta_HomeProc_ProcCmd:array<NODE_CMD>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>,
N0:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0
requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_Local.Length==N0
requires Sta_Dir_Pending.Length==N0
requires Sta_HomeProc_CacheState.Length==N0
requires Sta_HomeProc_InvMarked.Length==N0
requires Sta_HomeProc_ProcCmd.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_Local.Length&&0<=j<Sta_Dir_Local.Length==>Sta_Dir_Local[i]!=Sta_Dir_Local[j]
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_HomeProc_CacheState.Length&&0<=j<Sta_HomeProc_CacheState.Length==>Sta_HomeProc_CacheState[i]!=Sta_HomeProc_CacheState[j]
requires forall i,j::0<=i<Sta_HomeProc_InvMarked.Length&&0<=j<Sta_HomeProc_InvMarked.Length==>Sta_HomeProc_InvMarked[i]!=Sta_HomeProc_InvMarked[j]
requires forall i,j::0<=i<Sta_HomeProc_ProcCmd.Length&&0<=j<Sta_HomeProc_ProcCmd.Length==>Sta_HomeProc_ProcCmd[i]!=Sta_HomeProc_ProcCmd[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
//guard condition
requires   ((Sta_Dir_Dirty[0] == false) && (Sta_Dir_Pending[0] == false) && (Sta_HomeProc_CacheState[0] == CACHE_I) && (Sta_HomeProc_ProcCmd[0] == NODE_None))
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_Local
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
{
  Sta_Dir_Local[0] := true;
  Sta_HomeProc_ProcCmd[0] := NODE_None;
  if (Sta_HomeProc_InvMarked[0] == true) {
    Sta_HomeProc_InvMarked[0] := false;
    Sta_HomeProc_CacheState[0] := CACHE_I;}
else{
    Sta_HomeProc_CacheState[0] := CACHE_S;
  }
}


method n_NI_ShWbinv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_HomeInvSet:array<boolean>, Sta_Dir_HomeShrSet:array<boolean>, Sta_Dir_InvSet:array<boolean>,  Sta_Dir_Pending:array<boolean>, Sta_Dir_ShrSet:array<boolean>, Sta_Dir_ShrVld:array<boolean>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_ShWbMsg_Cmd:array<SHWB_CMD>, Sta_ShWbMsg_HomeProc:array<boolean>, Sta_ShWbMsg_Proc:array<NODE>,
N0:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0
requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_HomeInvSet.Length==N0
requires Sta_Dir_HomeShrSet.Length==N0
requires Sta_Dir_InvSet.Length==N0

requires Sta_Dir_Pending.Length==N0
requires Sta_Dir_ShrSet.Length==N0
requires Sta_Dir_ShrVld.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_ShWbMsg_Cmd.Length==N0
requires Sta_ShWbMsg_HomeProc.Length==N0
requires Sta_ShWbMsg_Proc.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_HomeInvSet.Length&&0<=j<Sta_Dir_HomeInvSet.Length==>Sta_Dir_HomeInvSet[i]!=Sta_Dir_HomeInvSet[j]
requires forall i,j::0<=i<Sta_Dir_HomeShrSet.Length&&0<=j<Sta_Dir_HomeShrSet.Length==>Sta_Dir_HomeShrSet[i]!=Sta_Dir_HomeShrSet[j]
requires forall i,j::0<=i<Sta_Dir_InvSet.Length&&0<=j<Sta_Dir_InvSet.Length==>Sta_Dir_InvSet[i]!=Sta_Dir_InvSet[j]

requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_Dir_ShrSet.Length&&0<=j<Sta_Dir_ShrSet.Length==>Sta_Dir_ShrSet[i]!=Sta_Dir_ShrSet[j]
requires forall i,j::0<=i<Sta_Dir_ShrVld.Length&&0<=j<Sta_Dir_ShrVld.Length==>Sta_Dir_ShrVld[i]!=Sta_Dir_ShrVld[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_ShWbMsg_Cmd.Length&&0<=j<Sta_ShWbMsg_Cmd.Length==>Sta_ShWbMsg_Cmd[i]!=Sta_ShWbMsg_Cmd[j]
requires forall i,j::0<=i<Sta_ShWbMsg_HomeProc.Length&&0<=j<Sta_ShWbMsg_HomeProc.Length==>Sta_ShWbMsg_HomeProc[i]!=Sta_ShWbMsg_HomeProc[j]
requires forall i,j::0<=i<Sta_ShWbMsg_Proc.Length&&0<=j<Sta_ShWbMsg_Proc.Length==>Sta_ShWbMsg_Proc[i]!=Sta_ShWbMsg_Proc[j]
//guard condition
requires   (Sta_ShWbMsg_Cmd[0] == SHWB_ShWb)
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_ShWbMsg_Cmd
modifies Sta_ShWbMsg_HomeProc
modifies Sta_ShWbMsg_Proc
{
  Sta_ShWbMsg_Cmd[0] := SHWB_None;
  Sta_Dir_Pending[0] := false;
  Sta_Dir_Dirty[0] := false;
  Sta_Dir_ShrVld[0] := true;
  var p:=0;
  while(p<N0)
    decreases N0-p
 {
    if (((p == Sta_ShWbMsg_Proc[0]) && (Sta_ShWbMsg_HomeProc[0] == false)) || (Sta_Dir_ShrSet[p] == true)) {
      Sta_Dir_ShrSet[p] := true;
      Sta_Dir_InvSet[p] := true;}
else{
      Sta_Dir_ShrSet[p] := false;
      Sta_Dir_InvSet[p] := false;
    }
  
 p:=p+1;
}
  if ((Sta_ShWbMsg_HomeProc[0] == true) || (Sta_Dir_HomeShrSet[0] == true)) {
    Sta_Dir_HomeShrSet[0] := true;
    Sta_Dir_HomeInvSet[0] := true;}
else{
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
  }
}


method n_PI_Local_GetX_PutX_HeadVld__part__0inv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_HeadPtr:array<NODE>, Sta_Dir_HeadVld:array<boolean>, Sta_Dir_HomeHeadPtr:array<boolean>, Sta_Dir_HomeInvSet:array<boolean>, Sta_Dir_HomeShrSet:array<boolean>, Sta_Dir_InvSet:array<boolean>,  Sta_Dir_Local:array<boolean>, Sta_Dir_Pending:array<boolean>, Sta_Dir_ShrSet:array<boolean>, Sta_Dir_ShrVld:array<boolean>, Sta_HomeInvMsg_Cmd:array<INV_CMD>, Sta_HomeProc_CacheState:array<CACHE_STATE>, Sta_HomeProc_InvMarked:array<boolean>, Sta_HomeProc_ProcCmd:array<NODE_CMD>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_InvMsg_Cmd:array<INV_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>,
N0:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0
requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_HeadPtr.Length==N0
requires Sta_Dir_HeadVld.Length==N0
requires Sta_Dir_HomeHeadPtr.Length==N0
requires Sta_Dir_HomeInvSet.Length==N0
requires Sta_Dir_HomeShrSet.Length==N0
requires Sta_Dir_InvSet.Length==N0

requires Sta_Dir_Local.Length==N0
requires Sta_Dir_Pending.Length==N0
requires Sta_Dir_ShrSet.Length==N0
requires Sta_Dir_ShrVld.Length==N0
requires Sta_HomeInvMsg_Cmd.Length==N0
requires Sta_HomeProc_CacheState.Length==N0
requires Sta_HomeProc_InvMarked.Length==N0
requires Sta_HomeProc_ProcCmd.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_InvMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_HeadPtr.Length&&0<=j<Sta_Dir_HeadPtr.Length==>Sta_Dir_HeadPtr[i]!=Sta_Dir_HeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HeadVld.Length&&0<=j<Sta_Dir_HeadVld.Length==>Sta_Dir_HeadVld[i]!=Sta_Dir_HeadVld[j]
requires forall i,j::0<=i<Sta_Dir_HomeHeadPtr.Length&&0<=j<Sta_Dir_HomeHeadPtr.Length==>Sta_Dir_HomeHeadPtr[i]!=Sta_Dir_HomeHeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HomeInvSet.Length&&0<=j<Sta_Dir_HomeInvSet.Length==>Sta_Dir_HomeInvSet[i]!=Sta_Dir_HomeInvSet[j]
requires forall i,j::0<=i<Sta_Dir_HomeShrSet.Length&&0<=j<Sta_Dir_HomeShrSet.Length==>Sta_Dir_HomeShrSet[i]!=Sta_Dir_HomeShrSet[j]
requires forall i,j::0<=i<Sta_Dir_InvSet.Length&&0<=j<Sta_Dir_InvSet.Length==>Sta_Dir_InvSet[i]!=Sta_Dir_InvSet[j]

requires forall i,j::0<=i<Sta_Dir_Local.Length&&0<=j<Sta_Dir_Local.Length==>Sta_Dir_Local[i]!=Sta_Dir_Local[j]
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_Dir_ShrSet.Length&&0<=j<Sta_Dir_ShrSet.Length==>Sta_Dir_ShrSet[i]!=Sta_Dir_ShrSet[j]
requires forall i,j::0<=i<Sta_Dir_ShrVld.Length&&0<=j<Sta_Dir_ShrVld.Length==>Sta_Dir_ShrVld[i]!=Sta_Dir_ShrVld[j]
requires forall i,j::0<=i<Sta_HomeInvMsg_Cmd.Length&&0<=j<Sta_HomeInvMsg_Cmd.Length==>Sta_HomeInvMsg_Cmd[i]!=Sta_HomeInvMsg_Cmd[j]
requires forall i,j::0<=i<Sta_HomeProc_CacheState.Length&&0<=j<Sta_HomeProc_CacheState.Length==>Sta_HomeProc_CacheState[i]!=Sta_HomeProc_CacheState[j]
requires forall i,j::0<=i<Sta_HomeProc_InvMarked.Length&&0<=j<Sta_HomeProc_InvMarked.Length==>Sta_HomeProc_InvMarked[i]!=Sta_HomeProc_InvMarked[j]
requires forall i,j::0<=i<Sta_HomeProc_ProcCmd.Length&&0<=j<Sta_HomeProc_ProcCmd.Length==>Sta_HomeProc_ProcCmd[i]!=Sta_HomeProc_ProcCmd[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_InvMsg_Cmd.Length&&0<=j<Sta_InvMsg_Cmd.Length==>Sta_InvMsg_Cmd[i]!=Sta_InvMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
//guard condition
requires   ((Sta_Dir_Dirty[0] == false) && (Sta_Dir_HeadVld[0] == true) && (Sta_Dir_Pending[0] == false) && (Sta_HomeProc_ProcCmd[0] == NODE_None) && (Sta_HomeProc_CacheState[0] == CACHE_I))
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
{
  Sta_Dir_Local[0] := true;
  Sta_Dir_Dirty[0] := true;
  Sta_Dir_Pending[0] := true;
  Sta_Dir_HeadVld[0] := false;
  Sta_Dir_ShrVld[0] := false;
  var p:=0;
  while(p<N0)
    decreases N0-p
 {
    Sta_Dir_ShrSet[p] := false;
    if (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || ((Sta_Dir_HeadPtr[0] == p) && (Sta_Dir_HomeHeadPtr[0] == false))) {
      Sta_Dir_InvSet[p] := true;
      Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
      Sta_Dir_InvSet[p] := false;
      Sta_InvMsg_Cmd[p] := INV_None;
    }
  
 p:=p+1;
}
  Sta_Dir_HomeShrSet[0] := false;
  Sta_Dir_HomeInvSet[0] := false;
  Sta_HomeInvMsg_Cmd[0] := INV_None;
  Sta_HomeProc_ProcCmd[0] := NODE_None;
  Sta_HomeProc_InvMarked[0] := false;
  Sta_HomeProc_CacheState[0] := CACHE_E;
}

method n_NI_Local_GetX_PutX_11inv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_HeadPtr:array<NODE>, Sta_Dir_HeadVld:array<boolean>, Sta_Dir_HomeHeadPtr:array<boolean>, Sta_Dir_HomeInvSet:array<boolean>, Sta_Dir_HomeShrSet:array<boolean>, Sta_Dir_InvSet:array<boolean>,  Sta_Dir_Local:array<boolean>, Sta_Dir_Pending:array<boolean>, Sta_Dir_ShrSet:array<boolean>, Sta_Dir_ShrVld:array<boolean>, Sta_HomeProc_CacheState:array<CACHE_STATE>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_UniMsg_Cmd:array<UNI_CMD>,  Sta_UniMsg_HomeProc:array<boolean>,
N0:nat,src:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_HeadPtr.Length==N0
requires Sta_Dir_HeadVld.Length==N0
requires Sta_Dir_HomeHeadPtr.Length==N0
requires Sta_Dir_HomeInvSet.Length==N0
requires Sta_Dir_HomeShrSet.Length==N0
requires Sta_Dir_InvSet.Length==N0

requires Sta_Dir_Local.Length==N0
requires Sta_Dir_Pending.Length==N0
requires Sta_Dir_ShrSet.Length==N0
requires Sta_Dir_ShrVld.Length==N0
requires Sta_HomeProc_CacheState.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_UniMsg_Cmd.Length==N0

requires Sta_UniMsg_HomeProc.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_HeadPtr.Length&&0<=j<Sta_Dir_HeadPtr.Length==>Sta_Dir_HeadPtr[i]!=Sta_Dir_HeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HeadVld.Length&&0<=j<Sta_Dir_HeadVld.Length==>Sta_Dir_HeadVld[i]!=Sta_Dir_HeadVld[j]
requires forall i,j::0<=i<Sta_Dir_HomeHeadPtr.Length&&0<=j<Sta_Dir_HomeHeadPtr.Length==>Sta_Dir_HomeHeadPtr[i]!=Sta_Dir_HomeHeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HomeInvSet.Length&&0<=j<Sta_Dir_HomeInvSet.Length==>Sta_Dir_HomeInvSet[i]!=Sta_Dir_HomeInvSet[j]
requires forall i,j::0<=i<Sta_Dir_HomeShrSet.Length&&0<=j<Sta_Dir_HomeShrSet.Length==>Sta_Dir_HomeShrSet[i]!=Sta_Dir_HomeShrSet[j]
requires forall i,j::0<=i<Sta_Dir_InvSet.Length&&0<=j<Sta_Dir_InvSet.Length==>Sta_Dir_InvSet[i]!=Sta_Dir_InvSet[j]

requires forall i,j::0<=i<Sta_Dir_Local.Length&&0<=j<Sta_Dir_Local.Length==>Sta_Dir_Local[i]!=Sta_Dir_Local[j]
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_Dir_ShrSet.Length&&0<=j<Sta_Dir_ShrSet.Length==>Sta_Dir_ShrSet[i]!=Sta_Dir_ShrSet[j]
requires forall i,j::0<=i<Sta_Dir_ShrVld.Length&&0<=j<Sta_Dir_ShrVld.Length==>Sta_Dir_ShrVld[i]!=Sta_Dir_ShrVld[j]
requires forall i,j::0<=i<Sta_HomeProc_CacheState.Length&&0<=j<Sta_HomeProc_CacheState.Length==>Sta_HomeProc_CacheState[i]!=Sta_HomeProc_CacheState[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_UniMsg_Cmd.Length&&0<=j<Sta_UniMsg_Cmd.Length==>Sta_UniMsg_Cmd[i]!=Sta_UniMsg_Cmd[j]

requires forall i,j::0<=i<Sta_UniMsg_HomeProc.Length&&0<=j<Sta_UniMsg_HomeProc.Length==>Sta_UniMsg_HomeProc[i]!=Sta_UniMsg_HomeProc[j]
requires 0<=src<N0

requires ((Sta_Dir_Dirty[0] == true) && (Sta_Dir_Local[0] == true) && (Sta_Dir_Pending[0] == false) && (Sta_HomeProc_CacheState[0] == CACHE_E) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true)) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeProc_CacheState
modifies Sta_UniMsg_Cmd

{
  Sta_Dir_Local[0] := false;
  Sta_Dir_Dirty[0] := true;
  Sta_Dir_HeadVld[0] := true;
  Sta_Dir_HeadPtr[0] := src;
  Sta_Dir_HomeHeadPtr[0] := false;
  Sta_Dir_ShrVld[0] := false;
  var p:=0;
  while(p<N0)
    decreases N0-p
 {
    Sta_Dir_ShrSet[p] := false;
    Sta_Dir_InvSet[p] := false;
  
 p:=p+1;
}
  Sta_Dir_HomeShrSet[0] := false;
  Sta_Dir_HomeInvSet[0] := false;
  Sta_UniMsg_Cmd[src] := UNI_PutX;
  Sta_HomeProc_CacheState[0] := CACHE_I;
}


method n_NI_Replaceinv__90_0(Sta_Dir_InvSet:array<boolean>,   Sta_Dir_ShrSet:array<boolean>, Sta_Dir_ShrVld:array<boolean>,  Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_RpMsg_Cmd:array<RP_CMD>,
N0:nat,src:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_Dir_InvSet.Length==N0


requires Sta_Dir_ShrSet.Length==N0
requires Sta_Dir_ShrVld.Length==N0

requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_RpMsg_Cmd.Length==N0
requires forall i,j::0<=i<Sta_Dir_InvSet.Length&&0<=j<Sta_Dir_InvSet.Length==>Sta_Dir_InvSet[i]!=Sta_Dir_InvSet[j]


requires forall i,j::0<=i<Sta_Dir_ShrSet.Length&&0<=j<Sta_Dir_ShrSet.Length==>Sta_Dir_ShrSet[i]!=Sta_Dir_ShrSet[j]
requires forall i,j::0<=i<Sta_Dir_ShrVld.Length&&0<=j<Sta_Dir_ShrVld.Length==>Sta_Dir_ShrVld[i]!=Sta_Dir_ShrVld[j]

requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_RpMsg_Cmd.Length&&0<=j<Sta_RpMsg_Cmd.Length==>Sta_RpMsg_Cmd[i]!=Sta_RpMsg_Cmd[j]
requires 0<=src<N0

requires (Sta_RpMsg_Cmd[src] == RP_Replace) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_InvSet
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_RpMsg_Cmd

{
  Sta_RpMsg_Cmd[src] := RP_None;
  if (Sta_Dir_ShrVld[0] == true) {
    Sta_Dir_ShrSet[src] := false;
    Sta_Dir_InvSet[src] := false;
  }
}


method n_NI_Local_GetX_PutX_1inv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_HeadPtr:array<NODE>, Sta_Dir_HeadVld:array<boolean>, Sta_Dir_HomeHeadPtr:array<boolean>, Sta_Dir_HomeInvSet:array<boolean>, Sta_Dir_HomeShrSet:array<boolean>, Sta_Dir_InvSet:array<boolean>,  Sta_Dir_Local:array<boolean>, Sta_Dir_Pending:array<boolean>, Sta_Dir_ShrSet:array<boolean>, Sta_Dir_ShrVld:array<boolean>, Sta_HomeProc_CacheState:array<CACHE_STATE>, Sta_HomeProc_InvMarked:array<boolean>, Sta_HomeProc_ProcCmd:array<NODE_CMD>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_UniMsg_Cmd:array<UNI_CMD>,  Sta_UniMsg_HomeProc:array<boolean>,
N0:nat,src:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_HeadPtr.Length==N0
requires Sta_Dir_HeadVld.Length==N0
requires Sta_Dir_HomeHeadPtr.Length==N0
requires Sta_Dir_HomeInvSet.Length==N0
requires Sta_Dir_HomeShrSet.Length==N0
requires Sta_Dir_InvSet.Length==N0

requires Sta_Dir_Local.Length==N0
requires Sta_Dir_Pending.Length==N0
requires Sta_Dir_ShrSet.Length==N0
requires Sta_Dir_ShrVld.Length==N0
requires Sta_HomeProc_CacheState.Length==N0
requires Sta_HomeProc_InvMarked.Length==N0
requires Sta_HomeProc_ProcCmd.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_UniMsg_Cmd.Length==N0

requires Sta_UniMsg_HomeProc.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_HeadPtr.Length&&0<=j<Sta_Dir_HeadPtr.Length==>Sta_Dir_HeadPtr[i]!=Sta_Dir_HeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HeadVld.Length&&0<=j<Sta_Dir_HeadVld.Length==>Sta_Dir_HeadVld[i]!=Sta_Dir_HeadVld[j]
requires forall i,j::0<=i<Sta_Dir_HomeHeadPtr.Length&&0<=j<Sta_Dir_HomeHeadPtr.Length==>Sta_Dir_HomeHeadPtr[i]!=Sta_Dir_HomeHeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HomeInvSet.Length&&0<=j<Sta_Dir_HomeInvSet.Length==>Sta_Dir_HomeInvSet[i]!=Sta_Dir_HomeInvSet[j]
requires forall i,j::0<=i<Sta_Dir_HomeShrSet.Length&&0<=j<Sta_Dir_HomeShrSet.Length==>Sta_Dir_HomeShrSet[i]!=Sta_Dir_HomeShrSet[j]
requires forall i,j::0<=i<Sta_Dir_InvSet.Length&&0<=j<Sta_Dir_InvSet.Length==>Sta_Dir_InvSet[i]!=Sta_Dir_InvSet[j]

requires forall i,j::0<=i<Sta_Dir_Local.Length&&0<=j<Sta_Dir_Local.Length==>Sta_Dir_Local[i]!=Sta_Dir_Local[j]
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_Dir_ShrSet.Length&&0<=j<Sta_Dir_ShrSet.Length==>Sta_Dir_ShrSet[i]!=Sta_Dir_ShrSet[j]
requires forall i,j::0<=i<Sta_Dir_ShrVld.Length&&0<=j<Sta_Dir_ShrVld.Length==>Sta_Dir_ShrVld[i]!=Sta_Dir_ShrVld[j]
requires forall i,j::0<=i<Sta_HomeProc_CacheState.Length&&0<=j<Sta_HomeProc_CacheState.Length==>Sta_HomeProc_CacheState[i]!=Sta_HomeProc_CacheState[j]
requires forall i,j::0<=i<Sta_HomeProc_InvMarked.Length&&0<=j<Sta_HomeProc_InvMarked.Length==>Sta_HomeProc_InvMarked[i]!=Sta_HomeProc_InvMarked[j]
requires forall i,j::0<=i<Sta_HomeProc_ProcCmd.Length&&0<=j<Sta_HomeProc_ProcCmd.Length==>Sta_HomeProc_ProcCmd[i]!=Sta_HomeProc_ProcCmd[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_UniMsg_Cmd.Length&&0<=j<Sta_UniMsg_Cmd.Length==>Sta_UniMsg_Cmd[i]!=Sta_UniMsg_Cmd[j]

requires forall i,j::0<=i<Sta_UniMsg_HomeProc.Length&&0<=j<Sta_UniMsg_HomeProc.Length==>Sta_UniMsg_HomeProc[i]!=Sta_UniMsg_HomeProc[j]
requires 0<=src<N0

requires ((Sta_Dir_Dirty[0] == false) && (Sta_Dir_HeadVld[0] == false) && (Sta_Dir_Local[0] == true) && (Sta_Dir_Pending[0] == false) && (Sta_HomeProc_ProcCmd[0] == NODE_Get) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true)) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_UniMsg_Cmd

{
  Sta_Dir_Local[0] := false;
  Sta_Dir_Dirty[0] := true;
  Sta_Dir_HeadVld[0] := true;
  Sta_Dir_HeadPtr[0] := src;
  Sta_Dir_HomeHeadPtr[0] := false;
  Sta_Dir_ShrVld[0] := false;
  var p:=0;
  while(p<N0)
    decreases N0-p
 {
    Sta_Dir_ShrSet[p] := false;
    Sta_Dir_InvSet[p] := false;
  
 p:=p+1;
}
  Sta_Dir_HomeShrSet[0] := false;
  Sta_Dir_HomeInvSet[0] := false;
  Sta_UniMsg_Cmd[src] := UNI_PutX;
  Sta_HomeProc_CacheState[0] := CACHE_I;
  Sta_HomeProc_InvMarked[0] := true;
}


method n_NI_Local_GetX_PutX_8_Homeinv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_HeadPtr:array<NODE>, Sta_Dir_HeadVld:array<boolean>, Sta_Dir_HomeHeadPtr:array<boolean>, Sta_Dir_HomeInvSet:array<boolean>, Sta_Dir_HomeShrSet:array<boolean>, Sta_Dir_InvSet:array<boolean>,  Sta_Dir_Local:array<boolean>, Sta_Dir_Pending:array<boolean>, Sta_Dir_ShrSet:array<boolean>, Sta_Dir_ShrVld:array<boolean>, Sta_HomeInvMsg_Cmd:array<INV_CMD>, Sta_HomeProc_CacheState:array<CACHE_STATE>, Sta_HomeProc_ProcCmd:array<NODE_CMD>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_InvMsg_Cmd:array<INV_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_UniMsg_Cmd:array<UNI_CMD>,  Sta_UniMsg_HomeProc:array<boolean>,
N0:nat,src:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_HeadPtr.Length==N0
requires Sta_Dir_HeadVld.Length==N0
requires Sta_Dir_HomeHeadPtr.Length==N0
requires Sta_Dir_HomeInvSet.Length==N0
requires Sta_Dir_HomeShrSet.Length==N0
requires Sta_Dir_InvSet.Length==N0

requires Sta_Dir_Local.Length==N0
requires Sta_Dir_Pending.Length==N0
requires Sta_Dir_ShrSet.Length==N0
requires Sta_Dir_ShrVld.Length==N0
requires Sta_HomeInvMsg_Cmd.Length==N0
requires Sta_HomeProc_CacheState.Length==N0
requires Sta_HomeProc_ProcCmd.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_InvMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_UniMsg_Cmd.Length==N0

requires Sta_UniMsg_HomeProc.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_HeadPtr.Length&&0<=j<Sta_Dir_HeadPtr.Length==>Sta_Dir_HeadPtr[i]!=Sta_Dir_HeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HeadVld.Length&&0<=j<Sta_Dir_HeadVld.Length==>Sta_Dir_HeadVld[i]!=Sta_Dir_HeadVld[j]
requires forall i,j::0<=i<Sta_Dir_HomeHeadPtr.Length&&0<=j<Sta_Dir_HomeHeadPtr.Length==>Sta_Dir_HomeHeadPtr[i]!=Sta_Dir_HomeHeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HomeInvSet.Length&&0<=j<Sta_Dir_HomeInvSet.Length==>Sta_Dir_HomeInvSet[i]!=Sta_Dir_HomeInvSet[j]
requires forall i,j::0<=i<Sta_Dir_HomeShrSet.Length&&0<=j<Sta_Dir_HomeShrSet.Length==>Sta_Dir_HomeShrSet[i]!=Sta_Dir_HomeShrSet[j]
requires forall i,j::0<=i<Sta_Dir_InvSet.Length&&0<=j<Sta_Dir_InvSet.Length==>Sta_Dir_InvSet[i]!=Sta_Dir_InvSet[j]

requires forall i,j::0<=i<Sta_Dir_Local.Length&&0<=j<Sta_Dir_Local.Length==>Sta_Dir_Local[i]!=Sta_Dir_Local[j]
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_Dir_ShrSet.Length&&0<=j<Sta_Dir_ShrSet.Length==>Sta_Dir_ShrSet[i]!=Sta_Dir_ShrSet[j]
requires forall i,j::0<=i<Sta_Dir_ShrVld.Length&&0<=j<Sta_Dir_ShrVld.Length==>Sta_Dir_ShrVld[i]!=Sta_Dir_ShrVld[j]
requires forall i,j::0<=i<Sta_HomeInvMsg_Cmd.Length&&0<=j<Sta_HomeInvMsg_Cmd.Length==>Sta_HomeInvMsg_Cmd[i]!=Sta_HomeInvMsg_Cmd[j]
requires forall i,j::0<=i<Sta_HomeProc_CacheState.Length&&0<=j<Sta_HomeProc_CacheState.Length==>Sta_HomeProc_CacheState[i]!=Sta_HomeProc_CacheState[j]
requires forall i,j::0<=i<Sta_HomeProc_ProcCmd.Length&&0<=j<Sta_HomeProc_ProcCmd.Length==>Sta_HomeProc_ProcCmd[i]!=Sta_HomeProc_ProcCmd[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_InvMsg_Cmd.Length&&0<=j<Sta_InvMsg_Cmd.Length==>Sta_InvMsg_Cmd[i]!=Sta_InvMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_UniMsg_Cmd.Length&&0<=j<Sta_UniMsg_Cmd.Length==>Sta_UniMsg_Cmd[i]!=Sta_UniMsg_Cmd[j]

requires forall i,j::0<=i<Sta_UniMsg_HomeProc.Length&&0<=j<Sta_UniMsg_HomeProc.Length==>Sta_UniMsg_HomeProc[i]!=Sta_UniMsg_HomeProc[j]
requires 0<=src<N0

requires ((Sta_Dir_Dirty[0] == false) && (Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HomeHeadPtr[0] == false) && (Sta_Dir_HomeShrSet[0] == true) && (Sta_Dir_Local[0] == true) && (Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_HomeProc_ProcCmd[0] == NODE_Get))) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd

{
  Sta_Dir_Pending[0] := true;
  Sta_Dir_Local[0] := false;
  Sta_Dir_Dirty[0] := true;
  Sta_Dir_HeadVld[0] := true;
  Sta_Dir_HeadPtr[0] := src;
  Sta_Dir_HomeHeadPtr[0] := false;
  Sta_Dir_ShrVld[0] := false;
  var p:=0;
  while(p<N0)
    decreases N0-p
 {
    Sta_Dir_ShrSet[p] := false;
    if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
      Sta_Dir_InvSet[p] := true;
      Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
      Sta_Dir_InvSet[p] := false;
      Sta_InvMsg_Cmd[p] := INV_None;
    }
  
 p:=p+1;
}
  Sta_Dir_HomeShrSet[0] := false;
  Sta_Dir_HomeInvSet[0] := false;
  Sta_HomeInvMsg_Cmd[0] := INV_None;
  Sta_UniMsg_Cmd[src] := UNI_PutX;
  Sta_HomeProc_CacheState[0] := CACHE_I;
}


method n_NI_Local_GetX_PutX_7__part__0inv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_HeadPtr:array<NODE>, Sta_Dir_HeadVld:array<boolean>, Sta_Dir_HomeHeadPtr:array<boolean>, Sta_Dir_HomeInvSet:array<boolean>, Sta_Dir_HomeShrSet:array<boolean>, Sta_Dir_InvSet:array<boolean>,  Sta_Dir_Local:array<boolean>, Sta_Dir_Pending:array<boolean>, Sta_Dir_ShrSet:array<boolean>, Sta_Dir_ShrVld:array<boolean>, Sta_HomeInvMsg_Cmd:array<INV_CMD>, Sta_HomeProc_CacheState:array<CACHE_STATE>, Sta_HomeProc_ProcCmd:array<NODE_CMD>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_InvMsg_Cmd:array<INV_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_UniMsg_Cmd:array<UNI_CMD>,  Sta_UniMsg_HomeProc:array<boolean>,
N0:nat,src:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_HeadPtr.Length==N0
requires Sta_Dir_HeadVld.Length==N0
requires Sta_Dir_HomeHeadPtr.Length==N0
requires Sta_Dir_HomeInvSet.Length==N0
requires Sta_Dir_HomeShrSet.Length==N0
requires Sta_Dir_InvSet.Length==N0

requires Sta_Dir_Local.Length==N0
requires Sta_Dir_Pending.Length==N0
requires Sta_Dir_ShrSet.Length==N0
requires Sta_Dir_ShrVld.Length==N0
requires Sta_HomeInvMsg_Cmd.Length==N0
requires Sta_HomeProc_CacheState.Length==N0
requires Sta_HomeProc_ProcCmd.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_InvMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_UniMsg_Cmd.Length==N0

requires Sta_UniMsg_HomeProc.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_HeadPtr.Length&&0<=j<Sta_Dir_HeadPtr.Length==>Sta_Dir_HeadPtr[i]!=Sta_Dir_HeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HeadVld.Length&&0<=j<Sta_Dir_HeadVld.Length==>Sta_Dir_HeadVld[i]!=Sta_Dir_HeadVld[j]
requires forall i,j::0<=i<Sta_Dir_HomeHeadPtr.Length&&0<=j<Sta_Dir_HomeHeadPtr.Length==>Sta_Dir_HomeHeadPtr[i]!=Sta_Dir_HomeHeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HomeInvSet.Length&&0<=j<Sta_Dir_HomeInvSet.Length==>Sta_Dir_HomeInvSet[i]!=Sta_Dir_HomeInvSet[j]
requires forall i,j::0<=i<Sta_Dir_HomeShrSet.Length&&0<=j<Sta_Dir_HomeShrSet.Length==>Sta_Dir_HomeShrSet[i]!=Sta_Dir_HomeShrSet[j]
requires forall i,j::0<=i<Sta_Dir_InvSet.Length&&0<=j<Sta_Dir_InvSet.Length==>Sta_Dir_InvSet[i]!=Sta_Dir_InvSet[j]

requires forall i,j::0<=i<Sta_Dir_Local.Length&&0<=j<Sta_Dir_Local.Length==>Sta_Dir_Local[i]!=Sta_Dir_Local[j]
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_Dir_ShrSet.Length&&0<=j<Sta_Dir_ShrSet.Length==>Sta_Dir_ShrSet[i]!=Sta_Dir_ShrSet[j]
requires forall i,j::0<=i<Sta_Dir_ShrVld.Length&&0<=j<Sta_Dir_ShrVld.Length==>Sta_Dir_ShrVld[i]!=Sta_Dir_ShrVld[j]
requires forall i,j::0<=i<Sta_HomeInvMsg_Cmd.Length&&0<=j<Sta_HomeInvMsg_Cmd.Length==>Sta_HomeInvMsg_Cmd[i]!=Sta_HomeInvMsg_Cmd[j]
requires forall i,j::0<=i<Sta_HomeProc_CacheState.Length&&0<=j<Sta_HomeProc_CacheState.Length==>Sta_HomeProc_CacheState[i]!=Sta_HomeProc_CacheState[j]
requires forall i,j::0<=i<Sta_HomeProc_ProcCmd.Length&&0<=j<Sta_HomeProc_ProcCmd.Length==>Sta_HomeProc_ProcCmd[i]!=Sta_HomeProc_ProcCmd[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_InvMsg_Cmd.Length&&0<=j<Sta_InvMsg_Cmd.Length==>Sta_InvMsg_Cmd[i]!=Sta_InvMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_UniMsg_Cmd.Length&&0<=j<Sta_UniMsg_Cmd.Length==>Sta_UniMsg_Cmd[i]!=Sta_UniMsg_Cmd[j]

requires forall i,j::0<=i<Sta_UniMsg_HomeProc.Length&&0<=j<Sta_UniMsg_HomeProc.Length==>Sta_UniMsg_HomeProc[i]!=Sta_UniMsg_HomeProc[j]
requires 0<=src<N0

requires ((Sta_Dir_Dirty[0] == false) && (Sta_Dir_HeadVld[0] == true) && (Sta_Dir_Local[0] == true) && (Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_HomeProc_ProcCmd[0] == NODE_Get)) && (Sta_Dir_HomeHeadPtr[0] == true)) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd

{
  Sta_Dir_Pending[0] := true;
  Sta_Dir_Local[0] := false;
  Sta_Dir_Dirty[0] := true;
  Sta_Dir_HeadVld[0] := true;
  Sta_Dir_HeadPtr[0] := src;
  Sta_Dir_HomeHeadPtr[0] := false;
  Sta_Dir_ShrVld[0] := false;
  var p:=0;
  while(p<N0)
    decreases N0-p
 {
    Sta_Dir_ShrSet[p] := false;
    if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
      Sta_Dir_InvSet[p] := true;
      Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
      Sta_Dir_InvSet[p] := false;
      Sta_InvMsg_Cmd[p] := INV_None;
    }
  
 p:=p+1;
}
  Sta_Dir_HomeShrSet[0] := false;
  Sta_Dir_HomeInvSet[0] := false;
  Sta_HomeInvMsg_Cmd[0] := INV_None;
  Sta_UniMsg_Cmd[src] := UNI_PutX;
  Sta_HomeProc_CacheState[0] := CACHE_I;
}


method n_NI_Nakinv__90_0(Sta_HomeUniMsg_Cmd:array<UNI_CMD>,   Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_Proc_InvMarked:array<boolean>,  Sta_Proc_ProcCmd:array<NODE_CMD>, Sta_UniMsg_Cmd:array<UNI_CMD>,
N0:nat,dst:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_HomeUniMsg_Cmd.Length==N0


requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_Proc_InvMarked.Length==N0

requires Sta_Proc_ProcCmd.Length==N0
requires Sta_UniMsg_Cmd.Length==N0
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]


requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_Proc_InvMarked.Length&&0<=j<Sta_Proc_InvMarked.Length==>Sta_Proc_InvMarked[i]!=Sta_Proc_InvMarked[j]

requires forall i,j::0<=i<Sta_Proc_ProcCmd.Length&&0<=j<Sta_Proc_ProcCmd.Length==>Sta_Proc_ProcCmd[i]!=Sta_Proc_ProcCmd[j]
requires forall i,j::0<=i<Sta_UniMsg_Cmd.Length&&0<=j<Sta_UniMsg_Cmd.Length==>Sta_UniMsg_Cmd[i]!=Sta_UniMsg_Cmd[j]
requires 0<=dst<N0

requires (Sta_UniMsg_Cmd[dst] == UNI_Nak) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Proc_InvMarked
modifies Sta_Proc_ProcCmd
modifies Sta_UniMsg_Cmd

{
  Sta_UniMsg_Cmd[dst] := UNI_None;
  Sta_Proc_ProcCmd[dst] := NODE_None;
  Sta_Proc_InvMarked[dst] := false;
}


method n_NI_Local_GetX_PutX_9__part__1inv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_HeadPtr:array<NODE>, Sta_Dir_HeadVld:array<boolean>, Sta_Dir_HomeHeadPtr:array<boolean>, Sta_Dir_HomeInvSet:array<boolean>, Sta_Dir_HomeShrSet:array<boolean>, Sta_Dir_InvSet:array<boolean>,  Sta_Dir_Local:array<boolean>, Sta_Dir_Pending:array<boolean>, Sta_Dir_ShrSet:array<boolean>, Sta_Dir_ShrVld:array<boolean>, Sta_HomeInvMsg_Cmd:array<INV_CMD>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_InvMsg_Cmd:array<INV_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_UniMsg_Cmd:array<UNI_CMD>,  Sta_UniMsg_HomeProc:array<boolean>,
N0:nat,src:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_HeadPtr.Length==N0
requires Sta_Dir_HeadVld.Length==N0
requires Sta_Dir_HomeHeadPtr.Length==N0
requires Sta_Dir_HomeInvSet.Length==N0
requires Sta_Dir_HomeShrSet.Length==N0
requires Sta_Dir_InvSet.Length==N0

requires Sta_Dir_Local.Length==N0
requires Sta_Dir_Pending.Length==N0
requires Sta_Dir_ShrSet.Length==N0
requires Sta_Dir_ShrVld.Length==N0
requires Sta_HomeInvMsg_Cmd.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_InvMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_UniMsg_Cmd.Length==N0

requires Sta_UniMsg_HomeProc.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_HeadPtr.Length&&0<=j<Sta_Dir_HeadPtr.Length==>Sta_Dir_HeadPtr[i]!=Sta_Dir_HeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HeadVld.Length&&0<=j<Sta_Dir_HeadVld.Length==>Sta_Dir_HeadVld[i]!=Sta_Dir_HeadVld[j]
requires forall i,j::0<=i<Sta_Dir_HomeHeadPtr.Length&&0<=j<Sta_Dir_HomeHeadPtr.Length==>Sta_Dir_HomeHeadPtr[i]!=Sta_Dir_HomeHeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HomeInvSet.Length&&0<=j<Sta_Dir_HomeInvSet.Length==>Sta_Dir_HomeInvSet[i]!=Sta_Dir_HomeInvSet[j]
requires forall i,j::0<=i<Sta_Dir_HomeShrSet.Length&&0<=j<Sta_Dir_HomeShrSet.Length==>Sta_Dir_HomeShrSet[i]!=Sta_Dir_HomeShrSet[j]
requires forall i,j::0<=i<Sta_Dir_InvSet.Length&&0<=j<Sta_Dir_InvSet.Length==>Sta_Dir_InvSet[i]!=Sta_Dir_InvSet[j]

requires forall i,j::0<=i<Sta_Dir_Local.Length&&0<=j<Sta_Dir_Local.Length==>Sta_Dir_Local[i]!=Sta_Dir_Local[j]
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_Dir_ShrSet.Length&&0<=j<Sta_Dir_ShrSet.Length==>Sta_Dir_ShrSet[i]!=Sta_Dir_ShrSet[j]
requires forall i,j::0<=i<Sta_Dir_ShrVld.Length&&0<=j<Sta_Dir_ShrVld.Length==>Sta_Dir_ShrVld[i]!=Sta_Dir_ShrVld[j]
requires forall i,j::0<=i<Sta_HomeInvMsg_Cmd.Length&&0<=j<Sta_HomeInvMsg_Cmd.Length==>Sta_HomeInvMsg_Cmd[i]!=Sta_HomeInvMsg_Cmd[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_InvMsg_Cmd.Length&&0<=j<Sta_InvMsg_Cmd.Length==>Sta_InvMsg_Cmd[i]!=Sta_InvMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_UniMsg_Cmd.Length&&0<=j<Sta_UniMsg_Cmd.Length==>Sta_UniMsg_Cmd[i]!=Sta_UniMsg_Cmd[j]

requires forall i,j::0<=i<Sta_UniMsg_HomeProc.Length&&0<=j<Sta_UniMsg_HomeProc.Length==>Sta_UniMsg_HomeProc[i]!=Sta_UniMsg_HomeProc[j]
requires 0<=src<N0

requires ((Sta_Dir_Dirty[0] == false) && (Sta_Dir_HeadVld[0] == true) && (Sta_Dir_Local[0] == false) && (Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_Dir_HeadPtr[0] == src))) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd

{
  Sta_Dir_Pending[0] := true;
  Sta_Dir_Local[0] := false;
  Sta_Dir_Dirty[0] := true;
  Sta_Dir_HeadVld[0] := true;
  Sta_Dir_HeadPtr[0] := src;
  Sta_Dir_HomeHeadPtr[0] := false;
  Sta_Dir_ShrVld[0] := false;
  var p:=0;
  while(p<N0)
    decreases N0-p
 {
    Sta_Dir_ShrSet[p] := false;
    if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
      Sta_Dir_InvSet[p] := true;
      Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
      Sta_Dir_InvSet[p] := false;
      Sta_InvMsg_Cmd[p] := INV_None;
    }
  
 p:=p+1;
}
  Sta_Dir_HomeShrSet[0] := false;
  Sta_Dir_HomeInvSet[0] := false;
  Sta_HomeInvMsg_Cmd[0] := INV_None;
  Sta_UniMsg_Cmd[src] := UNI_PutX;
}


method n_PI_Remote_GetXinv__90_0(Sta_HomeUniMsg_Cmd:array<UNI_CMD>,   Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_Proc_CacheState:array<CACHE_STATE>,  Sta_Proc_ProcCmd:array<NODE_CMD>, Sta_UniMsg_Cmd:array<UNI_CMD>, Sta_UniMsg_HomeProc:array<boolean>,
N0:nat,src:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_HomeUniMsg_Cmd.Length==N0


requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_Proc_CacheState.Length==N0

requires Sta_Proc_ProcCmd.Length==N0
requires Sta_UniMsg_Cmd.Length==N0
requires Sta_UniMsg_HomeProc.Length==N0
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]


requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_Proc_CacheState.Length&&0<=j<Sta_Proc_CacheState.Length==>Sta_Proc_CacheState[i]!=Sta_Proc_CacheState[j]

requires forall i,j::0<=i<Sta_Proc_ProcCmd.Length&&0<=j<Sta_Proc_ProcCmd.Length==>Sta_Proc_ProcCmd[i]!=Sta_Proc_ProcCmd[j]
requires forall i,j::0<=i<Sta_UniMsg_Cmd.Length&&0<=j<Sta_UniMsg_Cmd.Length==>Sta_UniMsg_Cmd[i]!=Sta_UniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_UniMsg_HomeProc.Length&&0<=j<Sta_UniMsg_HomeProc.Length==>Sta_UniMsg_HomeProc[i]!=Sta_UniMsg_HomeProc[j]
requires 0<=src<N0

requires ((Sta_Proc_CacheState[src] == CACHE_I) && (Sta_Proc_ProcCmd[src] == NODE_None)) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Proc_ProcCmd
modifies Sta_UniMsg_Cmd
modifies Sta_UniMsg_HomeProc

{
  Sta_Proc_ProcCmd[src] := NODE_GetX;
  Sta_UniMsg_Cmd[src] := UNI_GetX;
  Sta_UniMsg_HomeProc[src] := true;
}



method n_PI_Local_GetX_PutX__part__1inv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_HeadVld:array<boolean>, Sta_Dir_Local:array<boolean>, Sta_Dir_Pending:array<boolean>, Sta_HomeProc_CacheState:array<CACHE_STATE>, Sta_HomeProc_InvMarked:array<boolean>, Sta_HomeProc_ProcCmd:array<NODE_CMD>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>,
N0:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0
requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_HeadVld.Length==N0
requires Sta_Dir_Local.Length==N0
requires Sta_Dir_Pending.Length==N0
requires Sta_HomeProc_CacheState.Length==N0
requires Sta_HomeProc_InvMarked.Length==N0
requires Sta_HomeProc_ProcCmd.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_HeadVld.Length&&0<=j<Sta_Dir_HeadVld.Length==>Sta_Dir_HeadVld[i]!=Sta_Dir_HeadVld[j]
requires forall i,j::0<=i<Sta_Dir_Local.Length&&0<=j<Sta_Dir_Local.Length==>Sta_Dir_Local[i]!=Sta_Dir_Local[j]
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_HomeProc_CacheState.Length&&0<=j<Sta_HomeProc_CacheState.Length==>Sta_HomeProc_CacheState[i]!=Sta_HomeProc_CacheState[j]
requires forall i,j::0<=i<Sta_HomeProc_InvMarked.Length&&0<=j<Sta_HomeProc_InvMarked.Length==>Sta_HomeProc_InvMarked[i]!=Sta_HomeProc_InvMarked[j]
requires forall i,j::0<=i<Sta_HomeProc_ProcCmd.Length&&0<=j<Sta_HomeProc_ProcCmd.Length==>Sta_HomeProc_ProcCmd[i]!=Sta_HomeProc_ProcCmd[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
//guard condition
requires   ((Sta_Dir_Dirty[0] == false) && (Sta_Dir_HeadVld[0] == false) && (Sta_Dir_Pending[0] == false) && (Sta_HomeProc_ProcCmd[0] == NODE_None) && (Sta_HomeProc_CacheState[0] == CACHE_S))
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_Local
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
{
  Sta_Dir_Local[0] := true;
  Sta_Dir_Dirty[0] := true;
  Sta_HomeProc_ProcCmd[0] := NODE_None;
  Sta_HomeProc_InvMarked[0] := false;
  Sta_HomeProc_CacheState[0] := CACHE_E;
}

method n_NI_Remote_PutXinv__90_0(Sta_HomeUniMsg_Cmd:array<UNI_CMD>,   Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_Proc_CacheState:array<CACHE_STATE>,  Sta_Proc_InvMarked:array<boolean>, Sta_Proc_ProcCmd:array<NODE_CMD>, Sta_UniMsg_Cmd:array<UNI_CMD>,
N0:nat,dst:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_HomeUniMsg_Cmd.Length==N0


requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_Proc_CacheState.Length==N0

requires Sta_Proc_InvMarked.Length==N0
requires Sta_Proc_ProcCmd.Length==N0
requires Sta_UniMsg_Cmd.Length==N0
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]


requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_Proc_CacheState.Length&&0<=j<Sta_Proc_CacheState.Length==>Sta_Proc_CacheState[i]!=Sta_Proc_CacheState[j]

requires forall i,j::0<=i<Sta_Proc_InvMarked.Length&&0<=j<Sta_Proc_InvMarked.Length==>Sta_Proc_InvMarked[i]!=Sta_Proc_InvMarked[j]
requires forall i,j::0<=i<Sta_Proc_ProcCmd.Length&&0<=j<Sta_Proc_ProcCmd.Length==>Sta_Proc_ProcCmd[i]!=Sta_Proc_ProcCmd[j]
requires forall i,j::0<=i<Sta_UniMsg_Cmd.Length&&0<=j<Sta_UniMsg_Cmd.Length==>Sta_UniMsg_Cmd[i]!=Sta_UniMsg_Cmd[j]
requires 0<=dst<N0

requires ((Sta_Proc_ProcCmd[dst] == NODE_GetX) && (Sta_UniMsg_Cmd[dst] == UNI_PutX)) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Proc_CacheState
modifies Sta_Proc_InvMarked
modifies Sta_Proc_ProcCmd
modifies Sta_UniMsg_Cmd

{
  Sta_UniMsg_Cmd[dst] := UNI_None;
  Sta_Proc_ProcCmd[dst] := NODE_None;
  Sta_Proc_InvMarked[dst] := false;
  Sta_Proc_CacheState[dst] := CACHE_E;
}


method n_NI_Remote_Putinv__90_0(Sta_HomeUniMsg_Cmd:array<UNI_CMD>,   Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_Proc_CacheState:array<CACHE_STATE>,  Sta_Proc_InvMarked:array<boolean>, Sta_Proc_ProcCmd:array<NODE_CMD>, Sta_UniMsg_Cmd:array<UNI_CMD>,
N0:nat,dst:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_HomeUniMsg_Cmd.Length==N0


requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_Proc_CacheState.Length==N0

requires Sta_Proc_InvMarked.Length==N0
requires Sta_Proc_ProcCmd.Length==N0
requires Sta_UniMsg_Cmd.Length==N0
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]


requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_Proc_CacheState.Length&&0<=j<Sta_Proc_CacheState.Length==>Sta_Proc_CacheState[i]!=Sta_Proc_CacheState[j]

requires forall i,j::0<=i<Sta_Proc_InvMarked.Length&&0<=j<Sta_Proc_InvMarked.Length==>Sta_Proc_InvMarked[i]!=Sta_Proc_InvMarked[j]
requires forall i,j::0<=i<Sta_Proc_ProcCmd.Length&&0<=j<Sta_Proc_ProcCmd.Length==>Sta_Proc_ProcCmd[i]!=Sta_Proc_ProcCmd[j]
requires forall i,j::0<=i<Sta_UniMsg_Cmd.Length&&0<=j<Sta_UniMsg_Cmd.Length==>Sta_UniMsg_Cmd[i]!=Sta_UniMsg_Cmd[j]
requires 0<=dst<N0

requires (Sta_UniMsg_Cmd[dst] == UNI_Put) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Proc_CacheState
modifies Sta_Proc_InvMarked
modifies Sta_Proc_ProcCmd
modifies Sta_UniMsg_Cmd

{
  Sta_UniMsg_Cmd[dst] := UNI_None;
  Sta_Proc_ProcCmd[dst] := NODE_None;
  if (Sta_Proc_InvMarked[dst] == true) {
    Sta_Proc_InvMarked[dst] := false;
    Sta_Proc_CacheState[dst] := CACHE_I;}
else{
    Sta_Proc_CacheState[dst] := CACHE_S;
  }
}


method n_NI_Local_GetX_PutX_10inv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_HeadPtr:array<NODE>, Sta_Dir_HeadVld:array<boolean>, Sta_Dir_HomeHeadPtr:array<boolean>, Sta_Dir_HomeInvSet:array<boolean>, Sta_Dir_HomeShrSet:array<boolean>, Sta_Dir_InvSet:array<boolean>,  Sta_Dir_Local:array<boolean>, Sta_Dir_Pending:array<boolean>, Sta_Dir_ShrSet:array<boolean>,  Sta_Dir_ShrVld:array<boolean>, Sta_HomeInvMsg_Cmd:array<INV_CMD>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_InvMsg_Cmd:array<INV_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_UniMsg_Cmd:array<UNI_CMD>,  Sta_UniMsg_HomeProc:array<boolean>,
N0:nat,src:nat,pp:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0
requires N0>0

requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_HeadPtr.Length==N0
requires Sta_Dir_HeadVld.Length==N0
requires Sta_Dir_HomeHeadPtr.Length==N0
requires Sta_Dir_HomeInvSet.Length==N0
requires Sta_Dir_HomeShrSet.Length==N0
requires Sta_Dir_InvSet.Length==N0

requires Sta_Dir_Local.Length==N0
requires Sta_Dir_Pending.Length==N0
requires Sta_Dir_ShrSet.Length==N0

requires Sta_Dir_ShrVld.Length==N0
requires Sta_HomeInvMsg_Cmd.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_InvMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_UniMsg_Cmd.Length==N0

requires Sta_UniMsg_HomeProc.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_HeadPtr.Length&&0<=j<Sta_Dir_HeadPtr.Length==>Sta_Dir_HeadPtr[i]!=Sta_Dir_HeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HeadVld.Length&&0<=j<Sta_Dir_HeadVld.Length==>Sta_Dir_HeadVld[i]!=Sta_Dir_HeadVld[j]
requires forall i,j::0<=i<Sta_Dir_HomeHeadPtr.Length&&0<=j<Sta_Dir_HomeHeadPtr.Length==>Sta_Dir_HomeHeadPtr[i]!=Sta_Dir_HomeHeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HomeInvSet.Length&&0<=j<Sta_Dir_HomeInvSet.Length==>Sta_Dir_HomeInvSet[i]!=Sta_Dir_HomeInvSet[j]
requires forall i,j::0<=i<Sta_Dir_HomeShrSet.Length&&0<=j<Sta_Dir_HomeShrSet.Length==>Sta_Dir_HomeShrSet[i]!=Sta_Dir_HomeShrSet[j]
requires forall i,j::0<=i<Sta_Dir_InvSet.Length&&0<=j<Sta_Dir_InvSet.Length==>Sta_Dir_InvSet[i]!=Sta_Dir_InvSet[j]

requires forall i,j::0<=i<Sta_Dir_Local.Length&&0<=j<Sta_Dir_Local.Length==>Sta_Dir_Local[i]!=Sta_Dir_Local[j]
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_Dir_ShrSet.Length&&0<=j<Sta_Dir_ShrSet.Length==>Sta_Dir_ShrSet[i]!=Sta_Dir_ShrSet[j]

requires forall i,j::0<=i<Sta_Dir_ShrVld.Length&&0<=j<Sta_Dir_ShrVld.Length==>Sta_Dir_ShrVld[i]!=Sta_Dir_ShrVld[j]
requires forall i,j::0<=i<Sta_HomeInvMsg_Cmd.Length&&0<=j<Sta_HomeInvMsg_Cmd.Length==>Sta_HomeInvMsg_Cmd[i]!=Sta_HomeInvMsg_Cmd[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_InvMsg_Cmd.Length&&0<=j<Sta_InvMsg_Cmd.Length==>Sta_InvMsg_Cmd[i]!=Sta_InvMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_UniMsg_Cmd.Length&&0<=j<Sta_UniMsg_Cmd.Length==>Sta_UniMsg_Cmd[i]!=Sta_UniMsg_Cmd[j]

requires forall i,j::0<=i<Sta_UniMsg_HomeProc.Length&&0<=j<Sta_UniMsg_HomeProc.Length==>Sta_UniMsg_HomeProc[i]!=Sta_UniMsg_HomeProc[j]
requires 0<=src<N0
requires 0<=pp<N0

requires ((Sta_Dir_Dirty[0] == false) && (Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HomeHeadPtr[0] == false) && (Sta_Dir_Local[0] == false) && (Sta_Dir_Pending[0] == false) && (Sta_Dir_ShrSet[pp] == true) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true)) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd

{
  Sta_Dir_Pending[0] := true;
  Sta_Dir_Local[0] := false;
  Sta_Dir_Dirty[0] := true;
  Sta_Dir_HeadVld[0] := true;
  Sta_Dir_HeadPtr[0] := src;
  Sta_Dir_HomeHeadPtr[0] := false;
  Sta_Dir_ShrVld[0] := false;
  var p:=0;
  while(p<N0)
    decreases N0-p
 {
    Sta_Dir_ShrSet[p] := false;
    if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
      Sta_Dir_InvSet[p] := true;
      Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
      Sta_Dir_InvSet[p] := false;
      Sta_InvMsg_Cmd[p] := INV_None;
    }
  
 p:=p+1;
}
  Sta_Dir_HomeShrSet[0] := false;
  Sta_Dir_HomeInvSet[0] := false;
  Sta_HomeInvMsg_Cmd[0] := INV_None;
  Sta_UniMsg_Cmd[src] := UNI_PutX;
}


method n_NI_Local_GetX_PutX_8inv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_HeadPtr:array<NODE>, Sta_Dir_HeadVld:array<boolean>, Sta_Dir_HomeHeadPtr:array<boolean>, Sta_Dir_HomeInvSet:array<boolean>, Sta_Dir_HomeShrSet:array<boolean>, Sta_Dir_InvSet:array<boolean>,  Sta_Dir_Local:array<boolean>, Sta_Dir_Pending:array<boolean>, Sta_Dir_ShrSet:array<boolean>,  Sta_Dir_ShrVld:array<boolean>, Sta_HomeInvMsg_Cmd:array<INV_CMD>, Sta_HomeProc_CacheState:array<CACHE_STATE>, Sta_HomeProc_ProcCmd:array<NODE_CMD>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_InvMsg_Cmd:array<INV_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_UniMsg_Cmd:array<UNI_CMD>,  Sta_UniMsg_HomeProc:array<boolean>,
N0:nat,src:nat,pp:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0
requires N0>0

requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_HeadPtr.Length==N0
requires Sta_Dir_HeadVld.Length==N0
requires Sta_Dir_HomeHeadPtr.Length==N0
requires Sta_Dir_HomeInvSet.Length==N0
requires Sta_Dir_HomeShrSet.Length==N0
requires Sta_Dir_InvSet.Length==N0

requires Sta_Dir_Local.Length==N0
requires Sta_Dir_Pending.Length==N0
requires Sta_Dir_ShrSet.Length==N0

requires Sta_Dir_ShrVld.Length==N0
requires Sta_HomeInvMsg_Cmd.Length==N0
requires Sta_HomeProc_CacheState.Length==N0
requires Sta_HomeProc_ProcCmd.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_InvMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_UniMsg_Cmd.Length==N0

requires Sta_UniMsg_HomeProc.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_HeadPtr.Length&&0<=j<Sta_Dir_HeadPtr.Length==>Sta_Dir_HeadPtr[i]!=Sta_Dir_HeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HeadVld.Length&&0<=j<Sta_Dir_HeadVld.Length==>Sta_Dir_HeadVld[i]!=Sta_Dir_HeadVld[j]
requires forall i,j::0<=i<Sta_Dir_HomeHeadPtr.Length&&0<=j<Sta_Dir_HomeHeadPtr.Length==>Sta_Dir_HomeHeadPtr[i]!=Sta_Dir_HomeHeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HomeInvSet.Length&&0<=j<Sta_Dir_HomeInvSet.Length==>Sta_Dir_HomeInvSet[i]!=Sta_Dir_HomeInvSet[j]
requires forall i,j::0<=i<Sta_Dir_HomeShrSet.Length&&0<=j<Sta_Dir_HomeShrSet.Length==>Sta_Dir_HomeShrSet[i]!=Sta_Dir_HomeShrSet[j]
requires forall i,j::0<=i<Sta_Dir_InvSet.Length&&0<=j<Sta_Dir_InvSet.Length==>Sta_Dir_InvSet[i]!=Sta_Dir_InvSet[j]

requires forall i,j::0<=i<Sta_Dir_Local.Length&&0<=j<Sta_Dir_Local.Length==>Sta_Dir_Local[i]!=Sta_Dir_Local[j]
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_Dir_ShrSet.Length&&0<=j<Sta_Dir_ShrSet.Length==>Sta_Dir_ShrSet[i]!=Sta_Dir_ShrSet[j]

requires forall i,j::0<=i<Sta_Dir_ShrVld.Length&&0<=j<Sta_Dir_ShrVld.Length==>Sta_Dir_ShrVld[i]!=Sta_Dir_ShrVld[j]
requires forall i,j::0<=i<Sta_HomeInvMsg_Cmd.Length&&0<=j<Sta_HomeInvMsg_Cmd.Length==>Sta_HomeInvMsg_Cmd[i]!=Sta_HomeInvMsg_Cmd[j]
requires forall i,j::0<=i<Sta_HomeProc_CacheState.Length&&0<=j<Sta_HomeProc_CacheState.Length==>Sta_HomeProc_CacheState[i]!=Sta_HomeProc_CacheState[j]
requires forall i,j::0<=i<Sta_HomeProc_ProcCmd.Length&&0<=j<Sta_HomeProc_ProcCmd.Length==>Sta_HomeProc_ProcCmd[i]!=Sta_HomeProc_ProcCmd[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_InvMsg_Cmd.Length&&0<=j<Sta_InvMsg_Cmd.Length==>Sta_InvMsg_Cmd[i]!=Sta_InvMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_UniMsg_Cmd.Length&&0<=j<Sta_UniMsg_Cmd.Length==>Sta_UniMsg_Cmd[i]!=Sta_UniMsg_Cmd[j]

requires forall i,j::0<=i<Sta_UniMsg_HomeProc.Length&&0<=j<Sta_UniMsg_HomeProc.Length==>Sta_UniMsg_HomeProc[i]!=Sta_UniMsg_HomeProc[j]
requires 0<=src<N0
requires 0<=pp<N0

requires ((Sta_Dir_Dirty[0] == false) && (Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HomeHeadPtr[0] == false) && (Sta_Dir_Local[0] == true) && (Sta_Dir_Pending[0] == false) && (Sta_Dir_ShrSet[pp] == true) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_HomeProc_ProcCmd[0] == NODE_Get))) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd

{
  Sta_Dir_Pending[0] := true;
  Sta_Dir_Local[0] := false;
  Sta_Dir_Dirty[0] := true;
  Sta_Dir_HeadVld[0] := true;
  Sta_Dir_HeadPtr[0] := src;
  Sta_Dir_HomeHeadPtr[0] := false;
  Sta_Dir_ShrVld[0] := false;
  var p:=0;
  while(p<N0)
    decreases N0-p
 {
    Sta_Dir_ShrSet[p] := false;
    if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
      Sta_Dir_InvSet[p] := true;
      Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
      Sta_Dir_InvSet[p] := false;
      Sta_InvMsg_Cmd[p] := INV_None;
    }
  
 p:=p+1;
}
  Sta_Dir_HomeShrSet[0] := false;
  Sta_Dir_HomeInvSet[0] := false;
  Sta_HomeInvMsg_Cmd[0] := INV_None;
  Sta_UniMsg_Cmd[src] := UNI_PutX;
  Sta_HomeProc_CacheState[0] := CACHE_I;
}


method n_NI_Local_Get_Putinv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_HeadPtr:array<NODE>, Sta_Dir_HeadVld:array<boolean>, Sta_Dir_HomeHeadPtr:array<boolean>, Sta_Dir_Pending:array<boolean>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_RpMsg_Cmd:array<RP_CMD>,  Sta_UniMsg_Cmd:array<UNI_CMD>, Sta_UniMsg_HomeProc:array<boolean>,
N0:nat,src:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_HeadPtr.Length==N0
requires Sta_Dir_HeadVld.Length==N0
requires Sta_Dir_HomeHeadPtr.Length==N0
requires Sta_Dir_Pending.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_RpMsg_Cmd.Length==N0

requires Sta_UniMsg_Cmd.Length==N0
requires Sta_UniMsg_HomeProc.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_HeadPtr.Length&&0<=j<Sta_Dir_HeadPtr.Length==>Sta_Dir_HeadPtr[i]!=Sta_Dir_HeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HeadVld.Length&&0<=j<Sta_Dir_HeadVld.Length==>Sta_Dir_HeadVld[i]!=Sta_Dir_HeadVld[j]
requires forall i,j::0<=i<Sta_Dir_HomeHeadPtr.Length&&0<=j<Sta_Dir_HomeHeadPtr.Length==>Sta_Dir_HomeHeadPtr[i]!=Sta_Dir_HomeHeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_RpMsg_Cmd.Length&&0<=j<Sta_RpMsg_Cmd.Length==>Sta_RpMsg_Cmd[i]!=Sta_RpMsg_Cmd[j]

requires forall i,j::0<=i<Sta_UniMsg_Cmd.Length&&0<=j<Sta_UniMsg_Cmd.Length==>Sta_UniMsg_Cmd[i]!=Sta_UniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_UniMsg_HomeProc.Length&&0<=j<Sta_UniMsg_HomeProc.Length==>Sta_UniMsg_HomeProc[i]!=Sta_UniMsg_HomeProc[j]
requires 0<=src<N0

requires ((Sta_Dir_Dirty[0] == false) && (Sta_Dir_HeadVld[0] == false) && (Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_Get) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_RpMsg_Cmd[src] == RP_Replace))) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_UniMsg_Cmd

{
  Sta_Dir_HeadVld[0] := true;
  Sta_Dir_HeadPtr[0] := src;
  Sta_Dir_HomeHeadPtr[0] := false;
  Sta_UniMsg_Cmd[src] := UNI_Put;
}


method n_NI_Local_GetX_PutX_8_NODE_Getinv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_HeadPtr:array<NODE>, Sta_Dir_HeadVld:array<boolean>, Sta_Dir_HomeHeadPtr:array<boolean>, Sta_Dir_HomeInvSet:array<boolean>, Sta_Dir_HomeShrSet:array<boolean>, Sta_Dir_InvSet:array<boolean>,  Sta_Dir_Local:array<boolean>, Sta_Dir_Pending:array<boolean>, Sta_Dir_ShrSet:array<boolean>,  Sta_Dir_ShrVld:array<boolean>, Sta_HomeInvMsg_Cmd:array<INV_CMD>, Sta_HomeProc_CacheState:array<CACHE_STATE>, Sta_HomeProc_InvMarked:array<boolean>, Sta_HomeProc_ProcCmd:array<NODE_CMD>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_InvMsg_Cmd:array<INV_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_UniMsg_Cmd:array<UNI_CMD>,  Sta_UniMsg_HomeProc:array<boolean>,
N0:nat,src:nat,pp:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0
requires N0>0

requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_HeadPtr.Length==N0
requires Sta_Dir_HeadVld.Length==N0
requires Sta_Dir_HomeHeadPtr.Length==N0
requires Sta_Dir_HomeInvSet.Length==N0
requires Sta_Dir_HomeShrSet.Length==N0
requires Sta_Dir_InvSet.Length==N0

requires Sta_Dir_Local.Length==N0
requires Sta_Dir_Pending.Length==N0
requires Sta_Dir_ShrSet.Length==N0

requires Sta_Dir_ShrVld.Length==N0
requires Sta_HomeInvMsg_Cmd.Length==N0
requires Sta_HomeProc_CacheState.Length==N0
requires Sta_HomeProc_InvMarked.Length==N0
requires Sta_HomeProc_ProcCmd.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_InvMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_UniMsg_Cmd.Length==N0

requires Sta_UniMsg_HomeProc.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_HeadPtr.Length&&0<=j<Sta_Dir_HeadPtr.Length==>Sta_Dir_HeadPtr[i]!=Sta_Dir_HeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HeadVld.Length&&0<=j<Sta_Dir_HeadVld.Length==>Sta_Dir_HeadVld[i]!=Sta_Dir_HeadVld[j]
requires forall i,j::0<=i<Sta_Dir_HomeHeadPtr.Length&&0<=j<Sta_Dir_HomeHeadPtr.Length==>Sta_Dir_HomeHeadPtr[i]!=Sta_Dir_HomeHeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HomeInvSet.Length&&0<=j<Sta_Dir_HomeInvSet.Length==>Sta_Dir_HomeInvSet[i]!=Sta_Dir_HomeInvSet[j]
requires forall i,j::0<=i<Sta_Dir_HomeShrSet.Length&&0<=j<Sta_Dir_HomeShrSet.Length==>Sta_Dir_HomeShrSet[i]!=Sta_Dir_HomeShrSet[j]
requires forall i,j::0<=i<Sta_Dir_InvSet.Length&&0<=j<Sta_Dir_InvSet.Length==>Sta_Dir_InvSet[i]!=Sta_Dir_InvSet[j]

requires forall i,j::0<=i<Sta_Dir_Local.Length&&0<=j<Sta_Dir_Local.Length==>Sta_Dir_Local[i]!=Sta_Dir_Local[j]
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_Dir_ShrSet.Length&&0<=j<Sta_Dir_ShrSet.Length==>Sta_Dir_ShrSet[i]!=Sta_Dir_ShrSet[j]

requires forall i,j::0<=i<Sta_Dir_ShrVld.Length&&0<=j<Sta_Dir_ShrVld.Length==>Sta_Dir_ShrVld[i]!=Sta_Dir_ShrVld[j]
requires forall i,j::0<=i<Sta_HomeInvMsg_Cmd.Length&&0<=j<Sta_HomeInvMsg_Cmd.Length==>Sta_HomeInvMsg_Cmd[i]!=Sta_HomeInvMsg_Cmd[j]
requires forall i,j::0<=i<Sta_HomeProc_CacheState.Length&&0<=j<Sta_HomeProc_CacheState.Length==>Sta_HomeProc_CacheState[i]!=Sta_HomeProc_CacheState[j]
requires forall i,j::0<=i<Sta_HomeProc_InvMarked.Length&&0<=j<Sta_HomeProc_InvMarked.Length==>Sta_HomeProc_InvMarked[i]!=Sta_HomeProc_InvMarked[j]
requires forall i,j::0<=i<Sta_HomeProc_ProcCmd.Length&&0<=j<Sta_HomeProc_ProcCmd.Length==>Sta_HomeProc_ProcCmd[i]!=Sta_HomeProc_ProcCmd[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_InvMsg_Cmd.Length&&0<=j<Sta_InvMsg_Cmd.Length==>Sta_InvMsg_Cmd[i]!=Sta_InvMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_UniMsg_Cmd.Length&&0<=j<Sta_UniMsg_Cmd.Length==>Sta_UniMsg_Cmd[i]!=Sta_UniMsg_Cmd[j]

requires forall i,j::0<=i<Sta_UniMsg_HomeProc.Length&&0<=j<Sta_UniMsg_HomeProc.Length==>Sta_UniMsg_HomeProc[i]!=Sta_UniMsg_HomeProc[j]
requires 0<=src<N0
requires 0<=pp<N0

requires ((Sta_Dir_Dirty[0] == false) && (Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HomeHeadPtr[0] == false) && (Sta_Dir_Local[0] == true) && (Sta_Dir_Pending[0] == false) && (Sta_Dir_ShrSet[pp] == true) && (Sta_HomeProc_ProcCmd[0] == NODE_Get) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true)) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd

{
  Sta_Dir_Pending[0] := true;
  Sta_Dir_Local[0] := false;
  Sta_Dir_Dirty[0] := true;
  Sta_Dir_HeadVld[0] := true;
  Sta_Dir_HeadPtr[0] := src;
  Sta_Dir_HomeHeadPtr[0] := false;
  Sta_Dir_ShrVld[0] := false;
  var p:=0;
  while(p<N0)
    decreases N0-p
 {
    Sta_Dir_ShrSet[p] := false;
    if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
      Sta_Dir_InvSet[p] := true;
      Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
      Sta_Dir_InvSet[p] := false;
      Sta_InvMsg_Cmd[p] := INV_None;
    }
  
 p:=p+1;
}
  Sta_Dir_HomeShrSet[0] := false;
  Sta_Dir_HomeInvSet[0] := false;
  Sta_HomeInvMsg_Cmd[0] := INV_None;
  Sta_UniMsg_Cmd[src] := UNI_PutX;
  Sta_HomeProc_CacheState[0] := CACHE_I;
  Sta_HomeProc_InvMarked[0] := true;
}


method n_NI_Local_GetX_PutX_2inv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_HeadPtr:array<NODE>, Sta_Dir_HeadVld:array<boolean>, Sta_Dir_HomeHeadPtr:array<boolean>, Sta_Dir_HomeInvSet:array<boolean>, Sta_Dir_HomeShrSet:array<boolean>, Sta_Dir_InvSet:array<boolean>,  Sta_Dir_Local:array<boolean>, Sta_Dir_Pending:array<boolean>, Sta_Dir_ShrSet:array<boolean>, Sta_Dir_ShrVld:array<boolean>, Sta_HomeProc_CacheState:array<CACHE_STATE>, Sta_HomeProc_ProcCmd:array<NODE_CMD>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_UniMsg_Cmd:array<UNI_CMD>,  Sta_UniMsg_HomeProc:array<boolean>,
N0:nat,src:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_HeadPtr.Length==N0
requires Sta_Dir_HeadVld.Length==N0
requires Sta_Dir_HomeHeadPtr.Length==N0
requires Sta_Dir_HomeInvSet.Length==N0
requires Sta_Dir_HomeShrSet.Length==N0
requires Sta_Dir_InvSet.Length==N0

requires Sta_Dir_Local.Length==N0
requires Sta_Dir_Pending.Length==N0
requires Sta_Dir_ShrSet.Length==N0
requires Sta_Dir_ShrVld.Length==N0
requires Sta_HomeProc_CacheState.Length==N0
requires Sta_HomeProc_ProcCmd.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_UniMsg_Cmd.Length==N0

requires Sta_UniMsg_HomeProc.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_HeadPtr.Length&&0<=j<Sta_Dir_HeadPtr.Length==>Sta_Dir_HeadPtr[i]!=Sta_Dir_HeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HeadVld.Length&&0<=j<Sta_Dir_HeadVld.Length==>Sta_Dir_HeadVld[i]!=Sta_Dir_HeadVld[j]
requires forall i,j::0<=i<Sta_Dir_HomeHeadPtr.Length&&0<=j<Sta_Dir_HomeHeadPtr.Length==>Sta_Dir_HomeHeadPtr[i]!=Sta_Dir_HomeHeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HomeInvSet.Length&&0<=j<Sta_Dir_HomeInvSet.Length==>Sta_Dir_HomeInvSet[i]!=Sta_Dir_HomeInvSet[j]
requires forall i,j::0<=i<Sta_Dir_HomeShrSet.Length&&0<=j<Sta_Dir_HomeShrSet.Length==>Sta_Dir_HomeShrSet[i]!=Sta_Dir_HomeShrSet[j]
requires forall i,j::0<=i<Sta_Dir_InvSet.Length&&0<=j<Sta_Dir_InvSet.Length==>Sta_Dir_InvSet[i]!=Sta_Dir_InvSet[j]

requires forall i,j::0<=i<Sta_Dir_Local.Length&&0<=j<Sta_Dir_Local.Length==>Sta_Dir_Local[i]!=Sta_Dir_Local[j]
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_Dir_ShrSet.Length&&0<=j<Sta_Dir_ShrSet.Length==>Sta_Dir_ShrSet[i]!=Sta_Dir_ShrSet[j]
requires forall i,j::0<=i<Sta_Dir_ShrVld.Length&&0<=j<Sta_Dir_ShrVld.Length==>Sta_Dir_ShrVld[i]!=Sta_Dir_ShrVld[j]
requires forall i,j::0<=i<Sta_HomeProc_CacheState.Length&&0<=j<Sta_HomeProc_CacheState.Length==>Sta_HomeProc_CacheState[i]!=Sta_HomeProc_CacheState[j]
requires forall i,j::0<=i<Sta_HomeProc_ProcCmd.Length&&0<=j<Sta_HomeProc_ProcCmd.Length==>Sta_HomeProc_ProcCmd[i]!=Sta_HomeProc_ProcCmd[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_UniMsg_Cmd.Length&&0<=j<Sta_UniMsg_Cmd.Length==>Sta_UniMsg_Cmd[i]!=Sta_UniMsg_Cmd[j]

requires forall i,j::0<=i<Sta_UniMsg_HomeProc.Length&&0<=j<Sta_UniMsg_HomeProc.Length==>Sta_UniMsg_HomeProc[i]!=Sta_UniMsg_HomeProc[j]
requires 0<=src<N0

requires ((Sta_Dir_Dirty[0] == false) && (Sta_Dir_HeadVld[0] == false) && (Sta_Dir_Local[0] == true) && (Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_HomeProc_ProcCmd[0] == NODE_Get))) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeProc_CacheState
modifies Sta_UniMsg_Cmd

{
  Sta_Dir_Local[0] := false;
  Sta_Dir_Dirty[0] := true;
  Sta_Dir_HeadVld[0] := true;
  Sta_Dir_HeadPtr[0] := src;
  Sta_Dir_HomeHeadPtr[0] := false;
  Sta_Dir_ShrVld[0] := false;
  var p:=0;
  while(p<N0)
    decreases N0-p
 {
    Sta_Dir_ShrSet[p] := false;
    Sta_Dir_InvSet[p] := false;
  
 p:=p+1;
}
  Sta_Dir_HomeShrSet[0] := false;
  Sta_Dir_HomeInvSet[0] := false;
  Sta_UniMsg_Cmd[src] := UNI_PutX;
  Sta_HomeProc_CacheState[0] := CACHE_I;
}


method n_NI_Local_GetX_Nak__part__0inv__90_0(Sta_Dir_Pending:array<boolean>,   Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_UniMsg_Cmd:array<UNI_CMD>,  Sta_UniMsg_HomeProc:array<boolean>,
N0:nat,src:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_Dir_Pending.Length==N0


requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_UniMsg_Cmd.Length==N0

requires Sta_UniMsg_HomeProc.Length==N0
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]


requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_UniMsg_Cmd.Length&&0<=j<Sta_UniMsg_Cmd.Length==>Sta_UniMsg_Cmd[i]!=Sta_UniMsg_Cmd[j]

requires forall i,j::0<=i<Sta_UniMsg_HomeProc.Length&&0<=j<Sta_UniMsg_HomeProc.Length==>Sta_UniMsg_HomeProc[i]!=Sta_UniMsg_HomeProc[j]
requires 0<=src<N0

requires ((Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (Sta_Dir_Pending[0] == true)) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_UniMsg_Cmd

{
  Sta_UniMsg_Cmd[src] := UNI_Nak;
}


method n_NI_InvAck_exists_Homeinv__90_0(Sta_Dir_HomeInvSet:array<boolean>,   Sta_Dir_InvSet:array<boolean>,  Sta_Dir_Pending:array<boolean>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_InvMsg_Cmd:array<INV_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>,
N0:nat,src:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_Dir_HomeInvSet.Length==N0


requires Sta_Dir_InvSet.Length==N0

requires Sta_Dir_Pending.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_InvMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires forall i,j::0<=i<Sta_Dir_HomeInvSet.Length&&0<=j<Sta_Dir_HomeInvSet.Length==>Sta_Dir_HomeInvSet[i]!=Sta_Dir_HomeInvSet[j]


requires forall i,j::0<=i<Sta_Dir_InvSet.Length&&0<=j<Sta_Dir_InvSet.Length==>Sta_Dir_InvSet[i]!=Sta_Dir_InvSet[j]

requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_InvMsg_Cmd.Length&&0<=j<Sta_InvMsg_Cmd.Length==>Sta_InvMsg_Cmd[i]!=Sta_InvMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires 0<=src<N0

requires ((Sta_Dir_HomeInvSet[0] == true) && (Sta_Dir_InvSet[src] == true) && (Sta_Dir_Pending[0] == true) && (Sta_InvMsg_Cmd[src] == INV_InvAck)) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_InvSet
modifies Sta_InvMsg_Cmd

{
  Sta_InvMsg_Cmd[src] := INV_None;
  Sta_Dir_InvSet[src] := false;
}



method n_NI_Replace_Homeinv__90_0(Sta_Dir_HomeInvSet:array<boolean>,   Sta_Dir_HomeShrSet:array<boolean>, Sta_Dir_ShrVld:array<boolean>, Sta_HomeRpMsg_Cmd:array<RP_CMD>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>,
N0:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0
requires Sta_Dir_HomeInvSet.Length==N0


requires Sta_Dir_HomeShrSet.Length==N0
requires Sta_Dir_ShrVld.Length==N0
requires Sta_HomeRpMsg_Cmd.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires forall i,j::0<=i<Sta_Dir_HomeInvSet.Length&&0<=j<Sta_Dir_HomeInvSet.Length==>Sta_Dir_HomeInvSet[i]!=Sta_Dir_HomeInvSet[j]


requires forall i,j::0<=i<Sta_Dir_HomeShrSet.Length&&0<=j<Sta_Dir_HomeShrSet.Length==>Sta_Dir_HomeShrSet[i]!=Sta_Dir_HomeShrSet[j]
requires forall i,j::0<=i<Sta_Dir_ShrVld.Length&&0<=j<Sta_Dir_ShrVld.Length==>Sta_Dir_ShrVld[i]!=Sta_Dir_ShrVld[j]
requires forall i,j::0<=i<Sta_HomeRpMsg_Cmd.Length&&0<=j<Sta_HomeRpMsg_Cmd.Length==>Sta_HomeRpMsg_Cmd[i]!=Sta_HomeRpMsg_Cmd[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
//guard condition
requires   (Sta_HomeRpMsg_Cmd[0] == RP_Replace)
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeRpMsg_Cmd
{
  Sta_HomeRpMsg_Cmd[0] := RP_None;
  if (Sta_Dir_ShrVld[0] == true) {
    Sta_Dir_HomeShrSet[0] := false;
    Sta_Dir_HomeInvSet[0] := false;
  }
}

method n_NI_Remote_GetX_PutXinv__90_0(Sta_HomeUniMsg_Cmd:array<UNI_CMD>,   Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_Proc_CacheState:array<CACHE_STATE>,  Sta_ShWbMsg_Cmd:array<SHWB_CMD>, Sta_ShWbMsg_HomeProc:array<boolean>, Sta_ShWbMsg_Proc:array<NODE>, Sta_UniMsg_Cmd:array<UNI_CMD>,  Sta_UniMsg_HomeProc:array<boolean>, Sta_UniMsg_Proc:array<NODE>,
N0:nat,src:nat,dst:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0
requires N0>0

requires Sta_HomeUniMsg_Cmd.Length==N0


requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_Proc_CacheState.Length==N0

requires Sta_ShWbMsg_Cmd.Length==N0
requires Sta_ShWbMsg_HomeProc.Length==N0
requires Sta_ShWbMsg_Proc.Length==N0
requires Sta_UniMsg_Cmd.Length==N0

requires Sta_UniMsg_HomeProc.Length==N0
requires Sta_UniMsg_Proc.Length==N0
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]


requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_Proc_CacheState.Length&&0<=j<Sta_Proc_CacheState.Length==>Sta_Proc_CacheState[i]!=Sta_Proc_CacheState[j]

requires forall i,j::0<=i<Sta_ShWbMsg_Cmd.Length&&0<=j<Sta_ShWbMsg_Cmd.Length==>Sta_ShWbMsg_Cmd[i]!=Sta_ShWbMsg_Cmd[j]
requires forall i,j::0<=i<Sta_ShWbMsg_HomeProc.Length&&0<=j<Sta_ShWbMsg_HomeProc.Length==>Sta_ShWbMsg_HomeProc[i]!=Sta_ShWbMsg_HomeProc[j]
requires forall i,j::0<=i<Sta_ShWbMsg_Proc.Length&&0<=j<Sta_ShWbMsg_Proc.Length==>Sta_ShWbMsg_Proc[i]!=Sta_ShWbMsg_Proc[j]
requires forall i,j::0<=i<Sta_UniMsg_Cmd.Length&&0<=j<Sta_UniMsg_Cmd.Length==>Sta_UniMsg_Cmd[i]!=Sta_UniMsg_Cmd[j]

requires forall i,j::0<=i<Sta_UniMsg_HomeProc.Length&&0<=j<Sta_UniMsg_HomeProc.Length==>Sta_UniMsg_HomeProc[i]!=Sta_UniMsg_HomeProc[j]
requires forall i,j::0<=i<Sta_UniMsg_Proc.Length&&0<=j<Sta_UniMsg_Proc.Length==>Sta_UniMsg_Proc[i]!=Sta_UniMsg_Proc[j]
requires 0<=src<N0
requires 0<=dst<N0

requires ((Sta_Proc_CacheState[dst] == CACHE_E) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == false) && (Sta_UniMsg_Proc[src] == dst) && (!(src == dst))) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Proc_CacheState
modifies Sta_ShWbMsg_Cmd
modifies Sta_ShWbMsg_HomeProc
modifies Sta_ShWbMsg_Proc
modifies Sta_UniMsg_Cmd

{
  Sta_Proc_CacheState[dst] := CACHE_I;
  Sta_UniMsg_Cmd[src] := UNI_PutX;
  Sta_ShWbMsg_Cmd[0] := SHWB_FAck;
  Sta_ShWbMsg_Proc[0] := src;
  Sta_ShWbMsg_HomeProc[0] := false;
}


method n_NI_Local_GetX_PutX_7__part__1inv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_HeadPtr:array<NODE>, Sta_Dir_HeadVld:array<boolean>, Sta_Dir_HomeHeadPtr:array<boolean>, Sta_Dir_HomeInvSet:array<boolean>, Sta_Dir_HomeShrSet:array<boolean>, Sta_Dir_InvSet:array<boolean>,  Sta_Dir_Local:array<boolean>, Sta_Dir_Pending:array<boolean>, Sta_Dir_ShrSet:array<boolean>, Sta_Dir_ShrVld:array<boolean>, Sta_HomeInvMsg_Cmd:array<INV_CMD>, Sta_HomeProc_CacheState:array<CACHE_STATE>, Sta_HomeProc_ProcCmd:array<NODE_CMD>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_InvMsg_Cmd:array<INV_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_UniMsg_Cmd:array<UNI_CMD>,  Sta_UniMsg_HomeProc:array<boolean>,
N0:nat,src:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_HeadPtr.Length==N0
requires Sta_Dir_HeadVld.Length==N0
requires Sta_Dir_HomeHeadPtr.Length==N0
requires Sta_Dir_HomeInvSet.Length==N0
requires Sta_Dir_HomeShrSet.Length==N0
requires Sta_Dir_InvSet.Length==N0

requires Sta_Dir_Local.Length==N0
requires Sta_Dir_Pending.Length==N0
requires Sta_Dir_ShrSet.Length==N0
requires Sta_Dir_ShrVld.Length==N0
requires Sta_HomeInvMsg_Cmd.Length==N0
requires Sta_HomeProc_CacheState.Length==N0
requires Sta_HomeProc_ProcCmd.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_InvMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_UniMsg_Cmd.Length==N0

requires Sta_UniMsg_HomeProc.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_HeadPtr.Length&&0<=j<Sta_Dir_HeadPtr.Length==>Sta_Dir_HeadPtr[i]!=Sta_Dir_HeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HeadVld.Length&&0<=j<Sta_Dir_HeadVld.Length==>Sta_Dir_HeadVld[i]!=Sta_Dir_HeadVld[j]
requires forall i,j::0<=i<Sta_Dir_HomeHeadPtr.Length&&0<=j<Sta_Dir_HomeHeadPtr.Length==>Sta_Dir_HomeHeadPtr[i]!=Sta_Dir_HomeHeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HomeInvSet.Length&&0<=j<Sta_Dir_HomeInvSet.Length==>Sta_Dir_HomeInvSet[i]!=Sta_Dir_HomeInvSet[j]
requires forall i,j::0<=i<Sta_Dir_HomeShrSet.Length&&0<=j<Sta_Dir_HomeShrSet.Length==>Sta_Dir_HomeShrSet[i]!=Sta_Dir_HomeShrSet[j]
requires forall i,j::0<=i<Sta_Dir_InvSet.Length&&0<=j<Sta_Dir_InvSet.Length==>Sta_Dir_InvSet[i]!=Sta_Dir_InvSet[j]

requires forall i,j::0<=i<Sta_Dir_Local.Length&&0<=j<Sta_Dir_Local.Length==>Sta_Dir_Local[i]!=Sta_Dir_Local[j]
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_Dir_ShrSet.Length&&0<=j<Sta_Dir_ShrSet.Length==>Sta_Dir_ShrSet[i]!=Sta_Dir_ShrSet[j]
requires forall i,j::0<=i<Sta_Dir_ShrVld.Length&&0<=j<Sta_Dir_ShrVld.Length==>Sta_Dir_ShrVld[i]!=Sta_Dir_ShrVld[j]
requires forall i,j::0<=i<Sta_HomeInvMsg_Cmd.Length&&0<=j<Sta_HomeInvMsg_Cmd.Length==>Sta_HomeInvMsg_Cmd[i]!=Sta_HomeInvMsg_Cmd[j]
requires forall i,j::0<=i<Sta_HomeProc_CacheState.Length&&0<=j<Sta_HomeProc_CacheState.Length==>Sta_HomeProc_CacheState[i]!=Sta_HomeProc_CacheState[j]
requires forall i,j::0<=i<Sta_HomeProc_ProcCmd.Length&&0<=j<Sta_HomeProc_ProcCmd.Length==>Sta_HomeProc_ProcCmd[i]!=Sta_HomeProc_ProcCmd[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_InvMsg_Cmd.Length&&0<=j<Sta_InvMsg_Cmd.Length==>Sta_InvMsg_Cmd[i]!=Sta_InvMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_UniMsg_Cmd.Length&&0<=j<Sta_UniMsg_Cmd.Length==>Sta_UniMsg_Cmd[i]!=Sta_UniMsg_Cmd[j]

requires forall i,j::0<=i<Sta_UniMsg_HomeProc.Length&&0<=j<Sta_UniMsg_HomeProc.Length==>Sta_UniMsg_HomeProc[i]!=Sta_UniMsg_HomeProc[j]
requires 0<=src<N0

requires ((Sta_Dir_Dirty[0] == false) && (Sta_Dir_HeadVld[0] == true) && (Sta_Dir_Local[0] == true) && (Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_HomeProc_ProcCmd[0] == NODE_Get)) && (!(Sta_Dir_HeadPtr[0] == src))) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd

{
  Sta_Dir_Pending[0] := true;
  Sta_Dir_Local[0] := false;
  Sta_Dir_Dirty[0] := true;
  Sta_Dir_HeadVld[0] := true;
  Sta_Dir_HeadPtr[0] := src;
  Sta_Dir_HomeHeadPtr[0] := false;
  Sta_Dir_ShrVld[0] := false;
  var p:=0;
  while(p<N0)
    decreases N0-p
 {
    Sta_Dir_ShrSet[p] := false;
    if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
      Sta_Dir_InvSet[p] := true;
      Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
      Sta_Dir_InvSet[p] := false;
      Sta_InvMsg_Cmd[p] := INV_None;
    }
  
 p:=p+1;
}
  Sta_Dir_HomeShrSet[0] := false;
  Sta_Dir_HomeInvSet[0] := false;
  Sta_HomeInvMsg_Cmd[0] := INV_None;
  Sta_UniMsg_Cmd[src] := UNI_PutX;
  Sta_HomeProc_CacheState[0] := CACHE_I;
}


method n_NI_Local_Get_Put_Dirtyinv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_HeadPtr:array<NODE>, Sta_Dir_HeadVld:array<boolean>, Sta_Dir_HomeHeadPtr:array<boolean>, Sta_Dir_Local:array<boolean>, Sta_Dir_Pending:array<boolean>, Sta_HomeProc_CacheState:array<CACHE_STATE>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_RpMsg_Cmd:array<RP_CMD>,  Sta_UniMsg_Cmd:array<UNI_CMD>, Sta_UniMsg_HomeProc:array<boolean>,
N0:nat,src:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_HeadPtr.Length==N0
requires Sta_Dir_HeadVld.Length==N0
requires Sta_Dir_HomeHeadPtr.Length==N0
requires Sta_Dir_Local.Length==N0
requires Sta_Dir_Pending.Length==N0
requires Sta_HomeProc_CacheState.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_RpMsg_Cmd.Length==N0

requires Sta_UniMsg_Cmd.Length==N0
requires Sta_UniMsg_HomeProc.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_HeadPtr.Length&&0<=j<Sta_Dir_HeadPtr.Length==>Sta_Dir_HeadPtr[i]!=Sta_Dir_HeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HeadVld.Length&&0<=j<Sta_Dir_HeadVld.Length==>Sta_Dir_HeadVld[i]!=Sta_Dir_HeadVld[j]
requires forall i,j::0<=i<Sta_Dir_HomeHeadPtr.Length&&0<=j<Sta_Dir_HomeHeadPtr.Length==>Sta_Dir_HomeHeadPtr[i]!=Sta_Dir_HomeHeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_Local.Length&&0<=j<Sta_Dir_Local.Length==>Sta_Dir_Local[i]!=Sta_Dir_Local[j]
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_HomeProc_CacheState.Length&&0<=j<Sta_HomeProc_CacheState.Length==>Sta_HomeProc_CacheState[i]!=Sta_HomeProc_CacheState[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_RpMsg_Cmd.Length&&0<=j<Sta_RpMsg_Cmd.Length==>Sta_RpMsg_Cmd[i]!=Sta_RpMsg_Cmd[j]

requires forall i,j::0<=i<Sta_UniMsg_Cmd.Length&&0<=j<Sta_UniMsg_Cmd.Length==>Sta_UniMsg_Cmd[i]!=Sta_UniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_UniMsg_HomeProc.Length&&0<=j<Sta_UniMsg_HomeProc.Length==>Sta_UniMsg_HomeProc[i]!=Sta_UniMsg_HomeProc[j]
requires 0<=src<N0

requires ((Sta_Dir_Dirty[0] == true) && (Sta_Dir_Local[0] == true) && (Sta_Dir_Pending[0] == false) && (Sta_HomeProc_CacheState[0] == CACHE_E) && (Sta_UniMsg_Cmd[src] == UNI_Get) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_RpMsg_Cmd[src] == RP_Replace))) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_HomeProc_CacheState
modifies Sta_UniMsg_Cmd

{
  Sta_Dir_Dirty[0] := false;
  Sta_Dir_HeadVld[0] := true;
  Sta_Dir_HeadPtr[0] := src;
  Sta_Dir_HomeHeadPtr[0] := false;
  Sta_HomeProc_CacheState[0] := CACHE_S;
  Sta_UniMsg_Cmd[src] := UNI_Put;
}


method n_NI_Local_Get_Nak__part__0inv__90_0(Sta_Dir_Pending:array<boolean>,   Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_RpMsg_Cmd:array<RP_CMD>,  Sta_UniMsg_Cmd:array<UNI_CMD>, Sta_UniMsg_HomeProc:array<boolean>,
N0:nat,src:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_Dir_Pending.Length==N0


requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_RpMsg_Cmd.Length==N0

requires Sta_UniMsg_Cmd.Length==N0
requires Sta_UniMsg_HomeProc.Length==N0
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]


requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_RpMsg_Cmd.Length&&0<=j<Sta_RpMsg_Cmd.Length==>Sta_RpMsg_Cmd[i]!=Sta_RpMsg_Cmd[j]

requires forall i,j::0<=i<Sta_UniMsg_Cmd.Length&&0<=j<Sta_UniMsg_Cmd.Length==>Sta_UniMsg_Cmd[i]!=Sta_UniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_UniMsg_HomeProc.Length&&0<=j<Sta_UniMsg_HomeProc.Length==>Sta_UniMsg_HomeProc[i]!=Sta_UniMsg_HomeProc[j]
requires 0<=src<N0

requires ((Sta_UniMsg_Cmd[src] == UNI_Get) && (Sta_UniMsg_HomeProc[src] == true) && (!(Sta_RpMsg_Cmd[src] == RP_Replace)) && (Sta_Dir_Pending[0] == true)) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_UniMsg_Cmd

{
  Sta_UniMsg_Cmd[src] := UNI_Nak;
}


method n_NI_Remote_Get_Putinv__90_0(Sta_HomeUniMsg_Cmd:array<UNI_CMD>,   Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_Proc_CacheState:array<CACHE_STATE>,  Sta_ShWbMsg_Cmd:array<SHWB_CMD>, Sta_ShWbMsg_HomeProc:array<boolean>, Sta_ShWbMsg_Proc:array<NODE>, Sta_UniMsg_Cmd:array<UNI_CMD>,  Sta_UniMsg_HomeProc:array<boolean>, Sta_UniMsg_Proc:array<NODE>,
N0:nat,src:nat,dst:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0
requires N0>0

requires Sta_HomeUniMsg_Cmd.Length==N0


requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_Proc_CacheState.Length==N0

requires Sta_ShWbMsg_Cmd.Length==N0
requires Sta_ShWbMsg_HomeProc.Length==N0
requires Sta_ShWbMsg_Proc.Length==N0
requires Sta_UniMsg_Cmd.Length==N0

requires Sta_UniMsg_HomeProc.Length==N0
requires Sta_UniMsg_Proc.Length==N0
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]


requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_Proc_CacheState.Length&&0<=j<Sta_Proc_CacheState.Length==>Sta_Proc_CacheState[i]!=Sta_Proc_CacheState[j]

requires forall i,j::0<=i<Sta_ShWbMsg_Cmd.Length&&0<=j<Sta_ShWbMsg_Cmd.Length==>Sta_ShWbMsg_Cmd[i]!=Sta_ShWbMsg_Cmd[j]
requires forall i,j::0<=i<Sta_ShWbMsg_HomeProc.Length&&0<=j<Sta_ShWbMsg_HomeProc.Length==>Sta_ShWbMsg_HomeProc[i]!=Sta_ShWbMsg_HomeProc[j]
requires forall i,j::0<=i<Sta_ShWbMsg_Proc.Length&&0<=j<Sta_ShWbMsg_Proc.Length==>Sta_ShWbMsg_Proc[i]!=Sta_ShWbMsg_Proc[j]
requires forall i,j::0<=i<Sta_UniMsg_Cmd.Length&&0<=j<Sta_UniMsg_Cmd.Length==>Sta_UniMsg_Cmd[i]!=Sta_UniMsg_Cmd[j]

requires forall i,j::0<=i<Sta_UniMsg_HomeProc.Length&&0<=j<Sta_UniMsg_HomeProc.Length==>Sta_UniMsg_HomeProc[i]!=Sta_UniMsg_HomeProc[j]
requires forall i,j::0<=i<Sta_UniMsg_Proc.Length&&0<=j<Sta_UniMsg_Proc.Length==>Sta_UniMsg_Proc[i]!=Sta_UniMsg_Proc[j]
requires 0<=src<N0
requires 0<=dst<N0

requires ((Sta_Proc_CacheState[dst] == CACHE_E) && (Sta_UniMsg_Cmd[src] == UNI_Get) && (Sta_UniMsg_HomeProc[src] == false) && (Sta_UniMsg_Proc[src] == dst) && (!(src == dst))) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Proc_CacheState
modifies Sta_ShWbMsg_Cmd
modifies Sta_ShWbMsg_HomeProc
modifies Sta_ShWbMsg_Proc
modifies Sta_UniMsg_Cmd

{
  Sta_Proc_CacheState[dst] := CACHE_S;
  Sta_UniMsg_Cmd[src] := UNI_Put;
  Sta_ShWbMsg_Cmd[0] := SHWB_ShWb;
  Sta_ShWbMsg_Proc[0] := src;
  Sta_ShWbMsg_HomeProc[0] := false;
}


method n_NI_Local_GetX_PutX_10_Homeinv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_HeadPtr:array<NODE>, Sta_Dir_HeadVld:array<boolean>, Sta_Dir_HomeHeadPtr:array<boolean>, Sta_Dir_HomeInvSet:array<boolean>, Sta_Dir_HomeShrSet:array<boolean>, Sta_Dir_InvSet:array<boolean>,  Sta_Dir_Local:array<boolean>, Sta_Dir_Pending:array<boolean>, Sta_Dir_ShrSet:array<boolean>, Sta_Dir_ShrVld:array<boolean>, Sta_HomeInvMsg_Cmd:array<INV_CMD>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_InvMsg_Cmd:array<INV_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_UniMsg_Cmd:array<UNI_CMD>,  Sta_UniMsg_HomeProc:array<boolean>,
N0:nat,src:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_HeadPtr.Length==N0
requires Sta_Dir_HeadVld.Length==N0
requires Sta_Dir_HomeHeadPtr.Length==N0
requires Sta_Dir_HomeInvSet.Length==N0
requires Sta_Dir_HomeShrSet.Length==N0
requires Sta_Dir_InvSet.Length==N0

requires Sta_Dir_Local.Length==N0
requires Sta_Dir_Pending.Length==N0
requires Sta_Dir_ShrSet.Length==N0
requires Sta_Dir_ShrVld.Length==N0
requires Sta_HomeInvMsg_Cmd.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_InvMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_UniMsg_Cmd.Length==N0

requires Sta_UniMsg_HomeProc.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_HeadPtr.Length&&0<=j<Sta_Dir_HeadPtr.Length==>Sta_Dir_HeadPtr[i]!=Sta_Dir_HeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HeadVld.Length&&0<=j<Sta_Dir_HeadVld.Length==>Sta_Dir_HeadVld[i]!=Sta_Dir_HeadVld[j]
requires forall i,j::0<=i<Sta_Dir_HomeHeadPtr.Length&&0<=j<Sta_Dir_HomeHeadPtr.Length==>Sta_Dir_HomeHeadPtr[i]!=Sta_Dir_HomeHeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HomeInvSet.Length&&0<=j<Sta_Dir_HomeInvSet.Length==>Sta_Dir_HomeInvSet[i]!=Sta_Dir_HomeInvSet[j]
requires forall i,j::0<=i<Sta_Dir_HomeShrSet.Length&&0<=j<Sta_Dir_HomeShrSet.Length==>Sta_Dir_HomeShrSet[i]!=Sta_Dir_HomeShrSet[j]
requires forall i,j::0<=i<Sta_Dir_InvSet.Length&&0<=j<Sta_Dir_InvSet.Length==>Sta_Dir_InvSet[i]!=Sta_Dir_InvSet[j]

requires forall i,j::0<=i<Sta_Dir_Local.Length&&0<=j<Sta_Dir_Local.Length==>Sta_Dir_Local[i]!=Sta_Dir_Local[j]
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_Dir_ShrSet.Length&&0<=j<Sta_Dir_ShrSet.Length==>Sta_Dir_ShrSet[i]!=Sta_Dir_ShrSet[j]
requires forall i,j::0<=i<Sta_Dir_ShrVld.Length&&0<=j<Sta_Dir_ShrVld.Length==>Sta_Dir_ShrVld[i]!=Sta_Dir_ShrVld[j]
requires forall i,j::0<=i<Sta_HomeInvMsg_Cmd.Length&&0<=j<Sta_HomeInvMsg_Cmd.Length==>Sta_HomeInvMsg_Cmd[i]!=Sta_HomeInvMsg_Cmd[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_InvMsg_Cmd.Length&&0<=j<Sta_InvMsg_Cmd.Length==>Sta_InvMsg_Cmd[i]!=Sta_InvMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_UniMsg_Cmd.Length&&0<=j<Sta_UniMsg_Cmd.Length==>Sta_UniMsg_Cmd[i]!=Sta_UniMsg_Cmd[j]

requires forall i,j::0<=i<Sta_UniMsg_HomeProc.Length&&0<=j<Sta_UniMsg_HomeProc.Length==>Sta_UniMsg_HomeProc[i]!=Sta_UniMsg_HomeProc[j]
requires 0<=src<N0

requires ((Sta_Dir_Dirty[0] == false) && (Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HomeHeadPtr[0] == false) && (Sta_Dir_HomeShrSet[0] == true) && (Sta_Dir_Local[0] == false) && (Sta_Dir_Pending[0] == false) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true)) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd

{
  Sta_Dir_Pending[0] := true;
  Sta_Dir_Local[0] := false;
  Sta_Dir_Dirty[0] := true;
  Sta_Dir_HeadVld[0] := true;
  Sta_Dir_HeadPtr[0] := src;
  Sta_Dir_HomeHeadPtr[0] := false;
  Sta_Dir_ShrVld[0] := false;
  var p:=0;
  while(p<N0)
    decreases N0-p
 {
    Sta_Dir_ShrSet[p] := false;
    if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
      Sta_Dir_InvSet[p] := true;
      Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
      Sta_Dir_InvSet[p] := false;
      Sta_InvMsg_Cmd[p] := INV_None;
    }
  
 p:=p+1;
}
  Sta_Dir_HomeShrSet[0] := false;
  Sta_Dir_HomeInvSet[0] := false;
  Sta_HomeInvMsg_Cmd[0] := INV_None;
  Sta_UniMsg_Cmd[src] := UNI_PutX;
}


method n_NI_InvAck_2inv__90_0(Sta_Dir_HomeInvSet:array<boolean>,   Sta_Dir_InvSet:array<boolean>,       Sta_Dir_Local:array<boolean>, Sta_Dir_Pending:array<boolean>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_InvMsg_Cmd:array<INV_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>,
N0:nat,src:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_Dir_HomeInvSet.Length==N0


requires Sta_Dir_InvSet.Length==N0






requires Sta_Dir_Local.Length==N0
requires Sta_Dir_Pending.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_InvMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires forall i,j::0<=i<Sta_Dir_HomeInvSet.Length&&0<=j<Sta_Dir_HomeInvSet.Length==>Sta_Dir_HomeInvSet[i]!=Sta_Dir_HomeInvSet[j]


requires forall i,j::0<=i<Sta_Dir_InvSet.Length&&0<=j<Sta_Dir_InvSet.Length==>Sta_Dir_InvSet[i]!=Sta_Dir_InvSet[j]






requires forall i,j::0<=i<Sta_Dir_Local.Length&&0<=j<Sta_Dir_Local.Length==>Sta_Dir_Local[i]!=Sta_Dir_Local[j]
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_InvMsg_Cmd.Length&&0<=j<Sta_InvMsg_Cmd.Length==>Sta_InvMsg_Cmd[i]!=Sta_InvMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires 0<=src<N0

requires ((Sta_Dir_HomeInvSet[0] == false) && (Sta_Dir_InvSet[src] == true) && (Sta_Dir_Local[0] == false) && (Sta_Dir_Pending[0] == true) && (Sta_InvMsg_Cmd[src] == INV_InvAck) && (forall p  |0<= p<N0 :: ((Sta_Dir_InvSet[p] == false) || (p == src)) )) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_InvSet
modifies Sta_Dir_Pending
modifies Sta_InvMsg_Cmd

{
  Sta_InvMsg_Cmd[src] := INV_None;
  Sta_Dir_InvSet[src] := false;
  Sta_Dir_Pending[0] := false;
}



method n_PI_Local_GetX_PutX_HeadVld__part__1inv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_HeadPtr:array<NODE>, Sta_Dir_HeadVld:array<boolean>, Sta_Dir_HomeHeadPtr:array<boolean>, Sta_Dir_HomeInvSet:array<boolean>, Sta_Dir_HomeShrSet:array<boolean>, Sta_Dir_InvSet:array<boolean>,  Sta_Dir_Local:array<boolean>, Sta_Dir_Pending:array<boolean>, Sta_Dir_ShrSet:array<boolean>, Sta_Dir_ShrVld:array<boolean>, Sta_HomeInvMsg_Cmd:array<INV_CMD>, Sta_HomeProc_CacheState:array<CACHE_STATE>, Sta_HomeProc_InvMarked:array<boolean>, Sta_HomeProc_ProcCmd:array<NODE_CMD>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_InvMsg_Cmd:array<INV_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>,
N0:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0
requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_HeadPtr.Length==N0
requires Sta_Dir_HeadVld.Length==N0
requires Sta_Dir_HomeHeadPtr.Length==N0
requires Sta_Dir_HomeInvSet.Length==N0
requires Sta_Dir_HomeShrSet.Length==N0
requires Sta_Dir_InvSet.Length==N0

requires Sta_Dir_Local.Length==N0
requires Sta_Dir_Pending.Length==N0
requires Sta_Dir_ShrSet.Length==N0
requires Sta_Dir_ShrVld.Length==N0
requires Sta_HomeInvMsg_Cmd.Length==N0
requires Sta_HomeProc_CacheState.Length==N0
requires Sta_HomeProc_InvMarked.Length==N0
requires Sta_HomeProc_ProcCmd.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_InvMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_HeadPtr.Length&&0<=j<Sta_Dir_HeadPtr.Length==>Sta_Dir_HeadPtr[i]!=Sta_Dir_HeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HeadVld.Length&&0<=j<Sta_Dir_HeadVld.Length==>Sta_Dir_HeadVld[i]!=Sta_Dir_HeadVld[j]
requires forall i,j::0<=i<Sta_Dir_HomeHeadPtr.Length&&0<=j<Sta_Dir_HomeHeadPtr.Length==>Sta_Dir_HomeHeadPtr[i]!=Sta_Dir_HomeHeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HomeInvSet.Length&&0<=j<Sta_Dir_HomeInvSet.Length==>Sta_Dir_HomeInvSet[i]!=Sta_Dir_HomeInvSet[j]
requires forall i,j::0<=i<Sta_Dir_HomeShrSet.Length&&0<=j<Sta_Dir_HomeShrSet.Length==>Sta_Dir_HomeShrSet[i]!=Sta_Dir_HomeShrSet[j]
requires forall i,j::0<=i<Sta_Dir_InvSet.Length&&0<=j<Sta_Dir_InvSet.Length==>Sta_Dir_InvSet[i]!=Sta_Dir_InvSet[j]

requires forall i,j::0<=i<Sta_Dir_Local.Length&&0<=j<Sta_Dir_Local.Length==>Sta_Dir_Local[i]!=Sta_Dir_Local[j]
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_Dir_ShrSet.Length&&0<=j<Sta_Dir_ShrSet.Length==>Sta_Dir_ShrSet[i]!=Sta_Dir_ShrSet[j]
requires forall i,j::0<=i<Sta_Dir_ShrVld.Length&&0<=j<Sta_Dir_ShrVld.Length==>Sta_Dir_ShrVld[i]!=Sta_Dir_ShrVld[j]
requires forall i,j::0<=i<Sta_HomeInvMsg_Cmd.Length&&0<=j<Sta_HomeInvMsg_Cmd.Length==>Sta_HomeInvMsg_Cmd[i]!=Sta_HomeInvMsg_Cmd[j]
requires forall i,j::0<=i<Sta_HomeProc_CacheState.Length&&0<=j<Sta_HomeProc_CacheState.Length==>Sta_HomeProc_CacheState[i]!=Sta_HomeProc_CacheState[j]
requires forall i,j::0<=i<Sta_HomeProc_InvMarked.Length&&0<=j<Sta_HomeProc_InvMarked.Length==>Sta_HomeProc_InvMarked[i]!=Sta_HomeProc_InvMarked[j]
requires forall i,j::0<=i<Sta_HomeProc_ProcCmd.Length&&0<=j<Sta_HomeProc_ProcCmd.Length==>Sta_HomeProc_ProcCmd[i]!=Sta_HomeProc_ProcCmd[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_InvMsg_Cmd.Length&&0<=j<Sta_InvMsg_Cmd.Length==>Sta_InvMsg_Cmd[i]!=Sta_InvMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
//guard condition
requires   ((Sta_Dir_Dirty[0] == false) && (Sta_Dir_HeadVld[0] == true) && (Sta_Dir_Pending[0] == false) && (Sta_HomeProc_ProcCmd[0] == NODE_None) && (Sta_HomeProc_CacheState[0] == CACHE_S))
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_HomeProc_ProcCmd
modifies Sta_InvMsg_Cmd
{
  Sta_Dir_Local[0] := true;
  Sta_Dir_Dirty[0] := true;
  Sta_Dir_Pending[0] := true;
  Sta_Dir_HeadVld[0] := false;
  Sta_Dir_ShrVld[0] := false;
  var p:=0;
  while(p<N0)
    decreases N0-p
 {
    Sta_Dir_ShrSet[p] := false;
    if (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || ((Sta_Dir_HeadPtr[0] == p) && (Sta_Dir_HomeHeadPtr[0] == false))) {
      Sta_Dir_InvSet[p] := true;
      Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
      Sta_Dir_InvSet[p] := false;
      Sta_InvMsg_Cmd[p] := INV_None;
    }
  
 p:=p+1;
}
  Sta_Dir_HomeShrSet[0] := false;
  Sta_Dir_HomeInvSet[0] := false;
  Sta_HomeInvMsg_Cmd[0] := INV_None;
  Sta_HomeProc_ProcCmd[0] := NODE_None;
  Sta_HomeProc_InvMarked[0] := false;
  Sta_HomeProc_CacheState[0] := CACHE_E;
}


method n_NI_FAckinv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_HeadPtr:array<NODE>, Sta_Dir_HomeHeadPtr:array<boolean>, Sta_Dir_Pending:array<boolean>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_ShWbMsg_Cmd:array<SHWB_CMD>, Sta_ShWbMsg_HomeProc:array<boolean>, Sta_ShWbMsg_Proc:array<NODE>,
N0:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0
requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_HeadPtr.Length==N0
requires Sta_Dir_HomeHeadPtr.Length==N0
requires Sta_Dir_Pending.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_ShWbMsg_Cmd.Length==N0
requires Sta_ShWbMsg_HomeProc.Length==N0
requires Sta_ShWbMsg_Proc.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_HeadPtr.Length&&0<=j<Sta_Dir_HeadPtr.Length==>Sta_Dir_HeadPtr[i]!=Sta_Dir_HeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HomeHeadPtr.Length&&0<=j<Sta_Dir_HomeHeadPtr.Length==>Sta_Dir_HomeHeadPtr[i]!=Sta_Dir_HomeHeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_ShWbMsg_Cmd.Length&&0<=j<Sta_ShWbMsg_Cmd.Length==>Sta_ShWbMsg_Cmd[i]!=Sta_ShWbMsg_Cmd[j]
requires forall i,j::0<=i<Sta_ShWbMsg_HomeProc.Length&&0<=j<Sta_ShWbMsg_HomeProc.Length==>Sta_ShWbMsg_HomeProc[i]!=Sta_ShWbMsg_HomeProc[j]
requires forall i,j::0<=i<Sta_ShWbMsg_Proc.Length&&0<=j<Sta_ShWbMsg_Proc.Length==>Sta_ShWbMsg_Proc[i]!=Sta_ShWbMsg_Proc[j]
//guard condition
requires   (Sta_ShWbMsg_Cmd[0] == SHWB_FAck)
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_Pending
modifies Sta_ShWbMsg_Cmd
modifies Sta_ShWbMsg_HomeProc
modifies Sta_ShWbMsg_Proc
{
  Sta_ShWbMsg_Cmd[0] := SHWB_None;
  Sta_Dir_Pending[0] := false;
  if (Sta_Dir_Dirty[0] == true) {
    Sta_Dir_HeadPtr[0] := Sta_ShWbMsg_Proc[0];
    Sta_Dir_HomeHeadPtr[0] := Sta_ShWbMsg_HomeProc[0];
  }
}

method n_NI_Local_GetX_PutX_4inv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_HeadPtr:array<NODE>, Sta_Dir_HeadVld:array<boolean>, Sta_Dir_HomeHeadPtr:array<boolean>, Sta_Dir_HomeInvSet:array<boolean>, Sta_Dir_HomeShrSet:array<boolean>, Sta_Dir_InvSet:array<boolean>,  Sta_Dir_Local:array<boolean>, Sta_Dir_Pending:array<boolean>, Sta_Dir_ShrSet:array<boolean>,      Sta_Dir_ShrVld:array<boolean>, Sta_HomeProc_CacheState:array<CACHE_STATE>, Sta_HomeProc_InvMarked:array<boolean>, Sta_HomeProc_ProcCmd:array<NODE_CMD>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_UniMsg_Cmd:array<UNI_CMD>,  Sta_UniMsg_HomeProc:array<boolean>,
N0:nat,src:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_HeadPtr.Length==N0
requires Sta_Dir_HeadVld.Length==N0
requires Sta_Dir_HomeHeadPtr.Length==N0
requires Sta_Dir_HomeInvSet.Length==N0
requires Sta_Dir_HomeShrSet.Length==N0
requires Sta_Dir_InvSet.Length==N0

requires Sta_Dir_Local.Length==N0
requires Sta_Dir_Pending.Length==N0
requires Sta_Dir_ShrSet.Length==N0





requires Sta_Dir_ShrVld.Length==N0
requires Sta_HomeProc_CacheState.Length==N0
requires Sta_HomeProc_InvMarked.Length==N0
requires Sta_HomeProc_ProcCmd.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_UniMsg_Cmd.Length==N0

requires Sta_UniMsg_HomeProc.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_HeadPtr.Length&&0<=j<Sta_Dir_HeadPtr.Length==>Sta_Dir_HeadPtr[i]!=Sta_Dir_HeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HeadVld.Length&&0<=j<Sta_Dir_HeadVld.Length==>Sta_Dir_HeadVld[i]!=Sta_Dir_HeadVld[j]
requires forall i,j::0<=i<Sta_Dir_HomeHeadPtr.Length&&0<=j<Sta_Dir_HomeHeadPtr.Length==>Sta_Dir_HomeHeadPtr[i]!=Sta_Dir_HomeHeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HomeInvSet.Length&&0<=j<Sta_Dir_HomeInvSet.Length==>Sta_Dir_HomeInvSet[i]!=Sta_Dir_HomeInvSet[j]
requires forall i,j::0<=i<Sta_Dir_HomeShrSet.Length&&0<=j<Sta_Dir_HomeShrSet.Length==>Sta_Dir_HomeShrSet[i]!=Sta_Dir_HomeShrSet[j]
requires forall i,j::0<=i<Sta_Dir_InvSet.Length&&0<=j<Sta_Dir_InvSet.Length==>Sta_Dir_InvSet[i]!=Sta_Dir_InvSet[j]

requires forall i,j::0<=i<Sta_Dir_Local.Length&&0<=j<Sta_Dir_Local.Length==>Sta_Dir_Local[i]!=Sta_Dir_Local[j]
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_Dir_ShrSet.Length&&0<=j<Sta_Dir_ShrSet.Length==>Sta_Dir_ShrSet[i]!=Sta_Dir_ShrSet[j]





requires forall i,j::0<=i<Sta_Dir_ShrVld.Length&&0<=j<Sta_Dir_ShrVld.Length==>Sta_Dir_ShrVld[i]!=Sta_Dir_ShrVld[j]
requires forall i,j::0<=i<Sta_HomeProc_CacheState.Length&&0<=j<Sta_HomeProc_CacheState.Length==>Sta_HomeProc_CacheState[i]!=Sta_HomeProc_CacheState[j]
requires forall i,j::0<=i<Sta_HomeProc_InvMarked.Length&&0<=j<Sta_HomeProc_InvMarked.Length==>Sta_HomeProc_InvMarked[i]!=Sta_HomeProc_InvMarked[j]
requires forall i,j::0<=i<Sta_HomeProc_ProcCmd.Length&&0<=j<Sta_HomeProc_ProcCmd.Length==>Sta_HomeProc_ProcCmd[i]!=Sta_HomeProc_ProcCmd[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_UniMsg_Cmd.Length&&0<=j<Sta_UniMsg_Cmd.Length==>Sta_UniMsg_Cmd[i]!=Sta_UniMsg_Cmd[j]

requires forall i,j::0<=i<Sta_UniMsg_HomeProc.Length&&0<=j<Sta_UniMsg_HomeProc.Length==>Sta_UniMsg_HomeProc[i]!=Sta_UniMsg_HomeProc[j]
requires 0<=src<N0

requires ((Sta_Dir_Dirty[0] == false) && (Sta_Dir_HeadPtr[0] == src) && (Sta_Dir_HomeHeadPtr[0] == false) && (Sta_Dir_HomeShrSet[0] == false) && (Sta_Dir_Local[0] == true) && (Sta_Dir_Pending[0] == false) && (Sta_HomeProc_ProcCmd[0] == NODE_Get) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (forall p  |0<= p<N0 :: ((Sta_Dir_ShrSet[p] == false) || (p == src)) )) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_UniMsg_Cmd

{
  Sta_Dir_Local[0] := false;
  Sta_Dir_Dirty[0] := true;
  Sta_Dir_HeadVld[0] := true;
  Sta_Dir_HeadPtr[0] := src;
  Sta_Dir_HomeHeadPtr[0] := false;
  Sta_Dir_ShrVld[0] := false;
  var p:=0;
  while(p<N0)
    decreases N0-p
 {
    Sta_Dir_ShrSet[p] := false;
    Sta_Dir_InvSet[p] := false;
  
 p:=p+1;
}
  Sta_Dir_HomeShrSet[0] := false;
  Sta_Dir_HomeInvSet[0] := false;
  Sta_UniMsg_Cmd[src] := UNI_PutX;
  Sta_HomeProc_CacheState[0] := CACHE_I;
  Sta_HomeProc_InvMarked[0] := true;
}


method n_NI_Local_GetX_PutX_7_NODE_Get__part__0inv__90_0(Sta_Dir_Dirty:array<boolean>,   Sta_Dir_HeadPtr:array<NODE>, Sta_Dir_HeadVld:array<boolean>, Sta_Dir_HomeHeadPtr:array<boolean>, Sta_Dir_HomeInvSet:array<boolean>, Sta_Dir_HomeShrSet:array<boolean>, Sta_Dir_InvSet:array<boolean>,  Sta_Dir_Local:array<boolean>, Sta_Dir_Pending:array<boolean>, Sta_Dir_ShrSet:array<boolean>, Sta_Dir_ShrVld:array<boolean>, Sta_HomeInvMsg_Cmd:array<INV_CMD>, Sta_HomeProc_CacheState:array<CACHE_STATE>, Sta_HomeProc_InvMarked:array<boolean>, Sta_HomeProc_ProcCmd:array<NODE_CMD>, Sta_HomeUniMsg_Cmd:array<UNI_CMD>, Sta_InvMsg_Cmd:array<INV_CMD>, Sta_NakcMsg_Cmd:array<NAKC_CMD>, Sta_UniMsg_Cmd:array<UNI_CMD>,  Sta_UniMsg_HomeProc:array<boolean>,
N0:nat,src:nat,
p__Inv0:nat,p__Inv2:nat)
requires N0>0

requires Sta_Dir_Dirty.Length==N0


requires Sta_Dir_HeadPtr.Length==N0
requires Sta_Dir_HeadVld.Length==N0
requires Sta_Dir_HomeHeadPtr.Length==N0
requires Sta_Dir_HomeInvSet.Length==N0
requires Sta_Dir_HomeShrSet.Length==N0
requires Sta_Dir_InvSet.Length==N0

requires Sta_Dir_Local.Length==N0
requires Sta_Dir_Pending.Length==N0
requires Sta_Dir_ShrSet.Length==N0
requires Sta_Dir_ShrVld.Length==N0
requires Sta_HomeInvMsg_Cmd.Length==N0
requires Sta_HomeProc_CacheState.Length==N0
requires Sta_HomeProc_InvMarked.Length==N0
requires Sta_HomeProc_ProcCmd.Length==N0
requires Sta_HomeUniMsg_Cmd.Length==N0
requires Sta_InvMsg_Cmd.Length==N0
requires Sta_NakcMsg_Cmd.Length==N0
requires Sta_UniMsg_Cmd.Length==N0

requires Sta_UniMsg_HomeProc.Length==N0
requires forall i,j::0<=i<Sta_Dir_Dirty.Length&&0<=j<Sta_Dir_Dirty.Length==>Sta_Dir_Dirty[i]!=Sta_Dir_Dirty[j]


requires forall i,j::0<=i<Sta_Dir_HeadPtr.Length&&0<=j<Sta_Dir_HeadPtr.Length==>Sta_Dir_HeadPtr[i]!=Sta_Dir_HeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HeadVld.Length&&0<=j<Sta_Dir_HeadVld.Length==>Sta_Dir_HeadVld[i]!=Sta_Dir_HeadVld[j]
requires forall i,j::0<=i<Sta_Dir_HomeHeadPtr.Length&&0<=j<Sta_Dir_HomeHeadPtr.Length==>Sta_Dir_HomeHeadPtr[i]!=Sta_Dir_HomeHeadPtr[j]
requires forall i,j::0<=i<Sta_Dir_HomeInvSet.Length&&0<=j<Sta_Dir_HomeInvSet.Length==>Sta_Dir_HomeInvSet[i]!=Sta_Dir_HomeInvSet[j]
requires forall i,j::0<=i<Sta_Dir_HomeShrSet.Length&&0<=j<Sta_Dir_HomeShrSet.Length==>Sta_Dir_HomeShrSet[i]!=Sta_Dir_HomeShrSet[j]
requires forall i,j::0<=i<Sta_Dir_InvSet.Length&&0<=j<Sta_Dir_InvSet.Length==>Sta_Dir_InvSet[i]!=Sta_Dir_InvSet[j]

requires forall i,j::0<=i<Sta_Dir_Local.Length&&0<=j<Sta_Dir_Local.Length==>Sta_Dir_Local[i]!=Sta_Dir_Local[j]
requires forall i,j::0<=i<Sta_Dir_Pending.Length&&0<=j<Sta_Dir_Pending.Length==>Sta_Dir_Pending[i]!=Sta_Dir_Pending[j]
requires forall i,j::0<=i<Sta_Dir_ShrSet.Length&&0<=j<Sta_Dir_ShrSet.Length==>Sta_Dir_ShrSet[i]!=Sta_Dir_ShrSet[j]
requires forall i,j::0<=i<Sta_Dir_ShrVld.Length&&0<=j<Sta_Dir_ShrVld.Length==>Sta_Dir_ShrVld[i]!=Sta_Dir_ShrVld[j]
requires forall i,j::0<=i<Sta_HomeInvMsg_Cmd.Length&&0<=j<Sta_HomeInvMsg_Cmd.Length==>Sta_HomeInvMsg_Cmd[i]!=Sta_HomeInvMsg_Cmd[j]
requires forall i,j::0<=i<Sta_HomeProc_CacheState.Length&&0<=j<Sta_HomeProc_CacheState.Length==>Sta_HomeProc_CacheState[i]!=Sta_HomeProc_CacheState[j]
requires forall i,j::0<=i<Sta_HomeProc_InvMarked.Length&&0<=j<Sta_HomeProc_InvMarked.Length==>Sta_HomeProc_InvMarked[i]!=Sta_HomeProc_InvMarked[j]
requires forall i,j::0<=i<Sta_HomeProc_ProcCmd.Length&&0<=j<Sta_HomeProc_ProcCmd.Length==>Sta_HomeProc_ProcCmd[i]!=Sta_HomeProc_ProcCmd[j]
requires forall i,j::0<=i<Sta_HomeUniMsg_Cmd.Length&&0<=j<Sta_HomeUniMsg_Cmd.Length==>Sta_HomeUniMsg_Cmd[i]!=Sta_HomeUniMsg_Cmd[j]
requires forall i,j::0<=i<Sta_InvMsg_Cmd.Length&&0<=j<Sta_InvMsg_Cmd.Length==>Sta_InvMsg_Cmd[i]!=Sta_InvMsg_Cmd[j]
requires forall i,j::0<=i<Sta_NakcMsg_Cmd.Length&&0<=j<Sta_NakcMsg_Cmd.Length==>Sta_NakcMsg_Cmd[i]!=Sta_NakcMsg_Cmd[j]
requires forall i,j::0<=i<Sta_UniMsg_Cmd.Length&&0<=j<Sta_UniMsg_Cmd.Length==>Sta_UniMsg_Cmd[i]!=Sta_UniMsg_Cmd[j]

requires forall i,j::0<=i<Sta_UniMsg_HomeProc.Length&&0<=j<Sta_UniMsg_HomeProc.Length==>Sta_UniMsg_HomeProc[i]!=Sta_UniMsg_HomeProc[j]
requires 0<=src<N0

requires ((Sta_Dir_Dirty[0] == false) && (Sta_Dir_HeadVld[0] == true) && (Sta_Dir_Local[0] == true) && (Sta_Dir_Pending[0] == false) && (Sta_HomeProc_ProcCmd[0] == NODE_Get) && (Sta_UniMsg_Cmd[src] == UNI_GetX) && (Sta_UniMsg_HomeProc[src] == true) && (Sta_Dir_HomeHeadPtr[0] == true)) //guard condition
ensures   (!((Sta_HomeUniMsg_Cmd[0] == UNI_Get) && (Sta_NakcMsg_Cmd[0] == NAKC_Nakc)))
modifies Sta_Dir_Dirty
modifies Sta_Dir_HeadPtr
modifies Sta_Dir_HeadVld
modifies Sta_Dir_HomeHeadPtr
modifies Sta_Dir_HomeInvSet
modifies Sta_Dir_HomeShrSet
modifies Sta_Dir_InvSet
modifies Sta_Dir_Local
modifies Sta_Dir_Pending
modifies Sta_Dir_ShrSet
modifies Sta_Dir_ShrVld
modifies Sta_HomeInvMsg_Cmd
modifies Sta_HomeProc_CacheState
modifies Sta_HomeProc_InvMarked
modifies Sta_InvMsg_Cmd
modifies Sta_UniMsg_Cmd

{
  Sta_Dir_Pending[0] := true;
  Sta_Dir_Local[0] := false;
  Sta_Dir_Dirty[0] := true;
  Sta_Dir_HeadVld[0] := true;
  Sta_Dir_HeadPtr[0] := src;
  Sta_Dir_HomeHeadPtr[0] := false;
  Sta_Dir_ShrVld[0] := false;
  var p:=0;
  while(p<N0)
    decreases N0-p
 {
    Sta_Dir_ShrSet[p] := false;
    if ((!(p == src)) && (((Sta_Dir_ShrVld[0] == true) && (Sta_Dir_ShrSet[p] == true)) || (((Sta_Dir_HeadVld[0] == true) && (Sta_Dir_HeadPtr[0] == p)) && (Sta_Dir_HomeHeadPtr[0] == false)))) {
      Sta_Dir_InvSet[p] := true;
      Sta_InvMsg_Cmd[p] := INV_Inv;}
else{
      Sta_Dir_InvSet[p] := false;
      Sta_InvMsg_Cmd[p] := INV_None;
    }
  
 p:=p+1;
}
  Sta_Dir_HomeShrSet[0] := false;
  Sta_Dir_HomeInvSet[0] := false;
  Sta_HomeInvMsg_Cmd[0] := INV_None;
  Sta_UniMsg_Cmd[src] := UNI_PutX;
  Sta_HomeProc_CacheState[0] := CACHE_I;
  Sta_HomeProc_InvMarked[0] := true;
}


