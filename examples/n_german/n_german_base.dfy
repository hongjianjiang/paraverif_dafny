//(*  Title:      HOL/Auth/n_german_base.dfy
 //   Author:     Yongjian Li and Kaiqiang Duan, State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
 //   Copyright    2016 State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
//*)

//header{*The n_german Protocol Case Study*} 

//theory n_german_base imports paraTheory
//begin

//section{*Main definitions of dafny  file*}

//subsection{* Definitions of Constants*}

datatype CACHE_STATE = I| S| E
datatype MSG_CMD = Empty| ReqS| ReqE| Inv| InvAck| GntS| GntE
type NODE=nat
type DATA=nat
type boolean=bool

