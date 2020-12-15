type role = string
datatype message = Nil | Aenc(aencMsg:message,aencKey:message) | Senc(m1:message,m2:message) | K(r1:role,r2:role) | Pk(r:role) | Sk(r:role) | Str(r:role) | Var(n:role) | Concat(array<message>)
type channel = array<message>

method ReceiveMsgFromChannel(c:channel,m1:message,is:array<message>) returns (m:message)//take message from channel
    requires c.Length > 0 
    requires m1!=Nil  
    requires m1 == c[0]
    requires forall i:int :: 0<=i<is.Length ==> is[i]!=Var("Na")
    ensures forall i:int :: 0<=i<is.Length ==> is[i]!=Var("Na")
    ensures m1 == m
    ensures c[0] == Nil
    modifies c
{
    c[0]:=Nil;
    m:=m1;
}
method SendMsgToChannel(c:channel,m:message,is:array<message>)//put the message into channel
    requires c.Length > 0 
    requires c!=is
    requires forall i:int :: 0<=i<is.Length ==> is[i]!=Var("Na")
    ensures forall i:int :: 0<=i<is.Length ==> is[i]!=Var("Na")
    ensures  c[0] == m
    modifies c
{
    c[0] := m;
}
method AliceSendMsg_1(c:channel,is:array<message>)//Alice sends the first message into channel
    requires c.Length > 0
    requires c!=is
    requires forall i:int :: 0<=i<is.Length ==> is[i]!=Var("Na")
    ensures forall i:int :: 0<=i<is.Length ==> is[i]!=Var("Na")
    ensures  c[0]!=Nil
    modifies c
{
    var aencMsg:=new message[2];    
    aencMsg[0]:=Var("Na");
    aencMsg[1]:=Str("A");
    var m :=Aenc(Concat(aencMsg),Pk("B")); 
    c[0] := m;
}
method AliceSendMsg_2(c:channel,is:array<message>)//Alice sends the second message into channel
    requires c.Length > 0
    requires c.Length > 0
    requires c!=is
    requires forall i:int :: 0<=i<is.Length ==> is[i]!=Var("Na")
    ensures forall i:int :: 0<=i<is.Length ==> is[i]!=Var("Na")
    ensures c[0]!=Nil
    modifies c
{
    var aencMsg:=Var("Nb");
    var m :=Aenc(aencMsg,Pk("B"));
    c[0] :=m;
}
method BobSendMsg_1(c:channel,is:array<message>)//Bob sends the first message into channel
    requires c.Length > 0
    requires c!=is
    requires forall i:int :: 0<=i<is.Length ==> is[i]!=Var("Na")
    ensures forall i:int :: 0<=i<is.Length ==> is[i]!=Var("Na")
    ensures c[0] != Nil
    modifies c
{
    var aencMsg:=new message[2];
    aencMsg[0]:=Var("Na");
    aencMsg[1]:=Var("Nb");
    var m :=Aenc(Concat(aencMsg),Pk("A"));
    c[0] :=m;
}

 method AliceGetMsg_1(c:array<message>,is:array<message>) returns (m:message)//Alice receives the first message from channel
    requires c.Length > 0 
    requires c!=is
    requires nverify(c[0])
    requires forall i:int :: 0<=i<is.Length ==> is[i]!=Var("Na")
    ensures forall i:int :: 0<=i<is.Length ==> is[i]!=Var("Na")
    ensures c[0]==Nil
    ensures m!=Nil
    modifies c
 {
     m:=c[0];
     c[0]:=Nil;
 }
  method BobGetMsg_1(c:array<message>,is:array<message>) returns (m:message)//Bob receives the first message from channel
    requires c.Length > 0 
    requires c!=is
    requires nverify(c[0])
    requires forall i:int :: 0<=i<is.Length ==> is[i]!=Var("Na")
    ensures forall i:int :: 0<=i<is.Length ==> is[i]!=Var("Na")
    ensures c[0]==Nil
    ensures m!=Nil
    modifies c
 {
     m:=c[0];
     c[0]:=Nil;
 }
  method BobGetMsg_2(c:array<message>,is:array<message>) returns (m:message)//Bob receives the third message from channel
    requires c.Length > 0 
    requires c!=is
    requires nverify(c[0])
    requires forall i:int :: 0<=i<is.Length ==> is[i]!=Var("Na")
    ensures forall i:int :: 0<=i<is.Length ==> is[i]!=Var("Na")
    ensures c[0]==Nil
    ensures m!=Nil
    modifies c
 {
     m:=c[0];
     c[0]:=Nil;
 }
method IntruderGetMsg(c:channel,is:array<message>,i:int)//intruder intercepts the message in channel and insert it into intruder knowledge databases.
    requires c.Length > 0
    requires c!=is
    requires iverify(c[0])
    requires forall i:int :: 0<=i<is.Length ==> is[i]!=Var("Na")
    // ensures forall i:int :: 0<=i<is.Length ==> is[i]!=Var("Na")
    ensures c[0] == Nil
    modifies c,is
{   
    var aencMsg := destruct(c[0]);
    var i:=0;
    while(i<is.Length)
    {
        if(is[i]==Nil){
            is[i]:=aencMsg;
        break;
        }
        i:=i+1;
    }
    c[0]:=Nil;
}
 
predicate  nverify(m:message)//Alice or Bob verify Message received
{
    match m
    case Nil => false
    case Aenc(aencMsg,aencKey) => if aencKey == message.Pk("B") || aencKey == message.Pk("A") then true  else false
    case Senc(m1,m2)=> false
    case Var(r1)=> false
    case Str(r1)=> false
    case Pk(r1) => false
    case Sk(r1) => false
    case K(r1,r2)=>false
    case Concat(ms) => false
 }
  predicate  iverify(m:message)//Intruder verify message received
{
    match m
    case Nil => false
    case Aenc(aencMsg,aencKey) => if aencKey == message.Pk("I") then true  else false
    case Senc(m1,m2)=> true
    case Var(r1)=> false
    case Str(r1)=> true
    case Pk(r1) => true
    case Sk(r1) => true
    case K(r1,r2)=>true
    case Concat(ms) => true
 }

function method  destruct(m:message):message//Destruct the message into submessage
{
    match m
    case Nil => Nil
    case Aenc(aencMsg,aencKey) => if aencKey == message.Pk("I") then aencMsg  else Aenc(aencMsg,aencKey)
    case Senc(m1,m2)=>Senc(m1,m2)
    case Var(r1)=> Var(r1)
    case Str(r1)=> Str(r1)
    case Pk(r1) => Pk(r1)
    case Sk(r1) => Sk(r1)
    case K(r1,r2)=>K(r1,r2)
    case Concat(ms) => Concat(ms)
 }


  method Main()
{
    var c:=new message[1];
    c[0]:=Pk("B");
    var aencMsg:=new message[2];
    assert aencMsg != c ;
    var is:=new message[5];
    assert is != aencMsg;
    var i:=0;
    while(i<is.Length)
    {
        is[i]:=Nil;
        i:=i+1;
    }    
    var j:=0;
    while(j<is.Length)
    decreases is.Length -j
    {
        print is[j],"\n";
        j:=j+1;
    }

    // assert  forall i:int :: 0<=i<is.Length ==> is[i]==message.Nil;
    aencMsg[0]:=Var("Na");
    aencMsg[1]:=Str("A");
    var m1 :=Aenc(Concat(aencMsg),Pk("B"));    
    // SendMsgToChannel(c,m,is);
    // var m1:=AliceGetMsg_1(c);
    //     var aencMsg1:=new message[2];
    //     aencMsg1[0]:=Var("Na");
    //     aencMsg1[1]:=Var("Nb");
    //     var m2 :=Aenc(Concat(aencMsg1),Pk("A"));
    //     SendMsgToChannel(c,m2,is);
    //     var m3:=ReceiveMsgFromChannel(c,c[0],is);
    //     if (m3.aencKey == Pk("A")) {
    //         var aencMsg3:=Var("Nb");
    //         var m1:=Aenc((aencMsg3),Pk("B"));
    //         SendMsgToChannel(c,m1,is);
    //         var m4:=ReceiveMsgFromChannel(c,c[0],is);
    // }
}
