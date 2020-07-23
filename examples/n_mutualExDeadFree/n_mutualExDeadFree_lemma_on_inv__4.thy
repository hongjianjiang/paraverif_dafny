(*  Title:      HOL/Auth/n_mutualExDeadFree_lemma_on_inv__4.thy
    Author:     Yongjian Li and Kaiqiang Duan, State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
    Copyright    2016 State Key Lab of Computer Science, Institute of Software, Chinese Academy of Sciences
*)

header{*The n_mutualExDeadFree Protocol Case Study*} 

theory n_mutualExDeadFree_lemma_on_inv__4 imports n_mutualExDeadFree_base
begin
section{*All lemmas on causal relation between inv__4 and some rule r*}
lemma n_TryVsinv__4:
assumes a1: "(\<exists> i. i\<le>N\<and>r=n_Try  i)" and
a2: "(\<exists> p__Inv0 p__Inv1 p__Inv2. p__Inv0\<le>N\<and>p__Inv1\<le>N\<and>p__Inv2\<le>N\<and>p__Inv0~=p__Inv1\<and>p__Inv0~=p__Inv2\<and>p__Inv1~=p__Inv2\<and>f=inv__4  p__Inv0 p__Inv1 p__Inv2)"
shows "invHoldForRule s f r (invariants N)" (is "?P1 s \<or> ?P2 s \<or> ?P3 s")
proof -
from a1 obtain i where a1:"i\<le>N\<and>r=n_Try  i" apply fastforce done
from a2 obtain p__Inv0 p__Inv1 p__Inv2 where a2:"p__Inv0\<le>N\<and>p__Inv1\<le>N\<and>p__Inv2\<le>N\<and>p__Inv0~=p__Inv1\<and>p__Inv0~=p__Inv2\<and>p__Inv1~=p__Inv2\<and>f=inv__4  p__Inv0 p__Inv1 p__Inv2" apply fastforce done
have "(i=p__Inv0)\<or>(i=p__Inv1)\<or>(i=p__Inv2)" apply (cut_tac a1 a2, auto) done
moreover {
  assume b1: "(i=p__Inv0)"
  have "?P1 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
moreover {
  assume b1: "(i=p__Inv1)"
  have "?P1 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
moreover {
  assume b1: "(i=p__Inv2)"
  have "?P1 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
ultimately show "invHoldForRule s f r (invariants N)" by satx
qed

lemma n_CritVsinv__4:
assumes a1: "(\<exists> i. i\<le>N\<and>r=n_Crit  i)" and
a2: "(\<exists> p__Inv0 p__Inv1 p__Inv2. p__Inv0\<le>N\<and>p__Inv1\<le>N\<and>p__Inv2\<le>N\<and>p__Inv0~=p__Inv1\<and>p__Inv0~=p__Inv2\<and>p__Inv1~=p__Inv2\<and>f=inv__4  p__Inv0 p__Inv1 p__Inv2)"
shows "invHoldForRule s f r (invariants N)" (is "?P1 s \<or> ?P2 s \<or> ?P3 s")
proof -
from a1 obtain i where a1:"i\<le>N\<and>r=n_Crit  i" apply fastforce done
from a2 obtain p__Inv0 p__Inv1 p__Inv2 where a2:"p__Inv0\<le>N\<and>p__Inv1\<le>N\<and>p__Inv2\<le>N\<and>p__Inv0~=p__Inv1\<and>p__Inv0~=p__Inv2\<and>p__Inv1~=p__Inv2\<and>f=inv__4  p__Inv0 p__Inv1 p__Inv2" apply fastforce done
have "(i=p__Inv0)\<or>(i=p__Inv1)\<or>(i=p__Inv2)" apply (cut_tac a1 a2, auto) done
moreover {
  assume b1: "(i=p__Inv0)"
  have "?P1 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
moreover {
  assume b1: "(i=p__Inv1)"
  have "?P1 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
moreover {
  assume b1: "(i=p__Inv2)"
  have "?P1 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
ultimately show "invHoldForRule s f r (invariants N)" by satx
qed

lemma n_ExitVsinv__4:
assumes a1: "(\<exists> i. i\<le>N\<and>r=n_Exit  i)" and
a2: "(\<exists> p__Inv0 p__Inv1 p__Inv2. p__Inv0\<le>N\<and>p__Inv1\<le>N\<and>p__Inv2\<le>N\<and>p__Inv0~=p__Inv1\<and>p__Inv0~=p__Inv2\<and>p__Inv1~=p__Inv2\<and>f=inv__4  p__Inv0 p__Inv1 p__Inv2)"
shows "invHoldForRule s f r (invariants N)" (is "?P1 s \<or> ?P2 s \<or> ?P3 s")
proof -
from a1 obtain i where a1:"i\<le>N\<and>r=n_Exit  i" apply fastforce done
from a2 obtain p__Inv0 p__Inv1 p__Inv2 where a2:"p__Inv0\<le>N\<and>p__Inv1\<le>N\<and>p__Inv2\<le>N\<and>p__Inv0~=p__Inv1\<and>p__Inv0~=p__Inv2\<and>p__Inv1~=p__Inv2\<and>f=inv__4  p__Inv0 p__Inv1 p__Inv2" apply fastforce done
have "(i=p__Inv0)\<or>(i=p__Inv1)\<or>(i=p__Inv2)" apply (cut_tac a1 a2, auto) done
moreover {
  assume b1: "(i=p__Inv0)"
  have "?P1 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
moreover {
  assume b1: "(i=p__Inv1)"
  have "?P1 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
moreover {
  assume b1: "(i=p__Inv2)"
  have "?P1 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
ultimately show "invHoldForRule s f r (invariants N)" by satx
qed

lemma n_IdleVsinv__4:
assumes a1: "(\<exists> i. i\<le>N\<and>r=n_Idle  i)" and
a2: "(\<exists> p__Inv0 p__Inv1 p__Inv2. p__Inv0\<le>N\<and>p__Inv1\<le>N\<and>p__Inv2\<le>N\<and>p__Inv0~=p__Inv1\<and>p__Inv0~=p__Inv2\<and>p__Inv1~=p__Inv2\<and>f=inv__4  p__Inv0 p__Inv1 p__Inv2)"
shows "invHoldForRule s f r (invariants N)" (is "?P1 s \<or> ?P2 s \<or> ?P3 s")
proof -
from a1 obtain i where a1:"i\<le>N\<and>r=n_Idle  i" apply fastforce done
from a2 obtain p__Inv0 p__Inv1 p__Inv2 where a2:"p__Inv0\<le>N\<and>p__Inv1\<le>N\<and>p__Inv2\<le>N\<and>p__Inv0~=p__Inv1\<and>p__Inv0~=p__Inv2\<and>p__Inv1~=p__Inv2\<and>f=inv__4  p__Inv0 p__Inv1 p__Inv2" apply fastforce done
have "(i=p__Inv0)\<or>(i=p__Inv1)\<or>(i=p__Inv2)" apply (cut_tac a1 a2, auto) done
moreover {
  assume b1: "(i=p__Inv0)"
  have "?P1 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
moreover {
  assume b1: "(i=p__Inv1)"
  have "?P1 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
moreover {
  assume b1: "(i=p__Inv2)"
  have "?P1 s"
  proof(cut_tac a1 a2 b1, auto) qed
  then have "invHoldForRule s f r (invariants N)" by auto
}
ultimately show "invHoldForRule s f r (invariants N)" by satx
qed
end
