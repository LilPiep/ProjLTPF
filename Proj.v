(** Projet LTPF **)

(*
|-------+--------------+--------------|
|       | Bousquet Thomas | Catteau Pierrick |
|-------+--------------+--------------|
| 1.1.1 |              |             x|
| 1.1.2 |              |             x|
| 1.1.3 |              |             x|
| 1.1.4 |              |              |
| 1.2.1 |              |              |
|-------+--------------+--------------|
| 2.1.1 |              |              |
| 2.1.2 |              |              |
| 2.1.3 |              |              |
| 2.1.4 |              |              |
| 2.2.1 |              |              |
| 2.2.2 |              |              |
| 2.3.1 |              |              |
| 2.3.2 |              |              |
| 2.3.3 |              |              |
| 2.4.1 |              |    non traité|
| 2.4.2 |              |    non traité|
| 2.4.3 |              |    non traité|
| 2.4.4 |              |    non traité|
|-------+--------------+--------------|
| 3.1   |              |              |
| 3.2   |              |              |
| 3.3.1 |              |              |
| 3.3.2 |              |              |
| 3.3.3 |              |              |
| 3.4   |              |              |
| 3.5   |              |              |
| 3.6   |              |              |
| 3.7.1 |              |              |
| 3.7.2 |              |              |
| 3.7.3 |              |              |
| 3.7.4 |              |              |
| 3.7.5 |              |              |
| 3.8   |              |              |
| 3.9   |              |              |
|-------+--------------+--------------|
 *)

(** 2.3.1 **)

Theorem reduction_Pcarre_2 : SN (Pcarre_2) [0;0;1] [2;4;5].
Proof.
  cbv [Pcarre_2].
  eapply SN_While_true.
  { cbn. reflexivity. }
  { cbv [corps_carre].
    eapply SN_Seq.
    + apply SN_Assign.
    + cbn. cbv[incrX]. cbv[incrY]. eapply SN_Seq.
    - apply SN_Assign.
    - cbn. apply SN_Assign.
  }
  
  cbn.
  
  eapply SN_While_true.
  cbn. reflexivity.
  { cbv [corps_carre].
    eapply SN_Seq.
    + apply SN_Assign.
    + cbn. cbv[incrX]. cbv[incrY]. eapply SN_Seq.
    - apply SN_Assign.
    - cbn. apply SN_Assign.
  }
  cbn.
  eapply SN_While_false.
  cbn. reflexivity.
Qed.

(** 2.3.2 **)

Lemma SN_SN' : forall i s s1, SN i s s1 -> SN' i s s1.
Proof.
  intros i s s1 sn.
  induction sn as  [ (* SN_Skip *) s
                   | (* SN_Assign *) x s a
                   | (* SN_Seq *) i1 i2 s s1 s' sn1 hrec_sn1 sn2 hrec_sn2
                   | (* SN_If_true *) cond i1 i2 s s' e sn hrec_sn
                   | (* SN_If_false *) cond i1 i2 s s' e sn hrec_sn
                   | (* SN_While_false *) cond i s hrec_sn
                   | (* SN_While_true *)  cond i s s' hrec_sn
                   ].
  - apply SN'_Skip.
  - apply SN'_Assign.
  - eapply SN'_Seq.
    + apply hrec_sn1.
    + apply hrec_sn2.
  - apply SN'_If_true.
    + apply e.
    + apply hrec_sn.
  - apply SN'_If_false.
    + apply e.
    + apply hrec_sn.
  - apply SN'_While_false. rewrite hrec_sn. reflexivity.
  - (** Le sous-but le plus intéressant, où les formulations diffèrent entre
        SN' et SN *)
    apply SN'_While_true.
    + rewrite H. reflexivity.
    + eapply SN'_Seq.
      -- apply IHsn1.
      -- apply IHsn2.
Qed.
