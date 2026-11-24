import YM.CF.Dial.Haute
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Dial
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip Fock Peaks
open scoped Topology Matrix MatrixOrder BigOperators Matrix.Norms.L2Operator Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {N P:Side}(G:Ratio N P)
lemma vogue (u:Bool):Differentiable ℂ (squareD G u) :=by
  apply differentiable_pi.mpr; intro i; apply differentiable_pi.mpr; intro j
  simp only [squareD,readK, Matrix.submatrix_apply, jump_apply]
  split_ifs with p
  · have hh:Differentiable ℂ (fun x:Bale N P=> tableD G u x (abbe G i).1):=by cases u<;> unfold tableD <;> simp only [Bool.false_eq_true,if_false,if_true] <;> fun_prop
    exact differentiable_pi.mp (differentiable_pi.mp hh ((abbe G i).2)) ((abbe G j).2)
  exact differentiable_const _
lemma tee (u:Bool)(x y:Bale N P)(i):‖tableD G u x i-tableD G u y i‖≤ ‖x-y‖:=by
  let Z:= x-y; cases u
  · exact (norm_le_pi_norm ((x-y).2.2 (node i.1)) true).trans ((norm_le_pi_norm (x-y).2.2 _).trans ((norm_snd_le (x-y).2).trans (norm_snd_le (x-y))))
  exact (norm_le_pi_norm ((x-y).2.1 (node (isle G i))) true).trans ((norm_le_pi_norm (x-y).2.1 _).trans ((norm_fst_le (x-y).2).trans (norm_snd_le (x-y))))
private lemma monies {J:Type*}[Nonempty J][Fintype J][DecidableEq J](X Y:Op J)(h:Y∈unitary (Op J))(p:‖X-Y‖≤1): ‖X‖≤2:= le_trans (norm_le_norm_sub_add X Y) (le_trans (add_le_add p (CStarRing.norm_of_mem_unitary h).le) (by norm_num))
lemma table_pp(u:Bool)(x:TopK G 1)(i:Hand G): ‖tableD G u x.val i‖≤ 2:=by
  obtain ⟨U,h,f⟩:= x.property; exact monies _ _ (unit_table G u U i) ((tee G u x.val (post U) i).trans f.le)
lemma port_be (i: Iota G): (curveD G 1).home i=node (isle G (abbe G i).1):=rfl
lemma stampT (u:Bool)(hO:Odd G.count.val)(i:Iota G)(x y:TopK G 1):
 ‖tableD G u x.val (abbe G i).1-tableD G u y.val (abbe G i).1‖≤ (curveD G 1).eval (bay (terr _) ((curveD G 1).home i) (8*G.count.val)) x y:=by
 let S:=bay (terr _) ((curveD G 1).home i) (8*G.count.val)
 let F:= ∑ i∈S, ‖x.val.2.1 i-y.val.2.1 i‖; let B:=∑ i∈cloudG G S,‖x.val.2.2 i-y.val.2.2 i‖; let D:=deal G S x.val.1 y.val.1
 have hB : 0≤B:=by unfold B; positivity
 have hF:0≤F:=by unfold F; positivity
 have hD:0≤D:=deal_pos ..
 change _ ≤ (D+F+B)/ |(1:ℝ)|; rw [abs_one,div_one]
 let T:=(abbe G i).1
 cases u
 · let k:= node T.1
   have he:k∈cloudG G S:=by
     have he:k=node i.1.1:=rfl
     rw [he]; apply mem_filter.mpr ∘ And.intro (mem_univ _)
     let W:=loopTail G false i.1; have ht:= loopEnd G false hO i.1; apply (bay_mem _).mpr
     change separation (Peaks.arrive G i.1) (touch G false i.1)≤_ ; rw [separation_comm,← ht]; exact (leakspan ..).trans (tail_len ..)
   apply (norm_le_pi_norm (x.val.2.2 k-y.val.2.2 k) true).trans
   exact _root_.le_trans (Finset.single_le_sum (f:=fun i=> ‖x.val.2.2 i-y.val.2.2 i‖) (fun _ _=>norm_nonneg _) he) (le_add_of_nonneg_left (add_nonneg hD hF))
 let k:=(curveD G 1).home i; have hk:k=node (isle G T):=rfl; have he:k∈ S:= (bay_mem _).mpr (by rw [terr]; simp [k]) -- tune
 apply (norm_le_pi_norm (x.val.2.1 k-y.val.2.1 k) true).trans
 exact _root_.le_trans (Finset.single_le_sum (f:=fun i=> ‖x.val.2.1 i-y.val.2.1 i‖) (fun _ _=>norm_nonneg _) he) (show F ≤ _ by linarith)
lemma tablesB (ι :Type*)(u: Bool)(L:Side)(ho:Odd L.val): BoxD L (u,true) (u,false) (fun (_:ι) _ _ G x=> squareD G u x):=by
  apply boxify (e:=1) (k:=0) (a:=1) (C:=quota * ((((8*L.val:ℕ):ℝ))+1)^4*Real.exp (1*(quota*((((8*L.val:ℕ):ℝ))+1)^4))*2) ?_ one_pos one_pos
  intro i N P G he p; subst L
  let X :=squareD G u; let b:=curveD G 1; have hF:= vogue G u
  refine Crown.sheet (cD G _) quota_p.le zero_le_one (table_int G u _) (hF.continuous.comp continuous_subtype_val) zero_le_two (8*G.count.val) (fun i j=> honors (zoneP G 1) (f:=fun x:Bale N P=> X x i j) ((differentiable_pi.mp (differentiable_pi.mp hF i) j).differentiableOn)) ?_ ?_ ?_
  · intro x i j h; rw [squareD,readK, Matrix.submatrix_apply, jump_apply,if_neg]
    intro e; change b.F.span (b.home i) (b.home j)>_ at h; rw [port_be,port_be, show (abbe G i).1= _ from (e : (abbe G i).1=(abbe G j).1),b.F.reflex] at h; omega
  · intro i j x; simp only [squareD,readK,Matrix.submatrix_apply,jump_apply]; split; exact (norm_entry ..).trans (table_pp ..); simp
  intro i j x y
  have hp: 0≤b.eval (bay (terr _) (b.home i) (8*G.count.val)) x y:= b.pos ..
  simp only [squareD,readK,Matrix.submatrix_apply,jump_apply]; split_ifs; swap; simp; exact hp
  apply (norm_entry (tableD G u x.val _-tableD G u y.val _) ((abbe G i).2) ((abbe G j).2)).trans; apply (stampT G u ho i x y).trans; exact le_mul_of_one_le_left hp one_le_two
end YM.CF.Dial
