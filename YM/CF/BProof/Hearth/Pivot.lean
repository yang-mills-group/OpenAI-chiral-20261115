import YM.CF.BProof.Hearth.Elevate

/-! Constants/models for B-Cpass. Across occupied P bits at u=0, pair
matrices can be replaced by any values because two sides factor over these bits. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Hearth
open Function Filter Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Spin Stint Fig Align
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N:Side}{j:ℕ}{d c a b l r:ℝ} {P:Ready j a b l r}{F:Core j a b l r N}(h:Age P F d)
variable {S:Support N}
lemma freeE (x:1≤j)(M:Stamp)(u:ℝ) (p:‖u‖≤1)(H:BoardH F 1 S c)(W:Age P F d) : gapE F 1 S (fun _=>M) u=0:=by
 let B:Quilt N:= fun _=>M; let T:= PitH F 1 S u; let X:= H.houseFit u p; have hx:Align.Twig (pair B) (F.θ 1 1):=by rw [F.θtriv P W.minN]; exact freeAnti j x F.M M
 have he:= entersH H hx (pairBy S B true) (pairBy S B false) u p; change (1-T)* pair B * cc T=0; rw [mul_assoc, ← he,←mul_assoc]; change (1-T)*T*_=_; rw [qrComplement (P:=T) X.landed,zero_mul] -- tune defeq
lemma match_pair (X Y: Quilt N)(h:∀ i:Site N, X (node i)=Y (node i)) : pair X=pair Y:=by ext i j; rw [pair_local,pair_local]; unfold badgeOf; rw [h]
-- disconnected parts that can be changed in these pair matrices
lemma pair_comp (X Y: Quilt N)(e:∀ i:Site N,i ∉ S → X (node i)=Y (node i))(D:Type)(f:Feet N D): strip f.st (spot S)*(pair X-pair Y)=pair X -pair Y:=by
 ext i j; rw [stripL]; split; rfl; rename_i h; simp only [Matrix.sub_apply,pair_local,badgeOf]; rw [e,sub_self]; intro t; rw [f.index] at h; exact h ((spot_spec ..).2 t)
lemma zero_gap (U:Bkg (More N))(X Y:Quilt N)(h:BoardH F U S c)(e:∀ i: Site N,i∉ S→ X (node i)=Y (node i)): gapE F U S X 0=gapE F U S Y 0:=by
 let p:=bandCut S true; let q:=bandCut S false; let T:= PitH F U S 0; let E:= pair X-pair Y; let B:= iron N c c; let V:=strip B.st (spot S); have hp:V=p+q:= total S B; have he : E=pair (X-Y):= pair_difference ..; have ht:V*E=E:=pair_comp X Y e _ B; have hf:E*V=E:=(Eq.trans (by rw [he]; exact (pair_total S (X-Y) B).symm : E*V=V*E) ht)
                                                                                                 -- second
 have ha:T*p=p:=h.slotIn; have hw:T*q=0:=swapOrth h.q h.fit0.landed h.slotForget; have hk: cc V=V:= cut_real _; have hj: cc p=p:= cut_real _; have hy : V*T=p:= by rw [hp,add_mul,show p*T=p from h.slotSide, show q*T=0 from h.slotForget,add_zero]
 unfold gapE; apply sub_eq_zero.mp; change (1-T)*_*cc T-(1-T)*_*cc T=0; rw [←sub_mul,←mul_sub]; change (1-T)*E*cc T=0; rw [mul_assoc,←hf,mul_assoc E, show V*cc T=p from (by rw [←hk,←cc_mul,hy,hj]), show E*p=p*E from (by rw [he]; exact pairCom ..),←mul_assoc, sub_mul,one_mul,ha,sub_self,zero_mul] -- tune occurrence hf
lemma clipNodes {q:ℝ}{A: Quilt N}(h:0≤q)(hp:∀ i:Site N, ‖A (node i)‖≤q): ‖pair A‖≤q := by
 let B:Quilt N:= fun i=> if i∈ spot (univ:Support N) then A i else 0; rw [match_pair A B (by unfold B; simp)]; apply pair_bound h; intro i; unfold B; split; obtain ⟨t,g,rfl⟩:= spotsNN _ ‹_›; exact hp _; rw [norm_zero]; exact h
lemma clanModel (h:Age P F d)(H:BoardH F 1 S c)(g:1≤j)(Q:Quilt N)(T:Stamp){r':ℝ}(t:0≤r')(Y:∀ i: Site N,i∉ S→ ‖Q (node i)-T‖ ≤ r'): ‖gapE F 1 S Q 0‖≤r':=by
 let V:Quilt N:= fun i=> if i∈spot S then T else Q i; let B:Quilt N:=fun _=>T; let W:=pair V-pair B; rw [zero_gap 1 Q V H (fun i hi=>by simp [V,hi])]; have he:= H.fit0.landed; let U:= PitH F 1 S 0; change IsStarProjection U at he; have hg:‖W‖ ≤ r':=by rw [show W=_ from pair_difference V B]; apply clipNodes t; intro i; by_cases q:i∈S; simpa only [Pi.sub_apply,V,B,(spot_spec S i).2 q,↓reduceIte,sub_self,norm_zero]; simp [V,B,q]; exact Y i q -- tune
 rw [← sub_zero (gapE F 1 S V _), ← freeE g T 0 (by simp) H h, gapE,gapE,←sub_mul,←mul_sub]; change ‖(1-U)*W* cc U‖ ≤ r'
 exact (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) ((ccProj he).norm_le _)).trans ((norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) (he.one_sub.norm_le _)).trans hg)))
end YM.CF.BProof.Hearth
