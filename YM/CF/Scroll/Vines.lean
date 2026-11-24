import YM.CF.Scroll.Sheer
set_option autoImplicit false
noncomputable section
namespace YM.CF.Scroll
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Next.Free Laurent Fir Bloch SU Drapes Peaks Dial Tulip
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators Kronecker
attribute [local instance] opCStarAlgebra
variable {b r:Bool}{N P: Side}(G:Ratio N P)(ho:Odd G.count.val)(a:Shape)(u:ColorT b)(U:UNI SpinIdx)(p:JetS a.s b r U)
variable (k l:Bool)(A:Track G.count)(o:Lattice.Order)(x:Nom N P)
-- foam frames at fines basis use actual gauge x even in path z small
abbrev driveH (z:Cover):Op (Iota G):=∑ i:St G.count,∑ j:St G.count, drag G k l i j z (A z i j) o (unionP x)
def routeH(z:Cover)(i t:Site G.count):Walk:=runD k l G.count (i,0) (t,0) z o
def meetH(X: Hand G):Site (More P):=touch G k (X.1,X.2,0)
private lemma dragK (z:Cover)(a b r s:St G.count)(X Y:Site N) (p q:Slot): drag G k l a b z (A z a b) o (unionP x) ((X,r),p) ((Y,s),q) = if r=a∧ X+wrap N z=Y∧ s=b then Rush.wind X z*A z r s*(matter (travel x.1 (meetH G k (X,r.1)) (routeH G k l o z r.1 s.1))).val p q else 0:=by
  simp only [drag,unionP,track_pr,brand,Matrix.sum_apply]; rw [Finset.sum_eq_single X]; swap; intro x _ h; simp [panel,Ne.symm h]; swap; simp
  by_cases h:X+wrap N z=Y<;>by_cases g:r=a <;>by_cases hx:s=b <;> simp [panel,h,eq_comm (a:=Y),g,hx]; left; unfold meetH routeH; rw [show touch G k (X,(a.1,(0:SpinIdx)))=touch G k (X,a) from (by cases k <;> rfl)]; rfl
lemma summ_h (h:∀ i j,Summable fun z=>‖A z i j‖) (i j:St G.count) : Summable fun z:Cover=>drag G k l i j z (A z i j) o (unionP x):=by
 apply u_all; rintro ⟨⟨x',a⟩,p⟩ ⟨⟨y,b⟩,q⟩; apply Summable.of_norm; apply (h i j).of_nonneg_of_le; intro; apply norm_nonneg
 intro z; rw [dragK]; split; next he=>rw [he.1,he.2.2,norm_mul,norm_mul, show ‖Rush.wind x' z‖=1 from fee_norm _,one_mul]; apply mul_le_of_le_one_right (norm_nonneg _); exact (norm_entry ..).trans (CStarRing.norm_of_mem_unitary (matter _).property).le
 simp
lemma wrest (h:∀ i j,Summable fun z=> ‖A z i j‖): douse G k l A o (unionP x)=∑' z,driveH G k l A o x z:=by
  have hh:= summ_h G k l A o x h; unfold driveH
  rw [Summable.tsum_finsetSum]; swap; intro k _; exact summable_sum fun i _=>hh k i
  unfold douse; refine sum_congr rfl fun i _=> ?_
  rw [Summable.tsum_finsetSum]; swap; intro k _; exact hh i k
  exact sum_congr rfl fun j _=> names.tsum_eq (fun z=>drag G k l i j z (A z i j) o (unionP x))
lemma port_x (z:Cover)(i j:Hand G): tap ((driveH G k l A o x z).submatrix (abbe G).symm (abbe G).symm) i j =if i.1+wrap N z=j.1 then wind i.1 z • ((tap (A z) i.2 j.2) ⊗ₖ (matter (travel x.1 (meetH G k i) (routeH G k l o z i.2 j.2))).val) else 0:=by
 ext ⟨p,a⟩ ⟨q,t⟩; change driveH G _ _ _ _ _ z ((i.1,i.2,p),a) ((j.1,j.2,q),t)= _; simp only [driveH, Matrix.sum_apply,dragK]; by_cases h:i.1+wrap N z=j.1
 · rw [if_pos h]; simp only [h,and_true,true_and]; -- h rewrites too much
   rw [sum_eq_single (i.2,p)]; simp; try ring
   all_goals try (intro a _ g; simp [Ne.symm g])
   all_goals try simp
 rw [if_neg h]; simp [h]
include ho
lemma meet_x (i:Hand G): meetH G k (paceU a G i)= (a.broad G).anon P (meetH G k i):=by
 cases k
 · change (ratio G).embed (node (a.mills N i.1))=Shape.anon _ _ ((ratio G).embed (node i.1)); rw [a.nodex,a.foldsT]
 change node (isle G (a.mills N i.1,a.s.act i.2))=Shape.anon _ _ (node (isle G i)); rw [← Shape.folds a G ho, Shape.nodex]
lemma run_z(z:Cover)(i j: Site G.count): List.map (·.rotate a.s) (routeH G k l o z i j) = routeH G k l (rollX a.s o) (a.s.act z) (a.s.act i) (a.s.act j):=by
 unfold routeH runD; rw [send_route _ _ _ _ 0];
 have he(w:Bool)(i:Site G.count): a.s.act (traceU w (i,(0:SpinIdx)))=traceU w (a.s.act i,0):=by cases w; simp [traceU]; unfold traceU; simp only [ite_true]; rw [Ratio.lift_signed_of_odd ho]; exact map_nsmul (a.s.actEquiv (R:=ℤ)) 2 _
 simp only [affine, Signed.act_zero,add_zero,Signed.act_sub,Signed.act_add, he]; rw [two_smul, Signed.act_add,show a.s.act (G.count.val • z)=G.count.val • a.s.act z from map_nsmul (a.s.actEquiv (R:=ℤ)) _ _,two_smul]; rfl
variable (v:∀ z:Cover,sings b (pinBlock G.count a.s U) (A (a.s.act z))=A z)
include v
lemma crunch(z): sings b (pflux a G U u) (driveH G k l A (rollX a.s o) x (a.s.act z))=driveH G k l A o (stanza G a u x) z:=by
 let P:=driveH G k l A (rollX a.s o) x (a.s.act z); let Q:=driveH G k l A o (stanza G a u x) z; apply Epin G; rw [port_back]
 ext ⟨i,b'⟩ ⟨j,c⟩
 suffices t: tap (sings b (fros a G U u) (P.submatrix (abbe G).symm (abbe G).symm)) i j=tap (Q.submatrix (abbe G).symm (abbe G).symm) i j from congr_fun (congr_fun t _) _
 have he : (paceU a G i).1+wrap N (a.s.act z)=(paceU a G j).1 ↔ i.1+wrap N z=j.1:=by change a.mills N _+_=a.mills N _ ↔ _; rw [←a.tow]; exact a.mills_b.1.eq_iff
 have hv:z=z:=rfl
 unfold fros; rw [tap_sg,port_x,port_x]; by_cases p:i.1+wrap N z=j.1; swap; rw [if_neg (fun g=>p (he.mp g)),if_neg p,win_z,mul_zero,zero_mul]
 rw [if_pos (he.mpr p),if_pos p]; rw [show star (milU a U u j.1).val=star (milU a U u (i.1+wrap N z)).val by rw [p]]
 rw [show (paceU a G i).1=a.mills N i.1 from rfl,lane_x,wingK]
 have hh:= congr_arg (fun Z=>tap Z i.2 j.2) (v z); have ht:sings b U (tap (A (a.s.act z)) (paceU a G i).2 (paceU a G j).2)=tap (A z) i.2 j.2:=by
   unfold pinBlock at hh; rw [tap_sg] at hh; rw [singT,twist_formula]; exact hh
 rw [ht]; rw [meet_x G ho]; congr 2 -- tune
 simp only [stanza,levity,u.shore,run_z G ho]; rfl
omit p
lemma mosaicS (h:∀ i j,Summable fun z=>‖A z i j‖): sings b (pflux a G U u) (mosaic G k l A (unionP x))=mosaic G k l A (unionP (stanza G a u x)):=by
  rw [mosaic,mosaic,singT,win_r,map_smul,win_sum,map_sum,←Equiv.sum_comp (rollX a.s)]; congr 1; apply sum_congr rfl; intro i _
  rw [← singT,wrest G k l A _ x h,wrest G k l A i _ h,sings_sumts,← a.s.actEquiv.toEquiv.tsum_eq]; apply tsum_congr; intro z; exact crunch _ ho _ _ _ _ _ A i x v z
  exact summable_sum fun p _=> summable_sum fun q _=> summ_h _ _ _ _ _ _ h p q -- tune
end YM.CF.Scroll
