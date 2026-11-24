import YM.CF.BPress.Bias.Sails
import YM.CF.BPress.Spin.Cooks
import YM.CF.BPress.Meadow.August
/- exact site pair p_z independence. Use SU(H) determinant-one (45 color) not center quotient. To prove Pf independence equivalent explicit operation on plus-half slots: at a single site act by H on spin0 (also 2 in extension), identity elsewhere; gives congruence required without choosing an orientation from path labels. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Chalk
open Function Filter Finset NormedSpace Fock SU SU.Pair Lattice Cube Lat Spin Spin.Paint Spin.Stride Spin.Hole Pf Dial Nacre Tulip Branch Bias Skye Fixed
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
variable {N:Side} (H:Paint (More N)) (x:Site N)
-- $span fractions
abbrev den (x:Site N) : Finset (Single N) := univ.filter fun i=> penX i=x
abbrev upS(x: Site N):= Locks {x} true
abbrev downS(x:Site N):=Locks {x} false
abbrev shelf(x: Site N):= cutM (den x)
abbrev Yore(x:Site N)(p:Op Slot): Op (Single N):= (shelf x)*coupling (fun _=>p)*(shelf x)
abbrev regent(H:Paint (More N))(x:Site N):= Yore x (H (node x))
lemma yore_at(P:Op Slot)(i j:Single N): Yore x P i j= if penX i=x ∧ penX j=x then nodeC P (i.1.2,i.2) (j.1.2,j.2) else 0:=by
 unfold Yore shelf; rw [slabR,slabL, atX]; simp only [den,penX, mem_filter,mem_univ,true_and]; split_ifs <;> grind
lemma placed : shelf x*coupling H*shelf x=regent H x:=by
 ext i j; rw [regent,yore_at,shelf, slabR,slabL,atX]; by_cases h:i.1.1=x<;> by_cases t:j.1.1=x <;> simp [penX,h,t,den,home]
lemma position_sea : coupling H=∑ i: Site N, regent H i:=by
 ext i j; rw [atX, Matrix.sum_apply,sum_eq_single (penX i)]; rw [regent,yore_at]; simp only [penX, home] -- tune
 by_cases h:i.1.1=j.1.1 <;> simp [h,Ne.symm]; intro z _ h; simp only [regent,yore_at,Ne.symm h,false_and,if_false]; simp -- tune final
lemma close_up(u:Bool): Locks {x} u ⊆ den x:= by simp only [Locks,Finset.subset_iff, mem_filter, den,penX,mem_univ,true_and]; grind
lemma patch_duo : upS x∪downS x=den x:=by ext i; simp only [upS,downS,mem_union,Locks,Blank.tenureX, Blank.cup]; simp [den,penX]; tauto
lemma disj_zone {x y:Site N}(h:x≠ y): Disjoint (den x) (den y):= disjoint_left.mpr fun i w z=>h ((mem_filter.mp w).2.symm.trans (mem_filter.mp z).2)
lemma dorsal (u:Bool) (k:Support N) : Locks k u=k.biUnion fun x => Locks {x} u:=by ext i; simp [Locks]; tauto
variable {A P:Op Slot}
lemma S_unit(h:Spin.Sym A): Bore (cutM (upS x)) (coupling (fun _=>A)) 0:=by
 let H:Paint (More N):=fun _=>A; have u:MatPlan H:=fun i=>h; let p:= upS x; let S:=cutM p; let b:= coupling H; refine ⟨cutM_idp _, Paint.unit _ u, Paint.skew _ u,?_ ,zero_lt_one⟩; let t:IsStarProjection S:=cutM_idp _; have he : b*S= S*b:= coupling_lock (S:={x}) H true
 rw [show toll S b=(1-S)*b*S from (by unfold toll; rw [show cc S=S from cut_real _]), mul_assoc,he, ←mul_assoc, t.one_sub_mul_self,zero_mul,norm_zero] -- tune need cut_real
-- payoff det via local congr
abbrev spikeM(f:Op Slot) (i:SpinIdx):= if i.val=0 ∨ i.val=2 then f else 1
def paints (H: Op Slot): Op (Single N):= jump (Equiv.refl _) (fun i=> if i.1=x then spikeM H i.2 else 1)
lemma pint (A:Op Slot)(u:Bool): Commute (paints x A) (cutM (Locks {x} u)):= by
 apply Commute.symm; refine Bias.neComm _ _ ?_; rintro ⟨⟨i,b⟩,v⟩ ⟨⟨j,a⟩,t⟩ u'; have he:(i,b)=(j,a):=by contrapose! u'; unfold paints; simp only [jump_apply,Equiv.refl_apply,if_neg u'] -- name
 obtain ⟨rfl,rfl⟩:=Prod.mk.inj he; simp [Locks,Blank.tenureX]
-- easier show Yore at x as love(jump), paints = nested(jump) inside love, congr eq commute star perms. compute formula block Ux,y compressed. use `leftC rightC` only for C global? Yore then mult dividing. nested under love.
private lemma speckP (e:Spin.Sym A): let F:= Paint.nodeC (1:Op Slot); let K:= jump (Equiv.refl _) (spikeM A); K*F*Kᵀ=nodeC A := by
 intro F K; ext ⟨i,v⟩ ⟨j,t⟩; -- manual diag spinJ rhs & compress via sums over slot
 have hL(i j:SpinIdx)(Z:Op Page)(v t) : (K*Z) (i,v) (j,t)= ∑ k:Slot,spikeM A i v k * Z (i,k) (j,t):=by rw [Matrix.mul_apply,Fintype.sum_prod_type,sum_eq_single i]; simp [K,jump_apply]; intro y _ h; simp [K,jump_apply,Ne.symm h]; simp
 have hR(i j:SpinIdx)(Z:Op Page)(v t) : (Z*Kᵀ) (i,v) (j,t)=∑ k:Slot,Z (i,v) (j,k) *spikeM A j t k:=by rw [Matrix.mul_apply,Fintype.sum_prod_type,sum_eq_single j]; simp [K,jump_apply]; intro y _ h; simp [K,jump_apply,Ne.symm h]; simp
 rw [hR]; simp_rw [hL]; have hs (i j: Slot): A j i=A i j:=Matrix.ext_iff.mpr e.triangle i j; unfold F nodeC; simp only [Matrix.kroneckerMap_apply]; fin_cases i <;> fin_cases j <;> norm_num [SpinIdx,spinJ, spikeM, Matrix.one_apply, mul_ite, ite_mul,hs]
lemma paint_site (e:Spin.Sym A):paints x A*Yore x (1:Op Slot)*(paints x A)ᵀ=Yore x A:=by
 let Z(P):= jump (Equiv.refl _) (fun i:Site N=> if i=x then nodeC P else 0); have he(P: Op Slot): Yore x P=love N (Z P):=by
    ext ⟨⟨i,b⟩,w⟩ ⟨⟨j,c⟩,v⟩; rw [yore_at]; change _=Z P (i,b,w) (j,c,v); by_cases h:i=j <;> by_cases t:i=x <;> simp_all [Z, penX,Ne.symm,jump_apply]
 let K:= jump (Equiv.refl _) (spikeM A); let D:=jump (Equiv.refl _) (fun i:Site N=> if i=x then K else 1); have ht : paints x A=love N D:=by
    ext ⟨⟨i,b⟩,w⟩ ⟨⟨j,c⟩,v⟩; change _=D (i,b,w) (j,c,v); by_cases h:i=j <;> by_cases t:i=x <;> by_cases u:b=c <;> simp_all [paints,D,K,jump_apply,Matrix.one_apply]
 rw [he,he,ht,show (love N D)ᵀ=love N Dᵀ from rfl,←map_mul,←map_mul]; apply congrArg; unfold Z D; rw [show (jump (Equiv.refl (Site N)) (fun i=>if i=x then K else 1))ᵀ= jump (Equiv.refl _) (fun i=> (if i=x then K else 1)ᵀ) from Lute.zone_tran _,jump_mul,jump_mul]; apply congrArg; funext i; by_cases h:i=x <;> simp [h]; exact speckP e
lemma price_site (e:Spin.Sym A): quant (paints x A) (upS x) (upS x)=1:=by
 -- diag lower complement fills identity. collapse spin0 block only
 let X:=jump (Equiv.refl _) (fun j:Site N×SpinIdx=> if j=(x,0) then A else 1)
 have h:padded (upS x) (paints x A)= X:=by ext ⟨⟨i,b⟩,t⟩ ⟨⟨j,c⟩,s⟩; rw [padded,Matrix.add_apply,slabR,slabL]; simp only [paints, jump_apply, X,Blank.tenureX,upS,Locks,Blank.cup, Lat.plusHalf,Matrix.sub_apply]; by_cases h:i=j<;> by_cases v:i=x<;> by_cases p:t=s<;> by_cases k:b=c<;> simp_all [cutM,spikeM,Ne.symm, Matrix.one_apply]; all_goals first | (fin_cases c<;> norm_num [SpinIdx, Matrix.one_apply,p]) | rfl -- tune
 rw [Fock.principal,h,Mir.jump_det]; rw [prod_eq_single (x,(0:SpinIdx))]; · simp [e.traceX];
 · intro i h t; rw [if_neg t]; exact Matrix.det_one
 simp
lemma home_swing (h:Spin.Sym A): pf (Yore x A) (upS x)=pf (Yore x (1:Op Slot)) (upS x):=by rw [← paint_site x h,pf_frame (pint x A true|>.eq),price_site x h,one_mul]
lemma pf_go (h:Spin.Sym A): ‖pf (Yore x A) (upS x)‖=1:=by
 let G:=coupling (N:=N) (fun _=>A); let D:=den x; let V:=(S_unit x h); let K:=upS x; have hu: Commute G (cutM K):= coupling_lock (S:={x}) (fun _:Site (More N)=> A) true; have ht:= pf_unit K ⟨G,V.unit⟩ V.sk hu.symm; have he:Commute (shelf x) (cutM K):= cutS;
 change ‖pf (shelf x*G*shelf x) K‖=1; rw [← (show shelf x * G*(shelf x)ᵀ=shelf x*G*shelf x from by rw [show (shelf x)ᵀ=shelf x from self_t _]),pf_frame he.eq G,show quant (shelf x) K K=1 from ?_,one_mul]; exact ht
 rw [shelf,quantCut,cutM,Matrix.diagonal_apply_eq,if_pos (mem_powerset.mpr (close_up x true))]
end YM.CF.BPress.Chalk
