import YM.SU5.Relativistic.Wye
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Papyrus.GaugeFlux
open Function Finset Filter MeasureTheory Lattice Wilson RG Precision Exterior MinorPins Tree Matrix Bid Laurent
open scoped Matrix BigOperators Matrix.Norms.Frobenius InnerProductSpace ContDiff
variable {N C:Side}(S:StepData C N)(G:Gauge)(B:Bed)
local notation "Tn"=>Ink G N
local notation "Tc"=>Ink G C
local notation "T"=> solo G N C
local notation "Q"=> notice S G B
local notation "κ"=> S.kernel.penalty
local notation "F'"=> forecast S G
-- plane_det for large, swap first/coarse. explicit
private def reversed: Tc⊕ ScrollB G N ↪ Twin N C G.ColorIndex:=(Equiv.sumComm Tc (ScrollB G N)).toEmbedding.trans T -- implicit C use? projection
local notation "φ"=>reversed (N:=N) (C:=C) G
private lemma paste_rev (v:Tc⊕ ScrollB G N→ℝ): (smear φ*ᵥ v) ∘ Sum.inl= smear (fast G N)*ᵥ (v∘Sum.inr) ∧ (smear φ*ᵥ v) ∘ Sum.inr = v∘Sum.inl:=by
 constructor
 · funext i; by_cases e:i∈ interior G.ColorIndex N
   · rw [show (smear (fast G N) *ᵥ (v ∘ Sum.inr)) i=v (Sum.inr (⟨i,e⟩:ScrollB G N)) from smear_t (e:=fast G N) _ ⟨i,e⟩]; exact smear_t (e:=φ) v (.inr ⟨i,e⟩) -- tune
   have he: i∉ Set.range (fast G N):=fun ⟨y,q⟩=>e ((show y.val=i from q) ▸ y.property)
   rw [smear_f _ i he]; apply smear_f; rintro ⟨y,h⟩; cases y with| inl y=>nomatch h| inr y=> exact he ⟨y,Sum.inl.inj h⟩
 exact funext fun i=> smear_t (e:=φ) _ (.inl i)
lemma new_det {p:Clip}{a b:ℝ}(h:Floor B p N a b) : ((Q).submatrix φ φ).det= costDet G B N*κ^(Fintype.card Tc) :=by
 let A:= (Q).submatrix φ φ; let L:= smear (fast G N); let U:Matrix Tc Tc ℝ:=κ • 1
 rw [mul_comm]; convert plane_det A U (blockD G B N) (by unfold A; rw [transpose_submatrix,symmetric_m S G B h]) (by ext i j; rfl) ?_ using 1; swap
 · intro y; let p:= L *ᵥ y; let x:= Sum.elim (F'*ᵥ p) y; refine ⟨x,rfl,fun v=>?_⟩; have hv:= paste_rev G v; have hx:=paste_rev G x; change _ = dotProduct (v∘ Sum.inr) ((hess G B N).submatrix (fast G N) (fast G N) *ᵥ y) -- ... tune
   unfold A; rw [shade,notion, hv.1,hv.2,hx.1,hx.2]; change dotProduct (L*ᵥ _) _+κ* dotProduct _ ((F'*ᵥ p)-(F'*ᵥ p))=_; rw [sub_self,dotProduct_zero,mul_zero,add_zero]; exact (shade (fast G N) (hess G B N) _ _).symm
 unfold U costDet; rw [det_smul]; simp

variable (F:Forest S.ratio)
open FreeResolvent (treeMatrix)
def front: FreeResolvent.Active G F ↪ Tn:=Embedding.prodMap (Embedding.subtype _) (Embedding.refl _)
def stencil: (FreeResolvent.Active G F)⊕ScrollB G C ↪ Twin N C G.ColorIndex := duo (front S G F) (fast G C)
lemma range_now : Set.range (reversed (C:=C) (N:=N) G)=↑(newJoint (N:=N) (C:=C) (J:=G.ColorIndex)) := by
 ext i; cases i with
 | inl i=> change _ ↔ _∈(interior G.ColorIndex N).disjSum (univ:Finset Tc); constructor; · rintro ⟨y,h⟩; cases y with| inr y=>exact Finset.inl_mem_disjSum.mpr ((show y.val=i from Sum.inl.inj h) ▸ y.property)| inl y=>nomatch h
           intro e; exact ⟨Sum.inr ⟨i,Finset.inl_mem_disjSum.mp e⟩,rfl⟩
 | inr i=> constructor; · intro; simp [newJoint]
           intro; exact ⟨Sum.inl i,rfl⟩
lemma range_wind : Set.range (stencil S G F)=↑(oldJoint S F (J:=G.ColorIndex)):=by
 ext i; cases i with
 | inl i=> constructor
           · rintro ⟨a,g⟩; cases a with| inr j=>nomatch g| inl j=> rw [←g]; exact Finset.inl_mem_disjSum.mpr (mem_product.mpr ⟨mem_compl.mpr j.1.property,mem_univ _⟩)
           intro e; refine ⟨Sum.inl (⟨i.1, by simpa [oldJoint] using e⟩,i.2),rfl⟩
 | inr i=> change _↔ Sum.inr i∈_ ; constructor; · rintro ⟨y,h⟩; cases y with| inl y=>nomatch h| inr y=>exact Finset.inr_mem_disjSum.mpr ((show y.val=i from Sum.inr.inj h) ▸ y.property)
           intro e; exact ⟨Sum.inr ⟨i,Finset.inr_mem_disjSum.mp e⟩,rfl⟩
 
local notation "X"=> stencil S G F
-- encode relative stretches into F inner.
lemma stretched (x:Dir G C × AxisChart G F) (i:Bond N)(h:i∈F.trunks): collect G (stretch (S:=S) F x) i=0:=by
 obtain ⟨p,l⟩:=i; unfold collect; change stretch F x (p,coord l)=_; unfold stretch; simp only [show axisEquiv.symm (coord l)=l from axisEquiv.symm_apply_apply _,dif_pos h,add_zero]
 exact if_pos (F.trunk_internal h) -- implicit
lemma bright_peer (x:Dir G C × AxisChart G F) : let u:= coil G (stretch F x);
    smear (front S G F) *ᵥ (u ∘ (front S G F))=u:=by
 intro u; funext i; by_cases e:i.1∈ F.trunks
 · have he:=stretched S G F x _ e; rw [smear_f]; exact ( (congrFun (congrArg WithLp.ofLp he) i.2).symm)
   rintro ⟨y,t⟩; unfold front at t; apply y.1.property; exact (show y.1.val=i.1 from congrArg Prod.fst t).symm ▸ e
 let j: FreeResolvent.Active G F:=(⟨i.1,e⟩,i.2); exact smear_t (e:=front S G F) _ j
private lemma scripted (x:Dir G C)(y:FreeResolvent.Active G F→ℝ) : ∃ z: AxisChart G F, smear (front S G F) *ᵥ y=coil G (stretch F (x,z)):=by
 let a:=FreeResolvent.profile F y; let g(i:F.Free):= (linearCopy S.ratio (collect G x)) i.val; refine ⟨a-g,?_⟩
 rw [← bright_peer S G F (x,a-g)] -- let u?... tune
 congr 1
 funext i; apply Eq.symm; change stretch F (x,a-g) (i.1.val.1,coord i.1.val.2) i.2=y i -- tune
 unfold stretch; simp only [show axisEquiv.symm (coord i.1.val.2)=i.1.val.2 from axisEquiv.symm_apply_apply _,dif_neg i.1.property]
 rw [show (_ + (a - g) ⟨_,_⟩:G.Color)= a i.1 from (show g i.1+(a i.1-g i.1)= _ from (by abel))]; rfl
private lemma null_part (x: FreeResolvent.Active G F → ℝ): smear (front S G F) *ᵥ x = coil G (stretch (S:=S) F (0, FreeResolvent.profile F x)):=by
 rw [← bright_peer S G F (0,FreeResolvent.profile F x)]; congr 1; funext i; apply Eq.symm; exact congrFun (congrArg WithLp.ofLp (Work.F01.collect_vertical (S:=S) F (FreeResolvent.profile F x) i.1.val |>.trans (dif_neg i.1.property))) _
local notation "Μ"=>  Matrix.submatrix Q X X
private lemma stems : toBlocks₁₁ (Μ)=treeMatrix G S F B.metric:=by
 let A:=FreeResolvent.Active G F; let C:=ScrollB G C; ext i j
 let M:FreeResolvent.Active G F→ℝ:= Pi.single i (1:ℝ); let K:FreeResolvent.Active G F→ℝ:= Pi.single j (1:ℝ); let x:A⊕C→ℝ:=Pi.single (.inl i) 1; let y:A⊕C→ℝ:=Pi.single (.inl j) 1
 let v:= FreeResolvent.profile F M; let w:= FreeResolvent.profile F K
 have he: (Μ) (.inl i) (.inl j)= dotProduct x ((Μ)*ᵥ y):=by simp [x,y]
 change (Μ) (.inl i) (.inl j)= _; rw [he,shade,notion]; obtain ⟨a,b⟩:= paste (front S G F) (fast G _) x; obtain ⟨c,d⟩:= paste (front S G F) (fast G _) y; change (smear X *ᵥ x)∘ Sum.inl= _ at a; change (smear X *ᵥ x)∘ Sum.inr= _ at b; change (smear X *ᵥ y)∘ Sum.inl= _ at c; change (smear X *ᵥ y)∘ Sum.inr= _ at d
 rw [a,b,c,d,show (x ∘ Sum.inl)=M by funext i'; simp [x,M,Pi.single_apply],show (y∘ Sum.inl)=K by funext i'; simp [y,K,Pi.single_apply],show (x ∘ Sum.inr)= (0:C→ℝ) by funext; simp [x],show (y∘ Sum.inr)=(0:C→ℝ) by funext; simp [y],Matrix.mulVec_zero, zero_sub,zero_sub, null_part, null_part, tent_h,wrap_coil,wrap_coil,predicts_g,predicts_g, neg_dotProduct,dotProduct_neg,neg_neg,connect] -- κ.* compare via fiscal
 have hp:= FreeResolvent.fiscal_eq S B.metric (stretch F (0,v)) (stretch F (0,w)); rw [← FreeResolvent.tree_qf, show dotProduct (FreeResolvent.active F v) (treeMatrix G S F B.metric *ᵥ FreeResolvent.active F w)=treeMatrix G S F B.metric i j from (by unfold v w; rw [FreeResolvent.active_profile,FreeResolvent.active_profile]; simp [M,K])] at hp; exact hp.symm
private lemma leftRent {p:Clip}{W:PathData G}(P:Comptroller F B p W)(A D:ℝ)(pN:Floor B p N A D)(B':Bed)(U:Matrix (Body 1 N) (Body 1 C) ℝ)(π:Inputs S U (B.metric.acts N) (B'.metric.acts C)) : Matrix.det (Μ)= (treeMatrix G S F B.metric).det * costDet G B' C:=by
 apply plane_det (Μ) (treeMatrix G S F B.metric) (blockD G B' C) (by rw [Matrix.transpose_submatrix,symmetric_m S G B pN]) (stems S G B F)
 intro y
 let g:= fast G C; let h:=front S G F; let W':=smear g; let Z':=smear h; let L:=W'*ᵥ y; let ξ:= laced G L; let r:Dir G C × AxisChart G F:=(ξ,relative F U ξ)
 let f:=coil G (stretch F r); let V:= f ∘ h; let x:= Sum.elim V y; refine ⟨x,rfl,fun v=>?_⟩; let B_:= v ∘ Sum.inr; let A_:=v ∘ Sum.inl
 obtain ⟨a,b⟩:= paste h g v; obtain ⟨c,d⟩:=paste h g x; let Fv:=Z'*ᵥ A_; let C0:=W'*ᵥ B_; let ζ:= laced G C0; obtain ⟨u,t⟩:= scripted S G F ζ A_; change Fv=_ at t; change (smear X *ᵥ v)∘ Sum.inl= Fv at a; change (smear X *ᵥ v) ∘ Sum.inr=C0 at b; change (smear X *ᵥ x)∘ Sum.inl= Z' *ᵥ V at c; change (smear X *ᵥ x)∘ Sum.inr= L at d; let z:Dir G C × AxisChart G F:=(ζ,u)
 rw [shade,notion,a,b,c,d,t,show Z'*ᵥ V=f from bright_peer S G F _, tent_h];
 change gaugeFiscal B (laced G (coil G (stretch F z))) (laced G (coil G (stretch F r)))+κ*dotProduct (C0 - _) (L- _) = _
 rw [wrap_coil,wrap_coil,show C0 - _=coil G (crop F z) from ?_,show L- _ =coil G (crop F r) from ?_,connect]
 · let t':=Classical.arbitrary S.Choices; rw [← (show iteratedFDeriv ℝ 2 (uncurry (tested F t' p W)) 0 ![z,r]=_ from (P t').2.2 z r),Work.F04.test_pair F p W B B' U π P z ξ]; unfold blockD; rw [shade,tent_h]
 · unfold f; rw [predicts_g,crop,warp]; exact congrArg (fun x=>x-(coil G (bills S (stretch F r)))) (coil_wrap G L).symm -- goal order?
 · rw [predicts_g,crop,warp]; exact congrArg (fun x=>x-(coil G (bills S (stretch F z)))) (coil_wrap G C0).symm

-- exact leading Gaussian pressure step.Vol dimensions proven for any future forest/schedule
lemma stepGauge {p:Clip}{W:PathData G}(h:2≤ N.val)(w:2 ≤ C.val)(P:Comptroller F B p W) {A D:ℝ}(pN:Floor B p N A D)(B':Bed)(U:Matrix (Body 1 N) (Body 1 C) ℝ)(π:Inputs S U (B.metric.acts N) (B'.metric.acts C)) :
 costDet G B N*κ^(Fintype.card Tc)=(treeMatrix G S F B.metric).det * costDet G B' C:=by
 rw [←new_det S G B pN,←leftRent S G B F P A D pN B' U π]
 exact Grates.invariance (nowpins (J:=G.ColorIndex) S h) (beforepins S F (J:=G.ColorIndex) h w) (range_now ..) (range_wind S G F) (symmetric_m S G B pN) (lemma_kg S G B)
end YM.CF.Papyrus.GaugeFlux
#print axioms YM.CF.Papyrus.GaugeFlux.stepGauge
