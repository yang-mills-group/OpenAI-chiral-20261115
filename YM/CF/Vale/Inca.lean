import YM.CF.Vale.Honor
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vale
open Function Filter Lattice Laurent Bloch Wilson Precision Tree Finset Exterior Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Pec Next.Free Pressure Cascade Reef Hom
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable (m B L:Side)
def mesh (i:ℕ):Side:=m*L^i
lemma mesh_succ(i:ℕ):mesh m L (i+1)=mesh m L i*L:=by simp only [mesh,pow_succ']; ac_rfl -- tune
abbrev cell(i:ℕ):Side:=CSide (mesh m L i) B
lemma grows(i:ℕ):cell m B L (i+1)=cell m B L i * L:=by unfold cell CSide; rw [mesh_succ]; unfold More; ac_rfl
def apt(i:ℕ): Ratio (cell m B L i) (cell m B L (i+1)):= ⟨L, congrArg Subtype.val (grows m B L i)⟩
lemma val_e(i:ℕ): Even (cell m B L i).val:=by change Even ((mesh m L i).val*2*B.val); exact (even_two.mul_left _).mul_right _
lemma kint (i:ℕ): (More (cell m B L (i+1))).val=(More (cell m B L i)).val*L.val:=by
 rw [grows]; change (_*L.val)*2=_*2*L.val; ring
variable {B L m}
variable {K:Teller group}{P:RG.Patch}{R:ChartRatio group}{W:Postal}{η e:ℝ}{n k:ℕ}{f g a b d:ℝ}{A C:Side}
variable {U: Pricing K.j P.L P.odd_side (Thread K.j)} {D:Grasp U B e}
namespace Gold
variable (A:Gold K P R W)
lemma pace {m r: Side}(h:r.val=m.val*P.L.val)(p:W.n ≤m.val)(i:ℕ):Bid.Larger (G:=group) (A.op i h):=by
 have hg:A.op i h=⟨P,K.bind,h⟩:=by cases e: A.op i h with| mk z v y=> have hr:z=P:= Eq.trans (congrArg RG.StepData.patch e.symm) (A.lent _); have ht:v=K.bind:= Eq.trans (congrArg RG.StepData.kernel e.symm) rfl; congr
 rw [hg]; exact A.robe.bound _ p
variable {C:Credit}
abbrev ticket (m:Side)(D:Grasp U B e)(C:Credit)(j i:ℕ)(L₁:Interest (cell m B P.L i))(L₂:Interest (cell m B P.L (i+1)))(v:ℝ):Prop:=Mint D C v K L₂ L₁ (apt m B P.L i) (A.op j (kint m B P.L i)) (A.path j) (A.path (j+1))
lemma earnest(E:Reward D K C R P W)(i j:ℕ)(p:C.i≤(cell m B P.L i).val)(L₂:Interest (cell m B P.L (i+1)))(U:InterestX C _ L₂):∃ L₁ v,A.ticket m D C j i L₁ L₂ v:=by
 exact E.earns (A.lent j) (A.lent_L j).symm (A.roof j) (A.roof (j+1)) (A.Z j) (A.path j) (A.path (j+1)) (A.deed j) (A.mood j) (A.mood (j+1)) (A.ring j) (A.tied (j+1)) (A.sold j) (apt m B P.L i) rfl (A.sized j (kint m B P.L i)) p L₂ U
variable {v w u:ℝ}{j i:ℕ}{L₁:Interest (cell m B P.L i)}{L₂:Interest (cell m B P.L (i+1))}
lemma follow_X(z: Even K.j)(p:Stamped K.j P.L P.odd_side U)(h:Spack K.j P.L P.odd_side a b d k)(hy:0 < e)(hd:0<d)(hp:D.roundZ+k+W.n≤(cell m B P.L i).val)(M:A.ticket m D C j i L₁ L₂ v)
 (HH:∀ F:Forest (A.op j (kint m B P.L i)).ratio, ∀ z,Critical F K.top.clip (A.path j) z → Horizon F z 2 w u) : Valued K.j P.L P.odd_side a b d e k (mesh m P.L i) (mesh m P.L (i+1)) B U D K.j K.j K.bind.penalty K.η K.C w u L₁ L₂ v:=by
 let H:=cell m B P.L i; have he:W.n≤(More H).val:=by change W.n≤(cell m B P.L i).val*2; omega
 let T:= A.op j (kint m B P.L i); let G:= apt m B P.L i; have ht:T.ratio=ratio G:=rat_eq (A.lent_L j).symm; have hv:_:=A.sized j (kint m B P.L i); let F:Forest T.ratio:= Classical.choice (Tree.select _ (A.f j).odd)
 obtain ⟨y,Y,S⟩:= (A.sold j).existP _ _ hv he F; have hK:P.J=K.j:= A.lobby; have hk:1≤K.j:=by have hy:=P.order_cut; omega
 have hy :Hull K.j P.L P.odd_side a b d e k (mesh m P.L i) (mesh m P.L (i+1)) B G T F y U D:= by
    refine ⟨p,rfl,ht,?_,?_,z,hk,h,⟨_,_,_,_,_,_,Classical.arbitrary T.Choices,Y, (A.pace (kint m B P.L i) he j).1,A.mood j, ((A.sold j).all _ _ (A.sized j (kint m B P.L i)) he F).1,W.tame⟩,hy,hd⟩ <;> exact le_trans (by omega) hp
 let d:=A.roof (j+1); rw [(A.deed j).first] at S
 exact ⟨⟨G,T,F,y,hy,A.path (j+1),_,_,_,_,_,A.f j,A.lent_L j,hv,A.mood (j+1), A.tied (j+1),⟨_,_,d.2.1 _⟩,d.1.2.1,d.2.2 _, M.grown,S, HH F y Y,M.hope F y Y⟩⟩
end Gold
end YM.CF.Vale
