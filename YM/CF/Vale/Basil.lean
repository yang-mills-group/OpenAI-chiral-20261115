import YM.CF.Vale.Dose
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vale
open Function Filter Lattice Laurent Bloch Wilson Precision Tree Finset Exterior Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Pec Next.Free Pressure Cascade Reef Hom PhysicalNext.JointLoad.Heir
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {K:Teller group}{P:RG.Patch}{R:ChartRatio group}{W:Postal}{η e:ℝ}{n k v i:ℕ}{f g a b d w:ℝ}{B m c u:Side}{C:Credit}
variable {U: Pricing K.j P.L P.odd_side (Thread K.j)} {D:Grasp U B e}{S:Gold K P R W}{x y z:ℝ}
structure Grace(K:Teller group)(P:RG.Patch)(R:ChartRatio group) where
 W:Postal
 L:Gold K P R W
 U: Pricing K.j P.L P.odd_side (Thread K.j)
 note: Stamped K.j P.L P.odd_side U
 a:ℝ
 b:ℝ
 d:ℝ
 r:ℕ
 a_o:0<a
 b_o:0<b
 d_o:0<d
 sp: Spack K.j P.L P.odd_side a b d r
 F1:ℝ
 f:ℝ
 F2:ℝ
 g:ℝ
 pos1:0<F1
 pos2:0<F2
 width1:0<f
 width2:0<g
 aura{B:Side}{e:ℝ}{D:Grasp U B e}: Pearl D → 0<e → ∃ C:Credit,C.F=F1∧ C.f=f ∧C.U=F2∧C.u=g ∧ Reward D K C R P W
 roomZ:room K.top.drift P.L
 applyK: licensed K.η K.C P.L
 tallX:4≤P.L.val
 vor:∀ᶠ w:ℝ in atTop,∃ u:ℝ,0<u ∧ K.cash P.L w u
 gate: Even K.j
 up:1≤ K.C
lemma buy_l (A B:ℝ) :∃ n:ℕ,∀ L:Side,n≤ L.val → licensed A B L:=by
 obtain ⟨n,h⟩:= exists_nat_gt (128*yarn A B); refine ⟨n,fun L p=>?_⟩; unfold licensed; nlinarith only [(h.trans_le (show (n:ℝ) ≤ L.val from by exact_mod_cast p)),(show 1≤(L.val:ℝ) from by exact_mod_cast L.property)]
lemma sun(j:ℕ)(p:4≤j)(h: Even j)(Z:ChartRatio group)(v:LocalRatio Z):∃ K:Teller group,K.j=j ∧ 1≤K.C ∧ K.top.clip.direct≤1 ∧ (∀ P:RG.Patch,P.Branches K.bind group) ∧ ∃ n:ℕ,∀ P:RG.Patch,n≤P.L.val→ P.J=j→ Nonempty (Grace K P Z):=by
 obtain ⟨K,f,N,hK,hx,g,q,H,R⟩:=clay j p Z v; have he: Even K.j:=by rw [hK]; exact h
 obtain ⟨z,t⟩:=peace_price K g he (by omega); obtain ⟨p',X⟩:=clearance K.top.drift K.top.drift_ge; obtain ⟨i,Z'⟩:=buy_l K.η K.C; obtain ⟨m,hM⟩:=(Next.Fluctuations.grants K).precedes
 refine ⟨K,hK,g,H.fit,H.oath,N+z+p'+i+m+4,fun P φ Ψ=> ?_⟩; obtain ⟨W,Y,B⟩:=R P (by omega) Ψ
 obtain ⟨A⟩:= Vale.coin H (by omega) (Ψ.trans hK.symm) Y B; obtain ⟨U,F⟩:=sparkling (j:=K.j) he (by omega) P.odd_side; obtain ⟨a,b,d,ha,hb,hd,l,L⟩:=peach (by omega : 1 ≤ K.j) he P.odd_side
 obtain ⟨a',b',r,s,v1,v2,u,w,V⟩:= t P (by omega) Z W Y F L ha hb hd; exact ⟨⟨W,A,U,F,a,b,d,l,ha,hb,hd,L,a',b',r,s,v1,u,v2,w,@V,X P.L (by omega),Z' P.L (by omega),by omega,hM P.L (by omega),he,g⟩⟩
lemma huge(L:Side)(p:2≤ L.val)(z:ℕ): z ≤ (L^z).val:=by
 induction z with
 | zero=>omega
 | succ z ih=> rw [pow_succ]; change _ ≤ (L^z).val*L.val; cases z with
    | zero=> exact le_trans (by omega : 0+1 ≤ L.val) (by simp)
    | succ z=> exact le_trans (by omega : z+1+1≤ (z+1)*2) (Nat.mul_le_mul ih p)
lemma spices(X:Grace K P R)(T:Acorn.Repair K.j)(z:ℕ): ∃ i:ℕ, z≤ i ∧ ∀ j:ℕ,i≤j → ∃ e:ℝ,0< e∧∀ x:ℝ,0<x →x≤ e →∃ D:Grasp X.U (P.L^j) x,Nonempty (Pearl D) ∧ x ≤ T.d ∧ D.baseline ≤ T.d ∧ T.n ≤D.roundZ:=by
 have he:= X.tallX; let L:=P.L; have ht:L.val≥2:=by unfold L; omega
 obtain ⟨N,H⟩:= ava X.U T (by have hx:=X.L.lobby; have hy:=P.order_cut; omega); let b:=L^N; obtain ⟨n,h⟩:= H b (huge L ht _); let u:= L^n; obtain ⟨k,U⟩:= h u (huge L ht _); refine ⟨z+N+n+k,by omega,fun j hi=>?_⟩
 obtain ⟨e,hu,A⟩:= U (L^j) ((by omega : k ≤ j).trans (huge L ht j)) ⟨L^(j-N),show L^j=L^N*_ from by rw [←pow_add]; congr; omega⟩ ⟨L^(j-n),show L^j=L^n*_ from by rw [←pow_add]; congr; omega⟩; refine ⟨e,hu,fun x y z=>?_⟩
 obtain ⟨D,h,-,g,w⟩:= A x y z; exact ⟨D,h,g,w⟩
end YM.CF.Vale
