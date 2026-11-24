import YM.CF.Vale.Archer
import YM.CF.Spire.Neon
/-! The small-guard provision of VolumeB-gate. Copy and strengthen the FiniteGaugeData proofs
 `ava`, `spices`, `blessed`, `score` exactly as indicated there. -/
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Spire
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {j:ℕ}{L m B:Side}{ho:Odd L.val}{T:Script Male}{e:ℝ}{Y: Pricing j L ho T}
lemma ava_Bq (Y:Pricing j L ho T)(R: Acorn.Repair j)(p:1≤j): ∃ N:ℕ, ∀ b:Side,N≤b.val→∃ W:ℕ, ∀ D:Side, W≤ D.val →∃ K:ℕ,∀ B:Side,K ≤B.val →(∃ F, B=b*F) → (∃ F,B=D*F)→∃ e p0:ℝ,0<p0∧ 0<e ∧∀ f:ℝ, 0<f→f≤e→∃ g:Grasp Y B f, (∃ t:Pearl g, t.q=p0) ∧ g.b=b∧ f ≤ R.d∧g.baseline≤R.d∧ R.n≤g.roundZ:=by
 obtain ⟨l,d,a,t,v,n,pA,k,H⟩:=coin_v j p
 obtain ⟨N,V⟩:=resolve d H.posT
 refine ⟨N, fun b x=>?_⟩; obtain ⟨q,p',hp',hx⟩:= V b x
 let δ:=min (min Y.e p') R.d; have hd:0<δ:=lt_min (lt_min Y.range hx.pPositive) R.pd
 obtain ⟨u,h,hQ,W⟩:=kip L.val δ hd; obtain ⟨Z,HZ⟩:=resolve u h
 refine ⟨Z,fun D H'=>?_⟩; obtain ⟨e',w',g',G'⟩:=HZ D H'; obtain ⟨r,hr,hR,hB,B₁,B₂⟩:=loose w' u G'.pPositive h L; obtain ⟨r',hr',hu',hD'⟩:=kip L.val r hr
 obtain ⟨N',R'⟩:= scalable _ hr'; obtain ⟨x,A⟩:= all_room; refine ⟨max x N',?_⟩; intro B hP hb hF; obtain ⟨F,pB⟩:=hb; obtain ⟨B₀,pD⟩:=hF
 obtain ⟨c,r'',Q⟩:= R' B ((le_max_right ..).trans hP); obtain ⟨e,pE,Q'⟩:= A B ((le_max_left ..).trans hP); obtain ⟨w,pW,v',Wy⟩:= drift_l j p
 let m:=min (min (min u q) c) (min e w); let a':= min e' (min r' m); have hm:0< m:=lt_min (lt_min (lt_min h hp') r'') (lt_min pE pW)
 let b':=R.n+ v+v'+Y.N+(2*rankS L.val)+1
 refine ⟨a',r,hr,lt_min g' (lt_min hr' hm),fun M hk h'=>?_⟩; have hx₁:M≤r':=h'.trans ((min_le_right ..).trans (min_le_left ..)); have hf:= h'.trans ((min_le_right ..).trans (min_le_right ..) : a'≤ m)
 have hg:= hf.trans (min_le_right .. : m≤ min e w); have hl := hg.trans (min_le_right ..); have hx' := hf.trans (min_le_left .. : m≤ min (min u q) c)
 have hv:=hx'.trans (min_le_left ..); have hd':= hQ.le.trans ((min_le_left ..).trans (min_le_left ..) : δ≤Y.e)
 have hh :billK L.val M u < δ:= (by
   apply lt_of_le_of_lt _ W; unfold billK; gcongr <;> exact hv.trans (min_le_left ..))
 have hh' :billK L.val M r'<r:= (by apply lt_of_le_of_lt _ hD'; unfold billK; gcongr)
 have hz₁:=Q M (hx'.trans (min_le_right ..)); let g:Grasp Y B M:= ⟨l,n,v,b',b,F,pB.symm,d,t,a,pA,k,p',u,h,H,hx.pull hk.le (hv.trans (min_le_right ..)), Q' _ hk.le (hg.trans (min_le_left ..)), ⟨hz₁.1,hz₁.2.trans_le (hu'.le.trans hB)⟩,(hv.trans (min_le_left ..)).trans hd',hQ.le.trans ((min_le_left ..).trans (min_le_right ..)),hd', hh.trans_le ((min_le_left ..).trans (min_le_right ..)),hh.trans_le ((min_le_left ..).trans (min_le_left ..)),by unfold b'; omega,by unfold b'; omega,by unfold b'; omega, fun N hx M=> (Wy N (le_trans (show v'≤ b' from by unfold b'; omega) hx) M).red hl⟩; have hu:g.baseline≤ R.d:=hQ.le.trans (min_le_right ..)
 refine ⟨g,⟨⟨r,r',hr',hu'.le,hB,hh',B₁,B₂,hz₁,fun s=>?_⟩,rfl⟩,rfl,(hv.trans (min_le_left ..)).trans hu,hu,show R.n≤b' from by unfold b'; omega⟩
 have he: CSide (s*B₀) D=CSide s B:=by rw [pD]; unfold CSide More; ac_rfl
 intro U V x' h y hy; exact hike (G'.pull hk.le (h'.trans (min_le_left ..))) he U V x' (fun i q=>(h i q).trans_le hR) y (fun i q=>(hy i q).trans_le hR)
end YM.CF.Spire

section
namespace YM.CF.Vale
open Function Filter Lattice Laurent Bloch Wilson Precision Tree Finset Exterior Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Pec Next.Free Pressure Cascade Reef Hom PhysicalNext.JointLoad.Heir
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {K:Teller group}{P:RG.Patch}{R:ChartRatio group}{W:Postal}{η e:ℝ}{n k v i:ℕ}{f g a b d w:ℝ}{B m c u:Side}{C:Credit}
variable {U: Pricing K.j P.L P.odd_side (Thread K.j)} {D:Grasp U B e}{S:Gold K P R W}{x y z:ℝ}
lemma spices_Bq(X:Grace K P R)(T:Acorn.Repair K.j)(z:ℕ): ∃ i:ℕ, z≤ i ∧ ∀ j:ℕ,i≤j → ∃ e z0:ℝ,0<z0 ∧ 0< e∧∀ x:ℝ,0<x →x≤ e →∃ D:Grasp X.U (P.L^j) x,(∃ t:Pearl D,t.q=z0) ∧ x ≤ T.d ∧ D.baseline ≤ T.d ∧ T.n ≤D.roundZ:=by
 have he:= X.tallX; let L:=P.L; have ht:L.val≥2:=by unfold L; omega
 obtain ⟨N,H⟩:= ava_Bq X.U T (by have hx:=X.L.lobby; have hy:=P.order_cut; omega); let b:=L^N; obtain ⟨n,h⟩:= H b (huge L ht _); let u:= L^n; obtain ⟨k,U⟩:= h u (huge L ht _); refine ⟨z+N+n+k,by omega,fun j hi=>?_⟩
 obtain ⟨e,Z,hZ,hu,A⟩:= U (L^j) ((by omega : k ≤ j).trans (huge L ht j)) ⟨L^(j-N),show L^j=L^N*_ from by rw [←pow_add]; congr; omega⟩ ⟨L^(j-n),show L^j=L^n*_ from by rw [←pow_add]; congr; omega⟩; refine ⟨e,Z,hZ,hu,fun x y z=>?_⟩
 obtain ⟨D,h,-,g,w⟩:= A x y z; exact ⟨D,h,g,w⟩
end YM.CF.Vale
end

namespace YM.CF.Vale
open Function Filter Lattice Laurent Bloch Wilson Precision Tree Finset Exterior Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Pec Next.Free Pressure Cascade Reef Hom PhysicalNext.JointLoad.Heir
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {K:Teller group}{P:RG.Patch}{R:ChartRatio group}{W:Postal}{η e:ℝ}{n k v i:ℕ}{f g a b d w:ℝ}{B m c u:Side}{C:Credit}
variable {U: Pricing K.j P.L P.odd_side (Thread K.j)} {D:Grasp U B e}{S:Gold K P R W}{x y z:ℝ}
namespace Grace
variable{V:Grace K P R}{X:Grasp V.U B e}
lemma blessed_B (p:Pearl X)(t:0<e):∃ Y:GivenX V X,Y.pearl=p:=by
 obtain ⟨C,h1,h2,h3,h4,F⟩:= V.aura p t; obtain ⟨z,u,i,H⟩:= sum_cost V.up V.gate V.note V.sp p V.a_o V.b_o V.d_o t V.tallX V.L C
 let N:=i+C.i+V.W.n; let a(m: Side)(p:N≤ m.val)(v:ℕ): V.L.Last X C m v:= Classical.choice (V.L.gives F (show C.i ≤ m.val from by unfold N at p; omega) v)
 exact ⟨⟨C,h1,h2,h3,h4,z,u,N,by unfold N; omega,p,t,F,fun {m}=>a m,fun {m} p k=> H (show i ≤ m.val from by unfold N at p; omega) k (a m p k)⟩,rfl⟩
end Grace
open Grace
lemma score_B(j n k:ℕ)(p:4 ≤ j)(h:Even j)(hp:6 ≤ n)(ht:2 ≤ k):∃ (K:Teller group) (Z:ChartRatio group), LocalRatio Z∧1 ≤ K.C∧K.j=j∧K.top.clip.direct ≤ 1∧(∀ P:RG.Patch, P.Branches K.bind group)∧ ∃ N:ℕ,∀ (P:RG.Patch),N ≤ P.L.val →P.J=j → ∃ (V:Grace K P Z)(T:Acorn.Repair K.j)(i:ℕ),∀ B:ℕ,i ≤ B→∃ e u0:ℝ,0<u0 ∧ 0<e ∧∀ y:ℝ,0<y → y≤ e →∃ (X:Grasp V.U (P.L^B) y)(G:GivenX V X), G.pearl.q=u0 ∧ y ≤ T.d∧ X.baseline ≤ T.d∧ T.n ≤ X.roundZ ∧∀ u:ℕ,∀ᶠ b:ℝ in atTop,∀ r:ℝ,0<r→Nonempty (Month b r n k u V G):=by
 obtain ⟨Z,Y⟩:= LocalH.actual group; obtain ⟨K,hK,z,u,w,N,H⟩:= sun j p h Z Y
 refine ⟨K,Z,Y,z,hK,u,w,N,fun P x t=>?_⟩; obtain ⟨F⟩:=H P x t; obtain ⟨D⟩:=Acorn.restoreX K.j (by omega); obtain ⟨i,h',v⟩:=spices_Bq F D 1
 refine ⟨F,D,i,fun B p=>?_⟩; obtain ⟨e,U,hU,g,f⟩:=v B p; refine ⟨e,U,hU,g,fun y z q=>?_⟩; obtain ⟨D',⟨P,hu⟩,a,b,c⟩:= f y z q; obtain ⟨R,v⟩:=blessed_B P z
 exact ⟨D',R,(by rw [v,hu]),a,b,c,fun i=> Month.existsX n k i hp ht F R⟩
end YM.CF.Vale
