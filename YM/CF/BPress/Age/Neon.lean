import YM.CF.Spire.Neon

/- Adapted from FiniteGaugeData proofs in corresponding imported modules. Strengthening as in VolumeB-gate:
   keep q_P lower speed in same grant emitted while d, threshold still adjustable. This version is for
   B-main and any ordinary `MeterQ`, independent of comparison uses. -/
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Spire
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {j:ℕ}{L m B:Side}{ho:Odd L.val}{T:Script Male}{e:ℝ}{Y: Pricing j L ho T}
lemma avaP (Y:Pricing j L ho T)(R: Acorn.Repair j)(p:1≤j): ∃ N:ℕ, ∀ b:Side,N≤b.val→∃ W:ℕ, ∀ D:Side, W≤ D.val →∃ K:ℕ,∀ B:Side,K ≤B.val →(∃ F, B=b*F) → (∃ F,B=D*F)→∃ e u:ℝ,0<u∧ 0<e ∧∀ f:ℝ, 0<f→f≤e→∃ g:Grasp Y B f, (∃ V:Pearl g,V.q=u) ∧ g.b=b∧ f ≤ R.d∧g.baseline≤R.d∧ R.n≤g.roundZ:=by
 obtain ⟨l,d,a,t,v,n,pA,k,H⟩:=coin_v j p
 obtain ⟨N,V⟩:=resolve d H.posT
 refine ⟨N, fun b x=>?_⟩; obtain ⟨q,p',hp',hx⟩:= V b x
 let δ:=min (min Y.e p') R.d; have hd:0<δ:=lt_min (lt_min Y.range hx.pPositive) R.pd
 obtain ⟨u,h,hQ,W⟩:=kip L.val δ hd; obtain ⟨Z,HZ⟩:=resolve u h
 refine ⟨Z,fun D H'=>?_⟩; obtain ⟨e',w',g',G'⟩:=HZ D H'; obtain ⟨r,hr,hR,hB,B₁,B₂⟩:=loose w' u G'.pPositive h L; obtain ⟨r',hr',hu',hD'⟩:=kip L.val r hr
 obtain ⟨N',R'⟩:= scalable _ hr'; obtain ⟨x,A⟩:= all_room; refine ⟨max x N',?_⟩; intro B hP hb hF; obtain ⟨F,pB⟩:=hb; obtain ⟨B₀,pD⟩:=hF
 obtain ⟨c,r'',Q⟩:= R' B ((le_max_right ..).trans hP); obtain ⟨e,pE,Q'⟩:= A B ((le_max_left ..).trans hP); obtain ⟨w,pW,v',Wy⟩:= drift_l j p
 let m:=min (min (min u q) c) (min e w); let a':= min e' (min r' m); have hm:0<m:=lt_min (lt_min (lt_min h hp') r'') (lt_min pE pW)
 let b':=R.n+ v+v'+Y.N+(2*rankS L.val)+1
 refine ⟨a',r,hr,lt_min g' (lt_min hr' hm),fun M hk h'=>?_⟩; have hx₁:M≤r':=h'.trans ((min_le_right ..).trans (min_le_left ..)); have hf:= h'.trans ((min_le_right ..).trans (min_le_right ..) : a'≤m)
 have hg:= hf.trans (min_le_right .. : m≤ min e w); have hl := hg.trans (min_le_right ..); have hx' := hf.trans (min_le_left .. : m≤min (min u q) c)
 have hv:=hx'.trans (min_le_left ..); have hd':= hQ.le.trans ((min_le_left ..).trans (min_le_left ..) : δ≤Y.e)
 have hh :billK L.val M u < δ:= (by
   apply lt_of_le_of_lt _ W; unfold billK; gcongr <;> exact hv.trans (min_le_left ..))
 have hh' :billK L.val M r'<r:= (by apply lt_of_le_of_lt _ hD'; unfold billK; gcongr)
 have hz₁:=Q M (hx'.trans (min_le_right ..)); let g:Grasp Y B M:= ⟨l,n,v,b',b,F,pB.symm,d,t,a,pA,k,p',u,h,H,hx.pull hk.le (hv.trans (min_le_right ..)), Q' _ hk.le (hg.trans (min_le_left ..)), ⟨hz₁.1,hz₁.2.trans_le (hu'.le.trans hB)⟩,(hv.trans (min_le_left ..)).trans hd',hQ.le.trans ((min_le_left ..).trans (min_le_right ..)),hd', hh.trans_le ((min_le_left ..).trans (min_le_right ..)),hh.trans_le ((min_le_left ..).trans (min_le_left ..)),by unfold b'; omega,by unfold b'; omega,by unfold b'; omega, fun N hx M=> (Wy N (le_trans (show v'≤ b' from by unfold b'; omega) hx) M).red hl⟩; have hu:g.baseline≤ R.d:=hQ.le.trans (min_le_right ..)
 refine ⟨g,⟨⟨r,r',hr',hu'.le,hB,hh',B₁,B₂,hz₁,fun s=>?_⟩,rfl⟩,rfl,(hv.trans (min_le_left ..)).trans hu,hu,show R.n≤b' from by unfold b'; omega⟩
 have he: CSide (s*B₀) D=CSide s B:=by rw [pD]; unfold CSide More; ac_rfl
 intro U V x' h y hy; exact hike (G'.pull hk.le (h'.trans (min_le_left ..))) he U V x' (fun i q=>(h i q).trans_le hR) y (fun i q=>(hy i q).trans_le hR)

end YM.CF.Spire
