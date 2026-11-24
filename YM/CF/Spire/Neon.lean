import YM.CF.Spire.Pianos
import YM.CF.Acorn.Swan
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Spire
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {j:ℕ}{L m B:Side}{ho:Odd L.val}{T:Script Male}{e:ℝ}{Y: Pricing j L ho T}
structure Pearl (g:Grasp Y B e) where
 q:ℝ
 r:ℝ
 hp:0<r
 wide:r ≤q
 roof:q ≤ g.baseline
 land : billK L.val e r < q
 chute : 8*(L.val:ℝ)*q <1/2
 small: 4/low*(q+q)< g.baseline
 ample : enoughV B e r
 tick(m:Side) : truckV (CSide m B) q g.baseline e
lemma loose (p w:ℝ)(h:0<p)(g:0<w)(L:Side): ∃ q:ℝ,0<q ∧ q≤ p ∧ q ≤ w∧ 8*(L.val:ℝ)*q<1/2 ∧ 4/low*(q+q)< w:=by
 let f:ℝ→ℝ:= fun x=>4/low*(x+x); let F:ℝ→ℝ:=fun x=>8*(L.val:ℝ)*x; have he: Continuous f:=by unfold f; fun_prop
 have hk:Continuous F:=by unfold F; fun_prop
 have hx:∀ᶠ i in 𝓝[>] (0:ℝ), i<p ∧ i<w ∧ F i < 1/2 ∧ f i < w := by
   apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
   exact Eventually.and (gt_mem_nhds h) (Eventually.and (gt_mem_nhds g) (Eventually.and (hk.continuousAt (gt_mem_nhds (show F 0<1/2 by simp [F]))) (he.continuousAt (gt_mem_nhds (show f 0<w by simpa [f])))))
 obtain ⟨a,u,l,k,b,c⟩:= ((show ∀ᶠ i in 𝓝[>] (0:ℝ),i∈ Set.Ioi 0 from self_mem_nhdsWithin).and hx).exists
 exact ⟨a,u,l.le,k.le,b,c⟩
-- schedule. choose high mesh all powers L divides B. reserve arbitrary e after high. HR Repair for locality.
lemma ava (Y:Pricing j L ho T)(R: Acorn.Repair j)(p:1≤j): ∃ N:ℕ, ∀ b:Side,N≤b.val→∃ W:ℕ, ∀ D:Side, W≤ D.val →∃ K:ℕ,∀ B:Side,K ≤B.val →(∃ F, B=b*F) → (∃ F,B=D*F)→∃ e:ℝ, 0<e ∧∀ f:ℝ, 0<f→f≤e→∃ g:Grasp Y B f, Nonempty (Pearl g) ∧ g.b=b∧ f ≤ R.d∧g.baseline≤R.d∧ R.n≤g.roundZ:=by
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
 refine ⟨a',lt_min g' (lt_min hr' hm),fun M hk h'=>?_⟩; have hx₁:M≤r':=h'.trans ((min_le_right ..).trans (min_le_left ..)); have hf:= h'.trans ((min_le_right ..).trans (min_le_right ..) : a'≤m)
 have hg:= hf.trans (min_le_right .. : m≤ min e w); have hl := hg.trans (min_le_right ..); have hx' := hf.trans (min_le_left .. : m≤min (min u q) c)
 have hv:=hx'.trans (min_le_left ..); have hd':= hQ.le.trans ((min_le_left ..).trans (min_le_left ..) : δ≤Y.e)
 have hh :billK L.val M u < δ:= (by
   apply lt_of_le_of_lt _ W; unfold billK; gcongr <;> exact hv.trans (min_le_left ..))
 have hh' :billK L.val M r'<r:= (by apply lt_of_le_of_lt _ hD'; unfold billK; gcongr)
 have hz₁:=Q M (hx'.trans (min_le_right ..)); let g:Grasp Y B M:= ⟨l,n,v,b',b,F,pB.symm,d,t,a,pA,k,p',u,h,H,hx.pull hk.le (hv.trans (min_le_right ..)), Q' _ hk.le (hg.trans (min_le_left ..)), ⟨hz₁.1,hz₁.2.trans_le (hu'.le.trans hB)⟩,(hv.trans (min_le_left ..)).trans hd',hQ.le.trans ((min_le_left ..).trans (min_le_right ..)),hd', hh.trans_le ((min_le_left ..).trans (min_le_right ..)),hh.trans_le ((min_le_left ..).trans (min_le_left ..)),by unfold b'; omega,by unfold b'; omega,by unfold b'; omega, fun N hx M=> (Wy N (le_trans (show v'≤ b' from by unfold b'; omega) hx) M).red hl⟩; have hu:g.baseline≤ R.d:=hQ.le.trans (min_le_right ..)
 refine ⟨g,⟨r,r',hr',hu'.le,hB,hh',B₁,B₂,hz₁,fun s=>?_⟩,rfl,(hv.trans (min_le_left ..)).trans hu,hu,show R.n≤b' from by unfold b'; omega⟩
 have he: CSide (s*B₀) D=CSide s B:=by rw [pD]; unfold CSide More; ac_rfl
 intro U V x' h y hy; exact hike (G'.pull hk.le (h'.trans (min_le_left ..))) he U V x' (fun i q=>(h i q).trans_le hR) y (fun i q=>(hy i q).trans_le hR)
namespace Pearl
variable {g: Grasp Y B e}(P:Pearl g){A:Side}(G:Ratio (CSide m B) (CSide A B))(h:G.count=L)(x:Nom (CSide m B) (CSide A B))(z: Stun (CSide m B))
include h P
lemma liftR (he:0<e)(u:g.roundZ≤(CSide m B).val)(p:JointB G x e)(hx:Slow x.2 (hook z) P.r):Slow x.1 (hook (ascend G z x.1)) P.q:=by
  have hl:=g.period.trans_le (g.clock_fine G u)
  let N:=CSide A B; have hm: 2*rankS G.count.val <(More N).val:=by rw [h]; change 2*_ < N.val*2; exact hl.trans_le (by unfold N; omega)
  intro a i; exact lt_of_le_of_lt (marchG G x _ _ p he.le z hx P.hp a i hm) (by rw [h]; exact P.land)
end Pearl
end YM.CF.Spire
