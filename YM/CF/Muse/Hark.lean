import YM.CF.Stake.Robe
import YM.CF.Skye.Knit
set_option autoImplicit false
noncomputable section
namespace YM.CF.Skye
open Function Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n m:Side}{u d e a:ℝ}{r:ℕ}(q:Chi)
-- clipping chord to replica through forest
lemma narrowK (C:ℝ)(hC:0<C)(a:ℝ)(t:0<a):∃ d:ℝ,0<d ∧2*d< firstRadius group∧d ≤ C∧∀ q:Chi,∀ x y:E, ‖brand (knit q d x y)-brand y‖≤ a:=by
 let f:= brand ∘ group.lieExp
 have h:Continuous f:= Dial.spinD.comp group.lieExp_cont -- tune
 have ht: Tendsto f (𝓝 0) (𝓝 1):=by have ht:= h.tendsto 0; rw [show f 0=1 by simp [f, brand_one]] at ht; exact ht
 obtain ⟨k,he,hP⟩:=Metric.mem_nhds_iff.mp (ht.eventually (ball_mem_nhds 1 t))
 let d:= min k (min C (firstRadius group)); have hp:0<d:=lt_min he (lt_min hC (first_pos _))
 refine ⟨d/3,by positivity,by linarith [show d≤firstRadius group from le_trans (min_le_right ..) (min_le_right ..)],by linarith [show d≤C from le_trans (min_le_right ..) (min_le_left ..)],fun q x y=>?_⟩
 let z:=patched q (d/3) (x*y⁻¹); rw [knit, brand_mul,show _*brand y-brand y=(f z-1)*star (brand y⁻¹) by rw [brand_inv,star_star, sub_mul,one_mul]; rfl,brand_rig]; exact (mem_ball_iff_norm.mp (show f z∈ball _ a from hP (show z ∈ ball 0 k from mem_ball_iff_norm.mpr (by rw [sub_zero]; apply lt_of_le_of_lt (patched_small q (by positivity) _); linarith [show d≤k from min_le_left ..])))).le -- tune
theorem smockK(L:Side)(e:ℝ)(p:0<e)(E:ℝ)(hE:0<E):∃ u d:ℝ,0<u∧u≤e∧0<d∧ 2*d< firstRadius group∧d ≤ E∧∀ {n m:Side}(G:Ratio n m)(F:Forest (ratio G)), Odd G.count.val→G.count=L→max 8 (2*L.val)<(More n).val→∀ (q:Chi)(W:Pane m)(V:Pane n),Guard V u→JointB G (seine G F q d W V,V) e:=by
 let u:= e/128; let a:=u/(L.val:ℝ); have hu:0<u:=(by positivity); have ht:0<a:=(by positivity); obtain ⟨b,h,k,v,H⟩:=narrowK E hE a ht
 refine ⟨u,b,hu,by unfold u; linarith,h,k,v,fun G F hx hs hg q W V t=>cycleY q G F V W hx t hu.le ((le_max_left ..).trans_lt hg) (hs.symm ▸ (le_max_right ..|>.trans_lt hg)) ?_ ?_ ?_ (H q)⟩
 all_goals have hy:1≤ (L.val:ℝ):=by exact_mod_cast (L.property : 1≤ L.val)
 · have hf:a≤u:= div_le_self hu.le hy; unfold u at *; linarith
 · rw [hs]; unfold a; rw [mul_div_cancel₀ _ (lt_of_lt_of_le one_pos hy).ne']; unfold u; linarith
 unfold u; linarith
end YM.CF.Skye

end

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option quotPrecheck false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.Vale
open Function Filter Lattice Laurent Bloch Wilson Precision Tree Finset Exterior Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Pec Next.Free Pressure Cascade Reef Hom Push.SectorMeasure Next.SectorChange
open MeasureTheory Metric Skye Scree Grace
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {K:Teller group}{P:RG.Patch}{R:ChartRatio group}{W:Postal}{η e:ℝ}{n k v i:ℕ}{f g a b d w:ℝ}{B m c u:Side}{C:Credit}
variable {X:Grace K P R}{U: Pricing K.j P.L P.odd_side (Thread K.j)} {D:Grasp U B e}{S:Gold K P R W}{x y z:ℝ}
namespace Grace
variable {X' :Grasp X.U B e}{G:GivenX X X'}
lemma equipK (V:Grace K P R):∃ δ:ℝ,0<δ ∧∀ {e B}(u:Grasp V.U B e)(G:GivenX V u), e≤δ →∀ t:ℝ,0<t→ ∃ M:Side,∃ Q:Robes M V G,Q.k ≤ Q.roomX ∧ Q.d ≤ t:=by
 have hw:= (Peaks.cup K.j P.L P.odd_side V.gate (by have he:=P.order_cut; have hx:=V.L.lobby; omega) (canUse K.j P.L P.odd_side) true).1; obtain ⟨a,b,c,g,h,t,v,W⟩:= hw
 refine ⟨c,t,fun {e B} G U hp tk zk=>?_⟩
 let L:=P.L; have he:=U.health
 obtain ⟨p,e1,hq,hv,hH,hx,tt,Y⟩:=smockK L (e/2) (half_pos he) tk zk
 obtain ⟨N,T⟩:=roofs_small (e/2) p (half_pos he) hq
 let M:Side:=⟨N+1,by omega⟩; have hM:N≤M.val:=by unfold M; change N≤N+1; omega
 obtain ⟨k,f,t,u,J⟩:= T (M*B) (hM.trans (Nat.le_mul_of_pos_right _ B.property))
 let H:=U.n+G.roundZ+2*L.val+v+10
 have hc(c:Side): c.val ≤ (CSide (c*M) B).val:=by
    change _ ≤ _*M.val*2*B.val; apply le_trans (le_trans (Nat.le_mul_of_pos_right _ M.property) (Nat.le_mul_of_pos_right _ two_pos)) (Nat.le_mul_of_pos_right _ B.property)
 have hr(m:Side)(v:H ≤ m.val):∃ F:Scree.Loom (mid (m*M) B),Roof _ f (e/2) k F ∧ Roof _ f p k F:=by
    obtain ⟨F,hF⟩:= J m (by unfold H at v; omega)
    have hg: Roof _ f (e/2) k F:= {hF with paid:=fun x=>(hF.paid x).shrink hv}
    rw [show Scree.mid (m*M) B= CSide m (M*B) by unfold Scree.mid CSide More; ac_rfl]; exact ⟨_,hg,hF⟩
 choose F V₀ V' using hr
 refine ⟨M,⟨H,k,f,e1,e/2,t,hH,hx,half_lt_self he, ?_, ?_, F,V₀, ?_, ⟨v,a,b,c,W,(by unfold H; omega),hp⟩⟩,u,tt⟩ -- placeholders
 · unfold H; omega
 · unfold H; omega
 intro c u p Z h q U R A; refine Y Z _ (by rw [h]; exact P.odd_side) h ?_ _ _ _ ((V' _ _).paid A); have he:=u.trans (hc _); change _<(CSide (c*M) B).val*2; unfold H at he; omega
-- cap used at any mesh c*L^i
end Grace
end YM.CF.Vale

