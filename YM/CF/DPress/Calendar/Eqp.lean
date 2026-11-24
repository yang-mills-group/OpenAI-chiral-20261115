import YM.CF.DPress.FD.Issue
import YM.CF.Muse.Hark
/-! Adapt the FiniteGaugeData prechoice proofs, buying Firm with the Robes data. -/
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
open DPress.FD
abbrev Embark {M:Side} (J:Robes (K:=K) (P:=P) M X G) :Prop:=∀ n h,DPress.FD.Firm (J.rack n h) J.k J.n
lemma equipD (V:Grace K P R):∃ δ:ℝ,0<δ ∧∀ {e B}(u:Grasp V.U B e)(G:GivenX V u), e≤δ →∀ t:ℝ,0<t→ ∃ M:Side,∃ Q:Robes M V G,Q.k ≤ Q.roomX ∧ Q.d ≤ t ∧ Embark Q:=by
 have hw:= (Peaks.cup K.j P.L P.odd_side V.gate (by have he:=P.order_cut; have hx:=V.L.lobby; omega) (canUse K.j P.L P.odd_side) true).1; obtain ⟨a,b,c,g,h,t,v,W⟩:= hw
 refine ⟨c,t,fun {e B} G U hp tk zk=>?_⟩
 let L:=P.L; have he:=U.health
 obtain ⟨p,e1,hq,hv,hH,hx,tt,Y⟩:=smockK L (e/2) (half_pos he) tk zk
 obtain ⟨f,t,u,k,N,T⟩:=DPress.FD.booth hq (e/2) (half_pos he)
 let M:Side:=⟨N+1,by omega⟩; have hM:N≤M.val:=by unfold M; change N≤N+1; omega
 let H:=U.n+G.roundZ+2*L.val+v+N+10
 have hc(c:Side): c.val ≤ (CSide (c*M) B).val:=by
    change _ ≤ _*M.val*2*B.val; apply le_trans (le_trans (Nat.le_mul_of_pos_right _ M.property) (Nat.le_mul_of_pos_right _ two_pos)) (Nat.le_mul_of_pos_right _ B.property)
 have hr(m:Side)(v:H ≤ m.val):∃ F:Scree.Loom (mid (m*M) B),Roof _ f (e/2) k F ∧ Roof _ f p k F ∧ DPress.FD.Firm F f k:=by
    have he:N < m.val:=by unfold H at v; omega
    have hp: N < (Scree.mid (m*M) B).val:=he.trans_le (hc _); obtain ⟨F,hF,t⟩:= T (mid (m*M) B) (hp.trans_le (Nat.le_mul_of_pos_right _ (show 0 < (2:Lattice.Side).val from by exact two_pos)))
    have hg: Roof _ f (e/2) k F:= {hF with paid:=fun x=>(hF.paid x).shrink hv}
    exact ⟨_,hg,hF,t⟩
 choose F V₀ V' VL using hr
 refine ⟨M,⟨H,k,f,e1,e/2,t,hH,hx,half_lt_self he, ?_, ?_, F,V₀, ?_, ⟨v,a,b,c,W,(by unfold H; omega),hp⟩⟩,u,tt,VL⟩ -- placeholders
 · unfold H; omega
 · unfold H; omega
 intro c u p Z h q U R A; refine Y Z _ (by rw [h]; exact P.odd_side) h ?_ _ _ _ ((V' _ _).paid A); have he:=u.trans (hc _); change _<(CSide (c*M) B).val*2; unfold H at he; omega
-- cap used at any mesh c*L^i
end Grace
end YM.CF.Vale

