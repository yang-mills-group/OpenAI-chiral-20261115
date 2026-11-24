import YM.CF.Muse.Hark
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
/-- Capacity to impose a further post-divisor condition on the choices (unneeded for rate;
    provided for co-purchases in investigating the stronger paving estimate). -/
def AvailableΛ (F:ℕ→(s:Side)→Scree.Loom s→ Prop) :Prop :=∀ b d:ℝ,0<b→0<d→ ∃ N:ℕ,∀ B:Side,N≤B.val → ∃ k u l,0<u∧u ≤ b ∧∀ m:Side, (2:ℕ) ≤ Subtype.val m→ ∃ P,Roof (CSide m B) u d k P ∧ F l _ P
def RackedΛ (F:(s:Side)→Scree.Loom s→Prop)(J:Robes m X G):= ∀ (c:Side)(p:J.h≤ c.val), F _ (J.rack _ p)
lemma trueAvailable : AvailableΛ (fun _ _ _=>True):=by
 intro b d h t; obtain ⟨N,g⟩:= roofs_small b d h t; refine ⟨N,fun B v=>?_⟩; obtain ⟨k,u,p,i,f⟩:=g B v; exact ⟨k,u,0,p,i,fun m v=>let ⟨P,h⟩:= f m v; ⟨P,h,trivial⟩⟩
lemma equipForLaw {F_:ℕ→ (s:Side)→Scree.Loom s → Prop} (zF:AvailableΛ F_) (V:Grace K P R):∃ δ:ℝ,0<δ ∧∀ {e B}(u:Grasp V.U B e)(G:GivenX V u), e≤δ →∀ t:ℝ,0<t→ ∃ M:Side,∃ Q:Robes M V G,Q.k ≤ Q.roomX ∧ Q.d ≤ t ∧ ∃ i:ℕ, RackedΛ (F_ i) Q:=by
 have hw:= (Peaks.cup K.j P.L P.odd_side V.gate (by have he:=P.order_cut; have hx:=V.L.lobby; omega) (canUse K.j P.L P.odd_side) true).1; obtain ⟨a,b,c,g,h,t,v,W⟩:= hw
 refine ⟨c,t,fun {e B} G U hp tk zk=>?_⟩
 let L:=P.L; have he:=U.health
 obtain ⟨p,e1,hq,hv,hH,hx,tt,Y⟩:=smockK L (e/2) (half_pos he) tk zk
 obtain ⟨N,T⟩:=zF (e/2) p (half_pos he) hq
 let M:Side:=⟨N+1,by omega⟩; have hM:N≤M.val:=by unfold M; change N≤N+1; omega
 obtain ⟨k,f,l,t,u,J⟩:= T (M*B) (hM.trans (Nat.le_mul_of_pos_right _ B.property))
 let H:=U.n+G.roundZ+2*L.val+v+10
 have hc(c:Side): c.val ≤ (CSide (c*M) B).val:=by
    change _ ≤ _*M.val*2*B.val; apply le_trans (le_trans (Nat.le_mul_of_pos_right _ M.property) (Nat.le_mul_of_pos_right _ two_pos)) (Nat.le_mul_of_pos_right _ B.property)
 have hr(m:Side)(v:H ≤ m.val):∃ F:Scree.Loom (mid (m*M) B),Roof _ f (e/2) k F ∧ Roof _ f p k F ∧ F_ l _ F:=by
    obtain ⟨F,hF,hF_⟩:= J m (by change 2 ≤ m.val; unfold H at v; omega)
    have hg: Roof _ f (e/2) k F:= {hF with paid:=fun x=>(hF.paid x).shrink hv}
    rw [show Scree.mid (m*M) B= CSide m (M*B) by unfold Scree.mid CSide More; ac_rfl]; exact ⟨_,hg,hF,hF_⟩
 choose F V₀ V' Z' using hr
 refine ⟨M,⟨H,k,f,e1,e/2,t,hH,hx,half_lt_self he, ?_, ?_, F,V₀, ?_, ⟨v,a,b,c,W,(by unfold H; omega),hp⟩⟩,u,tt,l,@Z' ⟩
 · unfold H; omega
 · unfold H; omega
 intro c u p Z h q U R A; refine Y Z _ (by rw [h]; exact P.odd_side) h ?_ _ _ _ ((V' _ _).paid A); have he:=u.trans (hc _); change _<(CSide (c*M) B).val*2; unfold H at he; omega

end Grace
end YM.CF.Vale

