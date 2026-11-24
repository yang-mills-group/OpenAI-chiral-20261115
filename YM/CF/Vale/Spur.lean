import YM.CF.Vale.Archer
import YM.CF.Girt.Tree
import YM.CF.Rue.River
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
structure Robes (M:Side) (X:Grace K P R){X':Grasp X.U B e}(G:GivenX X X') where
 h:ℕ
 n:ℕ
 k:ℝ -- mask threshold absolute, post e small
 d:ℝ
 roomX:ℝ
 ht:0<k
 hv:0<d
 knot:2*d<firstRadius group
 hr:roomX<e
 ware: G.n≤h
 gran: X'.roundZ≤h
 rack (N:Side)(g:h≤ N.val): Scree.Loom (mid (N*M) B)
 roof(N H): Roof _ k roomX n (rack N H) -- syntax cast
 tick{c:Side}(g:h ≤ c.val)(p: h ≤ (c*P.L).val)(H:Ratio (mid (c*M) B) (mid (c*P.L*M) B))(z:H.count=P.L): ∀(q:Chi)(u:Pane (mid (c*P.L*M) B))(F:Forest (ratio H))(v:Orbit _), JointB H (seine H F q d u (rack c g v),rack c g v) roomX
 seed:∃ (s:ℕ)(a w d:ℝ), Tax P.L (ticketT (Thread K.j) true) false true a w s d ∧ s≤h ∧ e≤d
-- cap solution uses a *later* Loom mesh, enlarged IR periods only. Width harmless.
lemma equip (V:Grace K P R):∃ δ:ℝ,0<δ ∧∀ {e B}(u:Grasp V.U B e)(G:GivenX V u), e≤δ →∃ M:Side,Nonempty (Robes M V G):=by
 have hw:= (Peaks.cup K.j P.L P.odd_side V.gate (by have he:=P.order_cut; have hx:=V.L.lobby; omega) (canUse K.j P.L P.odd_side) true).1; obtain ⟨a,b,c,g,h,t,v,W⟩:= hw
 refine ⟨c,t,fun {e B} G U hp=>?_⟩
 let L:=P.L; have he:=U.health
 obtain ⟨p,e1,hq,hv,hH,hx,Y⟩:=smock L (e/2) (half_pos he)
 obtain ⟨N,T⟩:=roofs p hq
 let M:Side:=⟨N+1,by omega⟩; have hM:N≤M.val:=by unfold M; change N≤N+1; omega
 obtain ⟨k,f,t,J⟩:= T (M*B) (hM.trans (Nat.le_mul_of_pos_right _ B.property))
 let H:=U.n+G.roundZ+2*L.val+v+10
 have hc(c:Side): c.val ≤ (CSide (c*M) B).val:=by
    change _ ≤ _*M.val*2*B.val; apply le_trans (le_trans (Nat.le_mul_of_pos_right _ M.property) (Nat.le_mul_of_pos_right _ two_pos)) (Nat.le_mul_of_pos_right _ B.property)
 have hr(m:Side)(v:H ≤ m.val):∃ F:Scree.Loom (mid (m*M) B),Roof _ f (e/2) k F ∧ Roof _ f p k F:=by
    obtain ⟨F,hF⟩:= J m (by unfold H at v; omega)
    have hg: Roof _ f (e/2) k F:= {hF with paid:=fun x=>(hF.paid x).shrink hv}
    rw [show Scree.mid (m*M) B= CSide m (M*B) by unfold Scree.mid CSide More; ac_rfl]; exact ⟨_,hg,hF⟩
 choose F V₀ V' using hr
 refine ⟨M,⟨H,k,f,e1,e/2,t,hH,hx,half_lt_self he, ?_, ?_, F,V₀, ?_, ⟨v,a,b,c,W,(by unfold H; omega),hp⟩⟩⟩ -- placeholders
 · unfold H; omega
 · unfold H; omega
 intro c u p Z h q U R A; refine Y Z _ (by rw [h]; exact P.odd_side) h ?_ _ _ _ ((V' _ _).paid A); have he:=u.trans (hc _); change _<(CSide (c*M) B).val*2; unfold H at he; omega
-- cap used at any mesh c*L^i
namespace Robes
variable {M:Side}(D:Robes M X G)
lemma berth(N:Side)(g:D.h ≤ N.val):Roof _ D.k e D.n (D.rack N g):=let h:=D.roof N g;{h with paid:=fun x=>(h.paid x).shrink D.hr.le}
lemma hold {c:Side}(g:D.h ≤ c.val)(p:D.h ≤ (c*P.L).val)(Y:GramM (mid (c*P.L*M) B))(y:∃ a b c d:ℝ,Y.J.P.toll a b c d)(F:Girt.Ward Y)(H:Ratio (mid (c*M) B) (mid (c*P.L*M) B))(z:H.count=P.L)(q:Chi): Nonempty (Girt.BaseL X' H Y (D.rack c g) (D.rack _ p) q D.d):=by
 have hr:D.h ≤ (CSide (c*M) B).val:=by change _ ≤ c.val*M.val*2*B.val; exact g.trans (le_trans (le_trans (Nat.le_mul_of_pos_right _ M.property) (Nat.le_mul_of_pos_right _ two_pos)) (Nat.le_mul_of_pos_right _ B.property))
 refine ⟨⟨G.pearl,X.note,z,G.health,?_, D.gran.trans hr, ?_,y,⟨_,_,_,D.berth _ g,D.berth _ p⟩,⟨D.hv,D.knot⟩,fun i j v=>?_,F⟩⟩
 · have he:= X.L.lobby; have ht:= P.order_cut; omega
 · obtain ⟨n,a,b,m,x,h,g⟩:= D.seed; exact ⟨n,a,b,m,x,h.trans hr,g⟩
 have ht:= D.tick g p H z q j i v; exact ⟨ht.fg.shrink D.hr.le,ht.cg.shrink D.hr.le,fun v=>(ht.follow v).trans D.hr.le⟩
end Robes
end Grace
end YM.CF.Vale
