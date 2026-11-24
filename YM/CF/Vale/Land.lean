import YM.CF.Vale.Sail
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Vale
open Function Filter Lattice Laurent Bloch Wilson Precision Tree Finset Exterior Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Pec Next.Free Pressure Cascade Reef Hom PhysicalNext.JointLoad.Heir Push.SectorMeasure Next.SectorChange
open MeasureTheory Metric Skye Scree Grace Pastry
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
variable {K:Teller group}{P:RG.Patch}{R:ChartRatio group}{W:Postal}{η e:ℝ}{n k v i:ℕ}{f g a b d w:ℝ}{B m N M: Side}{C:Credit}
variable {V:Grace K P R}{X:Grasp V.U B e}{G: V.GivenX X}{x y z:ℝ}
namespace Grace.Robes
variable (F:Robes M V G)
lemma stretch (p:F.h≤ m.val)(i:ℕ): F.h ≤ (mesh m P.L i).val:=p.trans (Nat.le_mul_of_pos_right _ (P.L^i).property)
variable {F}
lemma solar (x:Skye.Orbit N)(T:Scree.Loom N)(h:Roof N d e k T)(L:RG.BudgetPoint)(v:L.threshold ≤ d)(p:RG.flags L.threshold x.1=∅): T x=x.1:=by
 have he:RG.flags d x.1=∅:=by
    rw [←Finset.subset_empty]; intro i hi; obtain ⟨l,u,w⟩:= (RG.flags_spec ..).mp hi; exact p ▸ ((RG.flags_spec ..).mpr ⟨l,u,v.trans_lt w⟩)
 funext i; exact h.lamp x.1 x.2 _ (by simp [he])
lemma markSeas {U:Pane (CSide m B)}(T:Scree.Loom (CSide m B))(h:Roof (CSide m B) x e k T)(p:RG.BudgetPoint)(t:p.threshold≤x)(hx: X.roundZ ≤ (CSide m B).val)(hv:RG.flags p.threshold U=∅): spar K.j babyM U=portW (helix _).symm (Phase.lens m B (Brace.northZ m B) U) ∧ Sea (spar K.j babyM U) (changeM X U babyM):=by
 let A:Ids (CSide m B):=Classical.arbitrary _
 have hh: T (U,A)=U:=solar (U,A) T h p t hv; have ht:Guard U e:= hh ▸ h.paid (U,A)
 exact ⟨Brace.frame_init X.topB X.baseY (X.couture hx _) ht,sea_g hx U ht _⟩
variable (F)
-- stage only; stitch by Mesh i=h etc later
lemma soaring (qu:RG.BudgetPoint)(p:qu.threshold ≤ F.k)(c:Side)(h:F.h ≤ c.val)(b:ℝ)(hx:K.top.clip.direct ≤1):
 let N:=c*M; let Vv:= CSide N B; RG.Envelope (denZ (launch V.L b qu Vv) X (F.rack c h)) ∧ (∀ W:Skye.Orbit Vv,denZ (launch V.L b qu Vv) X (F.rack c h) W= capP X b qu W.1) ∧ (∀ U:Pane Vv, RG.flags qu.threshold U=∅→spar K.j babyM U=portW (helix _).symm (Phase.lens N B (Brace.northZ N B) U)∧Sea (spar K.j babyM U) (changeM X U babyM)):=by
 intro N Y; have ht:F.h ≤ (CSide N B).val:=by change _ ≤ c.val*M.val*2*B.val; exact h.trans (le_trans (le_trans (Nat.le_mul_of_pos_right _ M.property) (Nat.le_mul_of_pos_right _ two_pos)) (Nat.le_mul_of_pos_right _ B.property))
 have he:X.roundZ≤ Y.val:= F.gran.trans ht
 exact ⟨Girt.sailW _ (wing_h ..) G.pearl V.note G.health (by have he:=V.L.lobby; have hv:=P.order_cut; omega) F.n _ (F.berth c h) he,core_b X V.L b qu _ _ (F.berth c h) p hx he,fun U hQ=>markSeas _ (F.berth c h) qu p he hQ⟩ -- order
end Grace.Robes
lemma Months_at {G:V.GivenX X}(h:Robes M V G)(z N:ℕ)(p:6 ≤ z)(u:2 ≤ N)(c:ℝ)(j:ℕ):∃ y:ℝ,c<y ∧ ∀ s:ℝ,0<s →∃ A:Month y s z N j V G,(∀ i,(A.a i).threshold ≤ h.k) ∧ (∀ i,Rue.IsleB group (A.a i).threshold):=by
 obtain ⟨v,hv⟩:= eventually_atTop.mp (Month.existsX z N j p u V G)
 have he:Tendsto Pressure.temp atTop (𝓝 0):=by simpa using Work.E09.radiusB_temp 0
 obtain ⟨x,hx⟩:=eventually_atTop.mp (he.eventually (ge_mem_nhds h.ht))
 obtain ⟨s,hs,ht⟩:=Rue.inherits group (max c (max v x)) _ (pitch P.L)
 refine ⟨s,(le_max_left ..).trans_lt hs,fun b p=>?_⟩; obtain ⟨Q⟩:= hv s ((le_max_left ..).trans ((le_max_right ..).trans hs.le)) _ p
 refine ⟨Q,fun i=>?_,fun i=>?_⟩
 · rw [(Q.boot i).1]; exact hx _ ((le_max_right ..).trans ((le_max_right ..).trans (hs.le.trans (crown P.L s i))))
 rw [(Q.boot i).1]; exact ht i
end YM.CF.Vale
