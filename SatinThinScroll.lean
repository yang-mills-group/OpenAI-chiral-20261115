import SatinThinBeacon
import SatinThinThimble

set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.QuadClock
open Neon
open Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew Waxy Roots Rive Oise


/- Complete and re-price; exact connection. -/
variable {J I: Type}[Fintype J][Fintype I][LinearOrder J][LinearOrder I]
attribute [-instance] instDecidableEqLex
variable {N P B: Side}{R:Patch}{K:Teller SU.group}{L:ChartRatio SU.group}
  (V:Grace K R L) {d A q t s T u h C BQ KX KY W M Vp Va κp b g r:ℝ}{x: ℕ}
  (P_:Grasp V.U B d)(X:GramM (mid N B))(Y:GramM (mid P B)) (G:Ratio (mid N B) (mid P B))
   (S:StepData (Domain N B) (Domain P B))(G₀: Scree.Loom (mid N B))(G₁: Scree.Loom (mid P B))(Xp:Op SU.Slot)(q':Chi)
variable {n:Side}
def dayShift (X:GramM n)(E:Key J→RegBudget n)(F:Key J→ ForceBudget n) (z:Key J):GramM n:= color_b X X.beta (X.F+E z) X.slip (X.K+F z) X.v
local notation "Ω"=>mid N B
local notation "Ξ"=> mid P B
variable (E:Key (Article I)→ RegBudget (mid P B))(F:Key (Article I)→ ForceBudget (mid P B)) (V':Fin 2→ Topic (mid P B))(σ:I→Site (mid N B))
local notation "Hc"=> Thimble
local notation "G1"=> Hove.heel G ∘ σ
variable (T_:Thimble (duty_Q X.p.order X.p.power*W) BQ A q s M Va κp R.L X.p) (street:Y.slip=0)(p:Arc_r Y h r r r) (hM:16*A*q ≤ g)(h0:r+16*A*q ≤ b)(store:Girt.BaseL P_ G Y G₀ G₁ q' u)(hS:S.ratio=ratio G)(hBr:S.patch.Branches S.kernel SU.group) (pσ:Very_Ψ σ X.p.B)
variable {S_:Foyer V P_ G S G₀ G₁ X Y Xp q' u h Vp Va M W C BQ KX KY b g κp 2}
def dampE {U:Type*}[Zero U](E:Key J→ U)(z:Key J):U:= if z∈ hill J then E z else 0
local notation "Λh"=>Key (Article I)
local notation "Yo"=> fun z: Key (Article I)=> Y.F+dampE E z
local notation "Yy"=> fun z: Key (Article I)=> Y.K+dampE F z
local notation "Wκ"=>fun i:Article I=> readFee q (layer i)
local notation "Dψ"=> fun _:Article I=> A*q
local notation "Δψ"=> fun i:Article I=>V' (layer i)
local notation "Σψ"=> treeO σ
variable (l:Bulletin R.L Y (Hove.heel G ∘ σ) E F h 1 (16*A) A q V')
include T_ street p hM h0 l pσ
lemma seek_φ (hω:∀ i:Site (mid P B), nun_ω Y.F i=(t:ℂ))(v:|t| ≤ Real.exp 1): Tripulse G X Y h b g R.L (treeO σ) Yo Yy Δψ Wκ Dψ 2:=by
 let E':= dampE E; let F':= dampE F; have he(z:Λh)(u:z∈hill (Article I)): E' z = E z∧ F' z= F z:= ⟨if_pos u,if_pos u⟩
 let H(z:Λh):= Y.F+E' z; let H'(z:Λh):= Y.K+F' z
 have v0:H 0=Y.F ∧ H' 0=Y.K:=by unfold H H'; rw [(he _ roots).1,(he _ roots).2,l.roll.1,l.roll.2]; simp
 have hF(i): νTip H i=νTip E i:=by
    funext x y; refine (lace_C [i] (f:=fun z=> H z x y) (g:=fun z=>Y.F x y+ E z x y) ?_ roots).trans ((tip_A (zeroR _) (river_all (fun z=>E z x y) (l.varE _ _)) [i]).trans ?_); · exact fun z v=> by dsimp only [H]; rw [(he z v).1]; rfl
    rw [proper,zero_add]
 have hE(i): emberTip H' i=emberTip F i:=by
    funext x y; refine (lace_C [i] (f:=fun z=> H' z x y) (g:=fun z=>Y.K x y+ F z x y) ?_ roots).trans ((tip_A (zeroR _) (river_all (fun z=>F z x y) (l.varF _ _)) [i]).trans ?_); · exact fun z v=> by dsimp only [H']; rw [(he z v).2]; rfl
    rw [proper,zero_add]
 have h1:0<q:=T_.q_pos; have hq:=T_.bought.root
 have hx:0≤ A:= zero_le_one.trans hq; have hv:0≤16*A*q:=by positivity
 have hb:=le_trans (show r≤r+16*A*q from le_add_of_nonneg_right hv) h0
 refine ⟨?_,double_gap σ R.L X.p pσ T_.belt,fun i=> ?_,fun i=>hF i|>.symm ▸ (l.boss i).1,fun i=> (?_: (V' (layer i)).face _ (νTip H i) (emberTip H' i)),fun i x u=>?_,fun i x u=>?_⟩
 · constructor
   · exact ⟨v0.1,street.symm,v0.2⟩
   · intro i; refine ⟨fun c a b t x=>?_,fun c a b t x=>rfl,fun x=> ⟨(dub_V (zeroR (Y.F i x)) (river_all (fun z=>E z i x) (l.varE _ _))).cong (fun c a=>?_), zeroR _⟩⟩
     · change (Y.F+ E' c) _=(Y.F+E' b) _; rw [(he c a).1,(he b t).1,Pi.add_apply,Pi.add_apply]; exact congrArg (Y.F i + ·) (l.col i c b x)
     change (Y.F+E' c) i x= _; rw [(he c a).1]; rfl
   · intro i; refine ⟨fun c a b t x=>?_,fun x=> (dub_V (zeroR (Y.K i x)) (river_all (fun z=> F z i x) (l.varF _ _))).cong (fun c a=>?_)⟩
     · change (Y.K+ F' c) _=(Y.K+F' b) _; rw [(he c a).2,(he b t).2,Pi.add_apply,Pi.add_apply]; exact congrArg (Y.K i+·) (l.joinF i c b x)
     change (Y.K+F' c) i x=_; rw [(he c a).2]; rfl
   intro z; constructor
   · by_cases t:z∈hill (Article I); · change IncX primeU (Y.F+ E' z) Y.p h b; rw [(he z t).1]; exact Provides.liftE h Y _ _ (Larch.add_v _ _ _ p.1 (l.cover z (hill_i.mp t)).1) h0
     change IncX _ (Y.F+ E' z) _ _ _; rw [show E' z=0 from if_neg t,add_zero]; exact Provides.liftE h Y _ _ p.1 hb
   · change IncX primeU 0 Y.p h b; rw [←street]; exact Provides.liftE h Y _ _ p.2 hb
   by_cases t:z∈hill (Article I); · change Dark primeU (Y.K+ F' z) Y.p h b; rw [(he z t).2]; exact Provides.liftQ h Y _ _ (union_F _ p.3 (l.cover z (hill_i.mp t)).2) h0
   change Dark _ (Y.K+ F' z) _ _ _; rw [show F' z=0 from if_neg t,add_zero]; exact Provides.liftQ h Y _ _ p.3 hb
 · let b:=readFee q (layer i); have hu:|b| ≤q:=by unfold b readFee; split; rw [abs_of_pos h1]; simpa using h1.le
   have hz:0≤g:=hv.trans hM
   rw [hω]; constructor
   · exact ⟨mul_nonneg hx h1.le, (show A*q ≤ 16*A*q from mul_le_mul_of_nonneg_right (by linarith) h1.le).trans hM⟩
   · change ‖(t:ℂ)‖* ‖(PointSk b).1‖≤g; rw [choice_slot,Complex.norm_real,Real.norm_eq_abs]; exact (mul_le_mul (peg_ub v) hu (abs_nonneg _) (by norm_num)).trans ((mul_le_mul_of_nonneg_right (by linarith only [hq]) h1.le).trans hM)
   · simpa [PointSk] using hz
   simpa [PointSk] using hz
 · -- placeholder auto generated for face goal
   rw [hF i,hE i]; exact (l.boss i).2
 · have he0:=realKey_mem i x u; change Y.F+E' _= H 0+_ • νTip H i; rw [(he _ he0).1,hF i,v0.1,(l.head i (x:ℂ)).1, Complex.coe_smul]
 · have he0:=realKey_mem i x u; change Y.K+F' _= H' 0+_ • emberTip H' i; rw [(he _ he0).2,hE i,v0.2,(l.head i (x:ℂ)).2,Complex.coe_smul]

/- density identity across step at sparse list. -/
structure Flight (p:I→Site (mid N B))(D:Funds R.L)(E' :Key (Article I)→RegBudget (mid N B))(F':Key (Article I)→ForceBudget (mid N B)) : Prop where
 boom: ∀ l:List (Article I), Roots.ψS (Cube.node ∘ treeO p) l→∀ x:Orbit (mid N B), Rue.FleetS X.p.threshold x.1 → Mew.tipI (fun z:Key (Article I)=> Scree.denZ (dayShift X E' F' z) P_ G₀ x) l=Roots.snow (Cube.node ∘ treeO p) (TicketM R.L D) (fun t=> ∫ v: Orbit (mid P B), lynx K S G G₁ G₁ G₀ Y q' u Xp x v (Mew.tipI (fun z:Key (Article I)=>Scree.denZ (dayShift Y E F z) P_ G₁ v) t) ∂city _) l
-- maybe lynx in Py not Roots
local notation "pκ"=> PointSk ∘ fun i:Article I=> readFee q (layer i)
local notation "duty"=> duty_Q X.p.order X.p.power*W
variable {o:TopicScheme (mid P B) (mid N B)}
local notation "X'"=> GroupPay o V' A q
local notation "rank'''"=> fun i:Article I=> (GroupPay o V' A q (layer i))
local notation "Dq"=> warpLine o V' R.L A q s
local notation "XU"=> hatchTopic R.L o V' A q s
local notation "Τ"=> TicketM R.L Dq
variable {E':Key (Article I)→ RegBudget (mid N B)}{Yf:Key (Article I)→ForceBudget (mid N B)}
omit street p hM h0 l
variable(hB: Cause_P V P_ G S G₀ G₁ X Y (fun z => Y.F+dampE E z) 0 (fun z=> Y.K+dampE F z) Xp q' u h Vp Va (treeO σ) (fun _=> A*q) (PointSk ∘ fun i:Article I=> readFee q (layer i)) E' Yf (fun i=>PointSk (GroupPay o V' A q (layer i))) 0 M (duty_Q X.p.order X.p.power*W) C BQ KX KY κp)
local notation "Xκ"=>FlameX (treeO σ) E' (TicketM R.L Dq)
local notation "Yκ"=> FlameK (treeO σ) Yf (TicketM R.L Dq)
variable (tc: ∀ i:Article I,(groupTopic o V' A q (layer i)).face (treeO σ i) (νTip E' i) (emberTip Yf i))
include hB tc S_
lemma stable_E : Bulletin R.L X σ Xκ Yκ h 2 (4*A) (A/8) s XU ∧ PanoramaBill X.p h (2*s⁻¹) s (2*A) Xκ Yκ :=by
 obtain ⟨t,he,p,r⟩:=S_.life; have u:= S_.sun; have v:= S_.rate
 let Tψ:=fun i:Article I=> PointSk (readFee s (layer i)); let uΦ(i):= spark_emit X σ V V' Yo Yy hB T_ pσ v.1 v.2 u he p r tc i
 have vx:=double_force σ X.p pσ; let L:=compassκ R.L; have hs:= T_.q_pos.trans_le T_.span; have hb:=T_.bought.root; have hg:= mul_nonneg (show 0 ≤ A/8 from by linarith) hs.le; have hp:=compass_pos R.L; have hL:0<L:=zero_lt_one.trans_le hp
 refine ⟨⟨flame_notice Σψ V Yo 0 Yy Dψ pκ E' Yf _ 0 hB Τ,fun z p=>?_,uΦ⟩,fun z h=>?_⟩
 · obtain ⟨x,y⟩:= double_C X Σψ 2 u Tψ vx V Yo 0 Yy Dψ pκ E' Yf _ 0 hB Τ (fun i=>(uΦ i).1) hg T_.xb hp T_.niceA z p (fun k=> (by simpa using (bound_C σ pσ.1 R.L 1 Dq z (by simpa using p) k))) -- param order
   have hv:=mul_le_mul_of_nonneg_right hb hs.le
   refine ⟨Provides.liftE _ X _ _ x ?_,Provides.liftQ _ X _ _ y ?_⟩; apply le_trans (add_le_add_right T_.ebb _) -- check left
   · push_cast; linarith only [hv,hs]
   exact T_.cut.trans (by linarith only [hv,hs])
 have hx:0≤Va:= (σηo V Σψ E' Yf Yo 0 Yy Xp Dψ pκ _ _ hB (zero_lt_one.trans_le u)).2
 have hκ:=T_.emin; have hy:1≤L*s⁻¹:=one_le_mul_of_one_le_of_one_le hp (one_le_inv₀ hs|>.mpr T_.s1)
 refine elevated_C X Σψ 2 u Tψ vx V Yo 0 Yy Dψ pκ E' Yf _ 0 hB Τ (fun i=> (uΦ i).1) hg T_.xb hy T_.niceE z h (bound_C σ pσ.1 R.L (s⁻¹) Dq z h) s (2*A) T_.ebb ?_ ?_ ?_
 · refine le_trans ?_ T_.cut; unfold χCut; have ht:0 ≤ wish_E X.p.B Va:=by
      unfold wish_E; have hk:0 ≤ Roots.KZ:=inv_nonneg.mpr (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num))); positivity
   have hM:0 ≤ compassκ R.L:=hL.le; push_cast; linarith only [ht,mul_nonneg hM hx]
 · rw [show 2*s⁻¹*(A/8*s)=2*(A/8) by field_simp]; linarith
 calc
    L*s⁻¹*Va ≤ L*s⁻¹*(s/L):= mul_le_mul_of_nonneg_left hκ (by positivity)
    _ = 1:= by field_simp
    _ ≤ _:= by linarith only [hb]
omit tc -- careful includes hi
include store hS hBr street p hM h0 l
lemma fly_E : Flight (u:=u) V P_ X Y G S G₀ G₁ Xp q' E F σ Dq Xκ Yκ:=by
 constructor; intro l' Z x h
 let s0(k:Λh):ℂ:=0; obtain ⟨t,u,p0,p1⟩:= S_.life
 have he: Law_C (Cube.node ∘ Σψ) Τ l' (fun z=> α_ξ 0 z+s0 z) s0:= by rw [show (fun z:Λh=> α_ξ (0:Article I→ℂ) z+s0 z)=s0 from funext fun z=> by simp [α_ξ,s0]]; exact σtag_l ..
 have hp:= hurt_Q V Σψ E' Yf Yo 0 Yy Xp _ _ _ _ hB Τ S_.sun s0 s0 store hS hBr l' Z he (zeroR _) (seek_φ X Y G E F V' σ T_ street p hM h0 pσ l u p1).buy x h
 refine (Eq.trans (Eq.trans ?_ hp) ?_)
 · unfold dayShift; simp_rw [s0,add_zero]
 refine rer _ _ _ (fun i _=> MeasureTheory.integral_congr_ae (ae_of_all _ fun y=> congrArg _ (lace_C _ ?_ roots)))
 intro z h; unfold dayShift; simp only [Pi.zero_apply, s0, add_zero, dampE,if_pos h,street]

/- Single-step certificate (incl implicit footnote use on Y).
   `Panorama.scene` pays the proof on the actual Y. -/
structure Putting (u q s A h:ℝ):Prop where
 past:0<q
 gives: ∃ Z:TopicScheme (mid P B) (mid N B),∀ (I:Type) [Fintype I][LinearOrder I] (V':Fin 2→ Topic (mid P B))(σ:I→ Site (mid N B))(E:Key (Article I)→ RegBudget (mid P B))(F:Key (Article I)→ForceBudget (mid P B)), Very_Ψ σ X.p.B→ Bulletin R.L Y (Hove.heel G ∘ σ) E F h 1 (16*A) A q V'→∃ (E':Key (Article I)→ RegBudget (mid N B))(Yf:Key (Article I)→ForceBudget (mid N B)), Bulletin R.L X σ E' Yf h 2 (4*A) (A/8) s (hatchTopic R.L Z V' A q s) ∧ PanoramaBill X.p h (2*s⁻¹) s (2*A) E' Yf ∧ Flight (u:=u) V P_ X Y G S G₀ G₁ Xp q' E F σ (warpLine Z V' R.L A q s) E' Yf
omit l hB pσ
lemma wheel_fast : Putting V P_ X Y G S G₀ G₁ Xp q' u q s A h:=by
 obtain ⟨t,hω,hv,hV⟩:=S_.life; obtain ⟨Z,hZ⟩:= S_.proc
 refine ⟨T_.q_pos,Z,fun I _ _ V' σ E F pσ l=> ?_⟩; -- notation references variable not binder? expand
 let P': Article I→ Fin 2:= layer
 obtain ⟨E',Yf,hB,tc⟩:= @hZ (Article I) _ _ (treeO σ) _ _ (fun i=>V' (layer i)) _ _ (seek_φ X Y G E F V' σ T_ street p hM h0 pσ l hω hV)
 obtain ⟨x,r⟩:= stable_E V P_ X Y G S G₀ G₁ Xp q' E F V' σ T_ pσ (S_:=S_) (o:=Z) hB tc
 exact ⟨_,_,x,r,fly_E V P_ X Y G S G₀ G₁ Xp q' E F V' σ T_ street p hM h0 store hS hBr pσ l (o:=Z) (S_:=S_) hB⟩
#print axioms wheel_fast
end YM.CF.QuadClock
