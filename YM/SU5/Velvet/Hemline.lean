import YM.SU5.Gleam.Stow
import YM.SU5.Velvet.Heather
import YM.SU5.Velvet.Viper
import YM.SU5.Velvet.Fronds
set_option autoImplicit false
set_option maxHeartbeats 320000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
variable {h z:ℝ}
open Buffered
open CF.Pannier.Damask
open YM.CF.Velvet
open Pannier
namespace Papal
local notation "ℶ" => hat P.R.L P.x
local notation "💠" => P.K.j
abbrev gistV(s i k:ℕ) := angleFin (gram Y s i k).J.M (count Y s i) P.K.j
abbrev venue (s i k:ℕ)(x:Orbit (count Y s i)) := room Y s i x
def reservable (s i k:ℕ) (h z c κ:ℝ)(F:Mark (count Y s i)): Prop:=let Q:= (gram Y s i k); let w:=room Y s i; let T:=count Y s i
                                                                        ∀ x:Orbit T,Yep h (acts (star (F (x.1,w x))) (mateK _)) (changeM P.U (w x) Q.J.M) (Real.exp (trade (spar P.K.j Q.J.M (w x)) (tickA _) z +κ*flakes Q.p.threshold x.1+c))
-- first part directly put through trade
local notation "💖" s:max i:max => sites (count Y s i)
local notation "💉" s:max i:max k:max => gram Y s i k
lemma speck (s i k:ℕ)(e:s≤Y.uv k) : (gram Y s i k).p.threshold=temp (hat P.R.L P.x s):=((congrArg BudgetPoint.threshold (prices_plot Y s i k e).1).trans (Y.meter.boot s).1)
/-- can prepay θ sizes after specifying e. DESCRIPTOR. -/
def SizeCloud(j:ℕ)(u z:ℝ):Prop:= ∀ (N:Side)(M:Tulip.Male)(ℓ:Kea.Pad j N), trade (spar j M (1:Pane N)) (tickA N) z ≤ angleFin M N j + u*sites N
-- this is independent of P history beyond 💠, geometry. any z even negative small. not applied on other preparations without hypotheses
lemma crystal_air(j:ℕ)(p:1≤j)(s:ℝ)(h:0<s):∃ z>(0:ℝ), z≤1 ∧ ∀ u,0<u→u≤z→SizeCloud j s u:=by
 obtain ⟨C,q,W⟩:=flat_earn p; have hp: ∀ᶠ x:ℝ in 𝓝[>] 0, C*x^4 ≤ s:=eventually_nhdsWithin_of_eventually_nhds (show ∀ᶠ x:ℝ in 𝓝 0,C*x^4 ≤ s from ((continuousAt_const.mul (continuous_id.continuousAt.pow 4)).tendsto.eventually (ge_mem_nhds (show C*0^4<s by simpa)))) -- tune
 obtain ⟨z,y,t⟩:= (hp.and self_mem_nhdsWithin).exists; change 0<z at t; refine ⟨min z 1,lt_min t one_pos,min_le_right ..,fun a p' v N M H=>?_⟩ -- exact? refine
 apply le_trans (W N H M a); apply add_le_add_right; refine mul_le_mul (le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ p'.le (v.trans (min_le_left ..)) 4) q.le) y) (pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ _) (by positivity) h.le; exact Nat.cast_le.mpr (Nat.le_mul_of_pos_right _ two_pos)
lemma earns_renewal {a:ℕ} (Q:Procurement P.K.j a P.d) (c:0<z)(o:z≤1)(s:ℝ)(p:0<s)(hL:SizeCloud P.K.j s z): ∃ κ:ℝ,0≤κ ∧∀ᶠ j in atTop,∀ᶠ i in atTop,∀ k:ℕ,j ≤ Y.uv k→ let A:= gram Y j i k; ∀ x:Orbit (count Y j i), trade (spar P.K.j A.J.M (room Y j i x)) (tickA _) z ≤ gistV Y j i k+2*s*sites (count Y j i)+κ*flakes A.p.threshold x.1:=by
 obtain ⟨B,v,u,pv,t,L⟩:= YM.CF.Velvet.Hours.time_flowers Q c o s p; obtain ⟨n,U⟩:=Kea.gave P.K.j (by rw [P.kJ]; omega); let T:= ( ((P.J.n+4)*2+1)^4 :ℕ); refine ⟨u*(4*T),by positivity,?_⟩
 have ht:Tendsto temp atTop (𝓝 0):=by simpa using Work.E09.radiusB_temp 0
 have hT:0<P.J.k:=P.J.ht
 filter_upwards [(ht.comp (turnover P)).eventually (ge_mem_nhds pv), (ht.comp (turnover P)).eventually (ge_mem_nhds hT)] with j x y
 filter_upwards [(count_grows Y j).eventually_ge_atTop (n+B)] with i hh k hk A X
 -- ↑ intro A actual
 let N:= count Y j i; let D:= room Y j i; let C:= flags A.p.threshold X.1; have he:=speck Y j i k hk; change A.p.threshold=temp _ at he; have hp:A.p.threshold ≤ v:=he.trans_le x
 have hs:A.p.threshold ≤ P.J.k:=he.trans_le y
 have hw:=roofage Y i j; let μ:=D X; apply le_trans (L A.p.threshold A.p.threshold_pos.le hp N (by change B ≤ (count Y j i).val; omega) μ A.J.M (hw.paid X));
 let G:= A.J.M; let V:=💖 j i; let K:= flakes A.p.threshold X.1; let P':= flags A.p.threshold μ
 have hx: (P'.card:ℝ) ≤ 4*K*T:= by
    have he:= (card_le_card (seep hw hs X)); let G:=P.J.n; let e:=flakes A.p.threshold X.1; have hz:(Lattice.halo (G+4) C).card≤ C.card*T:= (Corona.halo_size C (G+4)).trans_eq (by unfold T G; ring) -- tune
    have ht' := he.trans hz; have hv:= flag_coat X.1 A.p.threshold; have hu:= ht'.trans (Nat.mul_le_mul_right T hv)
    refine (Nat.cast_le.mpr hu).trans (Eq.le ?_); unfold K flakes; push_cast; ring
 have ht: trade (spar 💠 G (1:Pane N)) (tickA N) z≤ angleFin G N 💠 + s*V:= hL N G (U N (Vale.val_e ..) (by change n ≤ (count Y j i).val; omega))
 change trade _ _ _ + s*V+ _ ≤ angleFin G N 💠 + 2*s*V+ u*(4*T)*K
 have hy:= mul_le_mul_of_nonneg_left hx t; linarith only [hy,ht]
private def peg (s i k:ℕ)(F:Mark (count Y s i))(x:Orbit (count Y s i)):ℂ:= let L:=room Y s i; letterRead (F (x.1,L x)) (Graph.recX P.U (gram Y s i k) L x)
/-- ratio by compensated. -/
def BrokenMark(s i k:ℕ)(F:Mark (count Y s i)) : ℝ := (∫ x:Orbit (count Y s i), ‖peg Y s i k F x‖ ∂city _)/ ‖vac0 P.U (gram Y s i k) (room Y s i)‖
lemma markUpper {a:ℕ}(s:ℝ)(Q:Procurement P.K.j a P.d) (c:0<z)(o:z≤1)(p:0<s)(hL:SizeCloud P.K.j s z) (hp:0≤h)(p':h ≤ P.h)(t:Geometry P)(v:ℝ):∀ᶠ j:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ,(Y.voyage i).kick ≤ k → j ≤ Y.uv k → ∀ (F:Mark (count Y j i)) (C:ℝ),Envelope F → reservable Y j i k h z C v F → BrokenMark Y j i k F ≤ Real.exp ((8*s)*(sites (count Y j i)) + C) :=by
 -- combination: +4 mile +2 tilt +1 gauge +1 benchmark
 obtain ⟨κ,Hk,L⟩:= earns_renewal Y Q c o s p hL
 let X:= P.W.C; obtain ⟨μ,Hμ,R⟩:= VelvetC.wisps_goal (t:=P.d) (r:=P.J.n) hp (cash_v X) P.J.ht (level_p X) p
 filter_upwards [benchmarks Y s p t,L, (turnover P).eventually R,gauge_whole Y s p (κ+v+μ), (turnover P).eventually (((dev_R P.R).1.low (k:=1) (by omega)).spine.eventually (ge_mem_nhds p))] with j q HC ⟨n,hBudget⟩ hX W
 filter_upwards [HC,(count_grows Y j).eventually_ge_atTop n] with i H n0 k pC pA F C pZ Hz
 let B:=gram Y j i k; let N:=count Y j i; let f:= peg Y j i k F; let g:=room Y j i; let A:= Graph.recX P.U B g; let V:= sites N; let D:=sod Y k j i; let T:= P.K
 let Hv:=Y.each_level i k j pC pA; have Hf: Integrable f (city N):=mark_integrable (roofage Y i j).bill pZ ((Marks.can_read _ _ _ _ Hv).smul (Complex.exp (-B.v)))
 let b:=angleFin B.J.M N T.j
 let Hκ:=b+6*s*V+C; have hc(x:Orbit N): ‖f x‖≤ Real.exp (-(B.path.inChannels B.funds B.p B.beta x.1) + (κ+v+μ)*flakes B.p.threshold x.1+Hκ):= by
    have heX:= speck Y j i k pA; let Z:= (v*flakes B.p.threshold x.1+C); let D':=trade (spar T.j B.J.M (g x)) (tickA N) z; let E:=Real.exp (D'+Z); let k':=flakes B.p.threshold x.1; let R':= (4*s)*V+μ*k'
    obtain ⟨hx,vB,gV,hH,h'⟩:=prices_plot Y j i k pA
    have hm:=hBudget (roofage Y i j) P.h _ _ P.K.j h' p' n0 W W x (safety Y j i k x).1; rw [←heX] at hm; let f':=F (x.1,g x); let Y':= Graph.beam B P.U g x; let b':= mateK N; have hy': Yep h (acts (star f') b') (changeM P.U (g x) B.J.M) E:=by
       specialize Hz x; unfold E Z; rw [←add_assoc]; exact Hz
    have ht := Yep.val (show Yep h _ Y' (Real.exp R'*E) from hm.2 (acts (star f') b') (changeM P.U (g x) B.J.M) E (Real.exp_pos _).le hy')
    have hy : D' ≤ b+2*s*V+κ*k':= H k pA x; let a:= Graph.past B x.1; change ‖letterRead f' (Graph.recX P.U B g x)‖ ≤_; rw [Graph.porch, (letterRead _).map_smul_of_tower,norm_smul,Real.norm_of_nonneg (r:=a) (Real.exp_pos _|>.le)]; change a*‖inner ℂ b' (acts f' Y')‖ ≤ Real.exp _; rw [←act_inner]
    apply (mul_le_mul_of_nonneg_left ht (Real.exp_pos _|>.le)).trans; unfold E; rw [←Real.exp_add,← Real.exp_add]; apply Real.exp_monotone; change -(_ :ℝ) + _ ≤ -(_ : ℝ) + (κ+v+μ)*k'+Hκ; unfold Z R' Hκ; change _+(_+(D'+(v*k'+C))) ≤ _; linarith only [hy]
 change (∫ i, ‖f i‖ ∂_)/_ ≤_;
 let μ':= Real.exp (D-s*V); let Z:= ‖vac0 P.U B g‖; let m:= Real.exp ((8*s)*V+C)
 have he: μ'≤Z:=q i k pC pA; have ha: Z>0:= (Real.exp_pos _).trans_le he; refine (div_le_iff₀ ha).2 ?_; refine (hX i k pA f Hκ Hf hc).trans ((mul_le_mul_of_nonneg_left he (Real.exp_pos ((8*s)*V+C)|>.le)).trans' ?_)
 apply le_of_eq; rw [←Real.exp_add]; let Hψ:= Fineness.gaugedBase P.L B.beta (More N) (P.V.L.H (Y.uv k-j)); change Real.exp (Hψ+s*V+ Hκ)=Real.exp _; rw [show D=Hψ+b from rfl]; unfold Hκ; congr 1; ring
lemma broken_ratio (i j k:ℕ) (F:Mark (count Y j i)): ‖Buffered.Afterglow.Journey.compass Y i k j F‖ ≤ BrokenMark Y j i k F:=by
 rw [Buffered.Afterglow.Journey.compass,← same_ratio,norm_div]; exact div_le_div_of_nonneg_right (norm_integral_le_integral_norm ..) (norm_nonneg _)
lemma basic_op {a:ℕ}(s:ℝ)(Q:Procurement P.K.j a P.d) (c:0<z)(o:z≤1)(p:0<s)(hL:SizeCloud P.K.j (s/8) z) (p':flowCost z ≤ P.h)(t:Geometry P)(w:ℝ):∀ᶠ j:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ,(Y.voyage i).kick ≤ k → j ≤ Y.uv k → ∀ (F:Mark (count Y j i)) (C:ℝ),Envelope F →
 (∀ x:Orbit (count Y j i), ‖modifyB (tickA _) z (F (x.1,room Y j i x))‖ ≤ Real.exp (w*flakes (gram Y j i k).p.threshold x.1 + C)) → BrokenMark Y j i k F ≤ Real.exp (s*(sites (count Y j i)) + C) := by
 have he:=markUpper Y (s/8) Q c o (by positivity) hL (flow_pos c|>.le) p' t w; rw [show 8*(s/8)=s from (by ring)] at he
 filter_upwards [he] with j ht; filter_upwards [ht] with i q k s H F C hp u; refine q k s H F C hp fun x=>?_ -- reservable
 let N:= count Y j i; let G:=gram Y j i k; let T:=tickA N; let V:= room Y j i x; let R:= F (x.1,V);
 obtain ⟨a,E⟩:= safety Y j i k x; let d:= trade (spar P.K.j G.J.M V) T z; let r:= w*flakes G.p.threshold x.1
 have hg:T=cutM (Tset N):=touchP N; let f:=issue a c o (S:=Tset N) (show Sea (cutM _) (mateK N) from hg ▸ tickB N) E R
 apply f.weigh _ (flow_pos c|>.le); rw [←hg]; apply le_trans (mul_le_mul_of_nonneg_right (u x) (Real.exp_pos _|>.le)); change Real.exp (r + C)*Real.exp d ≤ Real.exp _; rw [←Real.exp_add]; exact le_of_eq (congrArg Real.exp (show r+C+d=d+r+C from (by ring)))
-- total variation measure (divided by abs, scalar charge only). ∀ ONE requested e. also equality check ratio
/-- The actual meaning of unmarked price estimate. This is **∫ |ρ(x)|** for actual normalized action on orbit. -/
lemma normal_price (s i k:ℕ)(F:Mark (count Y s i)): BrokenMark Y s i k F= ∫ x: Orbit (count Y s i), ‖(letterRead (F (x.1,Papal.room Y s i x)) (denZ (gram Y s i k) P.U (room Y s i) x)) / partitionZ (gram Y s i k) P.U (room Y s i)‖∂city _:=by
 let H:= gram Y s i k; let Fm:= room Y s i; let f:= fun x:Orbit (count Y s i)=> letterRead (F (x.1,Fm x)) (denZ H P.U Fm x); let G:= Complex.exp (-H.v); let Z:=partitionZ H P.U Fm; have h(x): ‖peg Y s i k F x‖=‖G‖ * ‖f x‖:=by unfold peg Graph.recX; simp only [map_smul,norm_smul]; rfl
 change _ = ∫ x, ‖f x/Z‖∂ _; unfold BrokenMark; simp_rw [h,norm_div,div_eq_mul_inv]; rw [integral_const_mul, integral_mul_const]; change _* _ * (‖G*Z‖)⁻¹=_; rw [norm_mul,mul_inv]; have hp:0 <‖G‖:=norm_pos_iff.mpr (Complex.exp_ne_zero _); rw [mul_mul_mul_comm, mul_inv_cancel₀ hp.ne',one_mul]
lemma audit_weather (j:ℕ)(p:1≤j) : ∃ θ>(0:ℝ),∀ t':ℝ,0≤t'→t'≤θ→∃ n,Procurement j n t':=by
 obtain ⟨t,u,N,h⟩:=CF.Pannier.Chancel.winter j p; obtain ⟨g,v,k,f⟩:=Brace.drift_l j p; refine ⟨min t g,lt_min u v,fun x p q=> ⟨N+k,p,?_,?_⟩⟩
 · intro n M hx; exact (f n (by omega) M).red (q.trans (min_le_right ..))
 intro y t0; obtain ⟨u',hc,i,l⟩:=h y t0; refine ⟨u',hc,i,fun X v=> ?_⟩; have he:=l X (by omega); let Z:= q.trans (min_le_left ..); exact ⟨fun b M X p T=> he.1 b M X (p.shrink Z) T,fun b M L U V p v X T=> he.2 b M L U V (p.shrink Z) (v.shrink Z) X T⟩
end Papal
end LocalLimit
end Rate
end YM.CF.Py
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.markUpper
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.basic_op
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.audit_weather
