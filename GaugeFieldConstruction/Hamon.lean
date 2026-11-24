import GaugeFieldConstruction.Razel
import GaugeFieldConstruction.Season
import GaugeFieldConstruction.Kayf
set_option autoImplicit false
set_option maxHeartbeats 1050000
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
open Pannier
namespace Papal
open XGarden XGarden.Ledger XGarden.Echo XGarden.MastTin XGarden.Shield
open CF.Buffered CF.Buffered.Advance CF.Buffered.Afterglow
local instance (I:Type)[Fintype I][DecidableEq I]:MeasurableSpace (Op I):=borel _
local instance (I:Type)[Fintype I][DecidableEq I]:BorelSpace (Op I):=⟨rfl⟩
-- Couple at the actual Gram; spectator.need linksOnly outside.C
local notation "Πk" Y:max i:max k:max=> gram Y (Course.uv Y k) i k -- tune names
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))(i k:ℕ)
abbrev hardPoint (p:BudgetPoint) : trans1 (count Y (Y.uv k) i):=hard P.K.top.clip p (gram Y (Y.uv k) i k).beta P.U
abbrev Priority(p: BudgetPoint):Prop:=p.threshold=(Y.meter.a (Y.uv k)).threshold
lemma dawnK (p:BudgetPoint)(q:Priority Y k p)(v:Orbit (count Y (Y.uv k) i)): Scree.denZ (gram Y (Y.uv k) i k) P.U (room Y (Y.uv k) i) v=hardPoint Y i k p v.1 :=by
 let m:= Y.uv k; let G:=gram Y m i k; let o:= Y.meter.a m
 rw [show denZ _ _ _ _=_ from Y.whole i k v]; let K:=P.K.top.clip; let x:= count Y m i; let U:=v.1
 unfold Vale.capP hardPoint hard; unfold Echo.tight -- ambiguous
 have hx:p.threshold= o.threshold:=q; rw [hx]; change Set.indicator {U:Pane x | flags o.threshold U=∅} (fun U=> Complex.exp (-((G.beta*basicP K U:ℝ):ℂ)) • changeM P.U U Vale.babyM) U= _
 rw [show (fun U:Pane x=> Complex.exp (-((G.beta*basicP K U:ℝ):ℂ)) • changeM P.U U babyM)=coatHead (m:=Vale.mesh (Y.ir i) P.R.L (Y.uv k)) P.K.top.clip (gram Y (Y.uv k) i k).beta P.U from ?_]; funext i; rw [CF.Buffered.Region.plain_s,← Complex.ofReal_neg, ← Complex.ofReal_exp,Complex.coe_smul]; rfl
lemma envelope_top (p:BudgetPoint)(q: Priority Y k p): Envelope (hardPoint Y i k p) :=by
 let s:=Y.uv k; refine cap_env P.K.top.clip p _ P.U P.dpos (P.J.gran.trans ((Y.voyage i).ownership s).size) (show 1≤ P.K.j by rw [P.kJ]; decide) P.W.pearl P.V.note (fun x v=> top_strict ((Y.voyage i).ownership s).paid P.J.hr v ?_); rw [show p.threshold=_ from q]; exact (Y.history i k).pole s
abbrev Huz {n:Side}(V:Mark n) : marker0 n:= fun A=> V (A,A)
def bridge {n:Side}(M: marker0 n): Mark n:=M ∘ Prod.fst
lemma article_P (p:BudgetPoint)(q:Priority Y k p)(U:Mark (count Y (Y.uv k) i))(M:marker0 (count Y (Y.uv k) i))(u:Envelope U)(a:Envelope M): Journey.compass Y i k (Y.uv k) (U*bridge M)= UnEcho M (Huz U) (hardPoint Y i k p) / partitionZ (gram Y (Y.uv k) i k) P.U (room Y (Y.uv k) i):=by
 let s:=Y.uv k; let S:=count Y s i; let f:=hardPoint Y i k p; let A:=room Y s i; let E:=U*bridge M; unfold Journey.compass; refine congrArg (· / _ ) ?_; unfold markedRead; change (∫ v:Orbit S,letterRead (U (v.1,A v)*M v.1) (denZ (gram Y s i k) P.U A v)∂city S)=_; simp_rw [show ∀ v:Orbit S, denZ (gram Y s i k) P.U A v=_ from dawnK Y i k p q]; -- tune meta
 let g(x:Pane S):=letterRead (U (x,x) * M x) (f x); change (∫ v:Orbit S,letterRead (U (v.1,A v)*M v.1) (f v.1) ∂city S)=(∫ x:Pane S,g x∂prior _ _); have he(v:Orbit S): letterRead (U (v.1,A v)*M v.1) (f v.1)=g v.1:=by
    by_cases hp:v.1∈XGarden.Echo.tight p S
    · have hx:A v=v.1:= roof_elem ((Y.voyage i).ownership s).paid v.2 v.1 hp ((show p.threshold=(Y.meter.a s).threshold from q).symm ▸ (Y.history i k).pole s); rw [hx]
    · unfold g; rw [show f v.1=0 from Set.indicator_of_notMem hp _,map_zero,map_zero]
 simp_rw [he]
 rw [MeasureTheory.integral_prod];
 · simp
 let X:Envelope (Huz U):=Env.along (g:=fun x=> (x,x)) u (measurable_id.prodMk measurable_id); have hp:Envelope g:=env_letterRead (env_mult X a) (envelope_top Y i k p q); exact Env.integrableX (Env.along (g:=Prod.fst) hp measurable_fst) _
omit i k
lemma summit_money:∀ᶠ s:ℕ in atTop,∀ i k:ℕ,s≤Y.uv k→let p:=(gram Y s i k); 0 < p.beta ∧ 1 ≤ p.beta*(Y.meter.a s).threshold^2:=by
 let Z:=hat P.R.L P.x; have h : Tendsto (fun x=> Real.log (Real.log (Z x))) atTop atTop:=Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp (turnover P)); filter_upwards [(turnover P).eventually_gt_atTop 0,h.eventually_ge_atTop 2] with s p u i k e
 let V:= gram Y s i k; have hp: Z s/2≤ V.beta:= (prices_plot Y s i k e).2.2.2.1.1; refine ⟨lt_of_lt_of_le (half_pos p) hp,?_⟩
 change _≤ V.beta*_ ; rw [(Y.meter.boot s).1]; change 1 ≤ V.beta*(temp (Z s))^2; apply le_trans _ (mul_le_mul_of_nonneg_right hp (sq_nonneg _)); unfold Pressure.temp
 let L:= Real.log (Real.log (Z s)); let S:=Real.exp (L^2); have hx:1+ (L^2)≤ S:=by linarith only [Real.add_one_le_exp (L^2)]
 have hu:2≤L:=u; have he: 2 ≤ S:=by nlinarith only [hx,hu]
 let d:= Real.sqrt (Z s); have hz:d^2=Z s:=Real.sq_sqrt (by exact p.le); have hv:0<d:=Real.sqrt_pos.mpr p; change 1 ≤ Z s/2*(d⁻¹*S)^2; rw [←hz]; field_simp; nlinarith
lemma inns_GE(H:ℝ): ∃ a D:ℝ,0<a ∧ 0≤D ∧∀ᶠ s in atTop,∀ i k:ℕ,s=Y.uv k → -- types use (Y.uv k) directly
 let m:=Y.uv k; let G:= gram Y m i k; let B:= count Y m i
 ∀ (p:BudgetPoint), Priority Y k p → p.order≤6→p.power≤3→∀ (o:Seat B)(e:Axis)(f:PlaqAxes),∃ X:Torches B,
    Inscribe p o H a X ((CaseL:ℝ)*reserveC P.K.top.clip) (D/(G.beta*p.threshold)) ∧ LegTax X ∧ X.1=isolate none (Gval o f p P.K.top.clip G.beta e) ∧∀ U: Mark B,Envelope U → untax (m:=Vale.mesh (Y.ir i) P.R.L (Y.uv k)) o e (Huz U) → Journey.compass Y i k (Y.uv k) (U*bridge (Ion X))=0:=by
 obtain ⟨D,E,a,h,hD,e,p,V⟩:= GEconomy P.U P.dpos P.W.pearl P.V.note P.K.top.clip (show 1≤ P.K.j by rw [P.kJ]; decide) P.J.n -- order
 refine ⟨a,D+H^2*E,p,by positivity,?_⟩
 filter_upwards [summit_money Y, Preparation.pane_fills Y 0 0 2] with s hb u i k q m G B p s' p₁ p₂ o e f -- q rename
 have hp:Roof _ P.J.k P.J.roomX P.J.n (room Y m i):=((Y.voyage i).ownership m).paid
 have hm:1<(More B).val:=by have ht:=(show _ from u i); rw [q] at ht; simpa [B,m] using (show 1< (More (P.Ctor _ (Y.uv k))).val from lt_trans (by norm_num:(1:ℕ)<2) (by simpa using ht)) -- tune
 have hn:P.U.roundZ≤B.val:=P.J.gran.trans ((Y.voyage i).ownership m).size; subst s; have he:=hb i k le_rfl; have hx:p.threshold=(Y.meter.a m).threshold:=s'; obtain ⟨C,U,T,t,Q⟩:=V (room Y m i) hp hn hm o e f p G.beta H (hx.symm ▸ (Y.history i k).pole m) P.J.hr he.1 p₁ p₂ (hx.symm ▸ he.2)
 refine ⟨C,U,t,T,fun X x pU=>?_⟩; rw [article_P Y i k p s' X (Ion C) x (Ion_env U), show UnEcho _ _ _=0 from Q _ pU,zero_div]
#print axioms inns_GE
end Papal
end LocalLimit
end Rate
end YM.CF.Py
end
