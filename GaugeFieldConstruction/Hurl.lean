import GaugeFieldConstruction.Weepers
set_option autoImplicit false
set_option maxHeartbeats 45000
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
open scoped ComplexOrder
variable {N:Side}{K : Teller SU.group}{R:Patch}{L:ChartRatio SU.group}
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
open YM.Gleam
open BProof.PricePort Gleam.clocks

namespace Papal
open Girt
local instance localeHurlT (I:Type)[Fintype I][DecidableEq I]:MeasurableSpace (Op I):=borel _
local instance localeHurlB (I:Type)[Fintype I][DecidableEq I]:BorelSpace (Op I):=⟨rfl⟩
lemma outfit_meas (s i k:ℕ)(h:s≤Y.uv k)(Z:Orbit (count Y s i)→ Cipher (count Y s i))(e:Measurable Z): Measurable (fun V:Orbit (count Y s i)=> attire Y s i k V (Z V)):=by
 let N:=count Y s i; let A:=room Y s i; let G:=gram Y s i k; let M:=G.J.M
 let K':= {x:Pane N // Guard x P.d}; let L(V:Orbit N):K':=⟨A V,(roofage Y i s).paid _⟩; have he:Measurable L:= (roofage Y i s).bill.subtype_mk
 have hg: P.U.roundZ ≤ N.val:=P.J.gran.trans ((Y.voyage i).ownership s).size; let u(x:K'):=changeM P.U x.val M; have hv:Continuous u:=Kea.concur P.W.pearl P.V.note P.dpos (by rw [P.kJ]; decide) M hg
 -- avoid topology instance diamonds. uncurry as continuous in dressed boarded pair
 let D(x:K'):=spar P.K.j M x.val; have hp:Continuous D:= continuousOn_iff_continuous_restrict.mp (P.U.broadness _ hg M).continuousOn
 let T (x: K' × Cipher N):= Complex.exp (-pigment G.J.I x.1.val) • (tank (D x.1) x.2 * exp (dg (capT (D x.1) (G.J.P.den x.1.val))))
 have hT:Continuous T:=by
    have hp' (A:Type) [TopologicalSpace A] (f:A→ Cipher N) (g:A→K') (hf:Continuous f)(hg:Continuous g) : Continuous (fun x=> T (g x,f x)):=by
       apply Continuous.smul (Complex.continuous_exp.comp (((pigmentC ..).comp (continuous_subtype_val.comp hg)).neg))
       letI : NormedAlgebra ℚ (FC (Single N)) := NormedAlgebra.restrictScalars ℚ ℂ (FC (Single N))
       have ht:Continuous fun i=>exp (dg (Kennel.capT (D (g i)) (G.J.P.den (g i).val))):=NormedSpace.exp_continuous.comp ((Girt.dgCT _).comp (((continuous_const.sub (hp.comp hg)).mul ((Girt.den_ct ..).comp (continuous_subtype_val.comp hg))).mul (hp.comp hg)))
       exact Continuous.mul (f:=fun i=>tank (D (g i)) (f i)) ((Girt.tan_k _).comp ((hp.comp hg).prodMk hf)) ht -- tune comp param
    exact hp' _ Prod.snd Prod.fst continuous_snd continuous_fst
 let X(x:K'× Cipher N):= acts (T x) (u x.1); have hx:Continuous X:= (acts_cont.comp hT).clm_apply (hv.comp continuous_fst)
 have hi:Measurable (fun V:Orbit N=>X (L V,Z V)):= hx.measurable.comp (he.prodMk e)
 obtain ⟨-,hk,hv,-⟩:=prices_plot Y s i k h -- tuple not all tune
 let B:=P.V.L.mood (Y.uv k-s)
 have hX:Measurable (fun V: Pane N=> G.path.inChannels G.funds G.p G.beta V):=by
    change G.path=_ at hk; change G.funds=P.K.top.clip at hv; rw [hk,hv]; exact (PathData.channels_env B G.p G.beta).meas
 exact (Real.continuous_exp.measurable.comp (hX.neg.comp measurable_fst)).smul hi
lemma orb_cont (n:Side) : Continuous (fun g:Seat n→SU.E=>(tradew n g).val) :=by
 apply continuous_matrix; intro i j; unfold tradew; simp only [jump_apply]; split; exact (SU.matter_cont.comp (show Continuous (fun g:Seat n→SU.E=> g (node i.1.1)) from continuous_apply _)).matrix_elem _ _; exact continuous_const -- from FoyerSeat
lemma align_cont (s i k:ℕ)(T: Oak Y s i)(j:Signed)(w:ℝ): Continuous (fun V:Pane (count Y s i)=> offWall Y s i k (Loose j T.T V) w):=by
 let N:=count Y s i; have hp:Continuous (fun V:Pane N=> Loose j T.T V):= continuous_pi (fun i=>(Forest.folds _ _).comp (Wilson.continuous_pull ..))
 exact continuous_const.mul (f:=fun _=>_) (g:=fun V=> quant (tradew N (Loose j T.T V)).val) (quant_cont.comp ((orb_cont ..).comp hp))
local notation "Xq" s:max => Vale.hat P.R.L P.x s
abbrev levy (s i k:ℕ)(V:Orbit (count Y s i))(q p:ℝ):ℝ:= let G:=gram Y s i k; let x:= Xq s
    p*tauTicket P.K.top.clip G.beta x * (misdemean G.p.threshold V.1).card + q*boldTicket P.K.top.clip G.beta x * (misdemean (badgeDust x) V.1).card -- option.Rather than count greys charge backs
lemma levy_meas (s i k:ℕ)(q p:ℝ): Measurable (fun V:Orbit (count Y s i)=> levy Y s i k V q p):=by
 let G:=gram Y s i k; let x:=Xq s
 have hv(t b:ℝ) : Measurable (fun V:Orbit (count Y s i)=> b*(misdemean t V.1).card):=(show Envelope (fun U:Pane (count Y s i)=> b*(misdemean t U).card) from conduct ..).meas.comp measurable_fst
 exact (hv ..).add (hv ..) -- metas tune
abbrev flagged (s i k:ℕ)(T:Oak Y s i)(σ:Signed)(b:ℝ)(Z:Orbit (count Y s i)→ Cipher (count Y s i))(V:Orbit (count Y s i)):= Real.exp (levy Y s i k V (1/16) (1/10)) * ‖acts (offWall Y s i k (Loose σ T.T V.1) b) (attire Y s i k V (Z V))‖
lemma exhibition (p:Geometry P)(q:Spicing P)(t:Cash_T P.V P.d P.h) :
 ∀ᶠ s:ℕ in atTop,∀ i k:ℕ,s ≤ Y.uv k → (Y.voyage i).kick ≤ k → ∀ (ε:ℝ)(X:Orbit (count Y s i)→ Cipher (count Y s i)), Measurable X → (∀ᵐ V∂city (count Y s i), tier P.h (X V).val ≤ Real.exp ε) → ∀ (T:Oak Y s i)(j:Signed)(b:ℝ), |b|≤1→
 let F:= flagged Y s i k T j b X; let W:=gram Y s i k
 Integrable F (city (count Y s i))∧ ØCost Y s i k*(∫ x,F x ∂city (count Y s i))≤ Real.exp (ε+3*saveZ (Xq s)*sites (count Y s i))* ‖compensated P.U W (room Y s i)‖:=by
 obtain ⟨C,D,t1,t2,t3,t⟩:= exhib_T Y t (1/16) (by norm_num)
 filter_upwards [seasonal_m Y p q,t,houses_P Y,(stage_slope P.V P.x).eventually_gt_atTop 0,(stage_slope P.V P.x).eventually badge_ok] with s o u hv ha ht i k y v ε X hX e T j b H F W
 let x:=Xq s; let β:= W.beta; let q:=P.K.top.clip; let k':= 1/10* tauTicket q β x; let l:= boldTicket q β x; let N:=count Y s i; let U:= city N; let w:=ε+1/16*(saveZ x*sites N)
 have hb:0<β:=lt_of_lt_of_le (half_pos ha) (prices_plot Y s i k y).2.2.2.1.1
 have hk:0 ≤ boldTicket q β x:=by unfold boldTicket; have h:=q.tail_pos; have hd:= Work.E09.temp_pos ha; have he:0<badgeDust x:=hd.trans_le ht; positivity
 let Yq:=fun (_:Signed) (_:Pane N)=> (0:ℝ)
 obtain ⟨Zh,Qh,ζ⟩:= (hv i k y).support -- tune order P; need names B Za
 have hx: 0 ≤ tauTicket q β x:=by unfold tauTicket; have hx:= q.tail_pos; positivity
 obtain ⟨d,κ⟩:= ζ T k' (l/8) 0 0 0 Yq (fun _=> Envelope.const _) (show k' ≤ tauTicket q β x/8 from (by unfold k'; linarith only [hx])) le_rfl (div_nonneg hx (by norm_num)) (div_nonneg hk (by norm_num)) (fun i=> moderated_vacuum Zh Qh _ 0 0 _ (Yq i) le_rfl le_rfl (fun _=>le_rfl))
 rw [Real.exp_zero,mul_one] at κ
 let A(V:Orbit N):= segments W.path W.funds W.p β k' (l/8) (badgeDust x) Yq V.1
 have he:Measurable F:=by
    let Z:= outfit_meas Y s i k y X hX
    let B:=FC (Single N)
    have hp:Continuous (fun i:B × Wave (Single N) => acts i.1 i.2):=(acts_cont.comp continuous_fst).clm_apply continuous_snd
    have hx:= hp.measurable.comp (((align_cont Y s i k T j b).measurable.comp measurable_fst).prodMk Z)
    apply Measurable.mul (Real.continuous_exp.measurable.comp (levy_meas ..)) hx.norm
 have he':Integrable (fun V:Orbit N=>Real.exp w*A V) U:= d.const_mul _ -- tune simp Yq (uses no U)
 have hx: F ≤ᵐ[U] fun V=>Real.exp w*A V:=by
    filter_upwards [e] with Z e
    let R:= Real.exp (levy Y s i k Z (1/16) (1/10)); apply le_trans (mul_le_mul_of_nonneg_left ((u i k y).2.2 j T Z b H (X Z) ε e) (show 0 ≤ R from (Real.exp_pos _).le))
    change Real.exp (levy _ _ _ _ Z (1/16) (1/10))* (_ *_ ) ≤ Real.exp w *_; let E':= -W.path.inChannels W.funds W.p W.beta Z.1+ k'*(misdemean W.p.threshold Z.1).card + l/8* (misdemean (badgeDust x) Z.1).card + 0
    have hf:Real.exp E'≤ A Z:= season_average Yq (fun _=> le_rfl)
    apply le_trans _ (mul_le_mul_of_nonneg_left hf (Real.exp_pos _).le); unfold Graph.past; rw [←Real.exp_add,←Real.exp_add,←Real.exp_add]; apply Real.exp_monotone
    unfold E' w nativeCost levy k' l; rw [←sites_as_price]; unfold CF.Pannier.Damask.VelvetP.lad_z
    let a:= tauTicket q β x; let a':=(1/10)*a * (misdemean W.p.threshold Z.1).card; let l':=(misdemean (badgeDust x) Z.1).card; let N':= Fintype.card (Site (More N)); let c:=W.path.inChannels W.funds W.p β Z.1
    change a' + 1/16 * l * l' + (-c + (ε+1/16*(saveZ x * N' + l*l'))) ≤ ε+1/16*(saveZ x*N') + (-c+a'+l/8*l'+0)
    apply le_of_eq; ring
 have ht:Integrable F U:=he'.mono' he.aestronglyMeasurable (hx.mono fun i p=> (Real.norm_of_nonneg (show 0≤ F i from mul_nonneg (Real.exp_pos _).le (norm_nonneg _))).trans_le p)
 refine ⟨ht,?_⟩
 have hp' := integral_mono_ae ht he' hx; rw [integral_const_mul] at hp'; let X':=ØCost Y s i k; apply (mul_le_mul_of_nonneg_left (hp'.trans (mul_le_mul_of_nonneg_left κ (Real.exp_pos _).le)) (show 0≤ X' from norm_nonneg _)).trans
 rw [mul_left_comm,mul_comm X']; apply le_trans (mul_le_mul_of_nonneg_left (o i k v y) (Real.exp_pos _).le); rw [←mul_assoc, ←Real.exp_add];
 apply mul_le_mul_of_nonneg_right (Real.exp_monotone _) (norm_nonneg _); rw [sites_as_price]; unfold w; have hx:0≤ saveZ x*sites N:=mul_nonneg (BProof.coin_pos ..).le (zero_le_one.trans (sites_pos _)); change ε+1/16*(saveZ x*sites N)+2*saveZ x*sites N ≤ ε+3*saveZ x*sites N; linarith only [hx]
end Papal
end LocalLimit
end Rate
end YM.CF.Py
end
