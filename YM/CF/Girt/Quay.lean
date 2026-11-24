import YM.CF.Girt.Mist
import YM.CF.Girt.East
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.CF.Girt
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Cube SU Fock Skye Scree Spire Dial Laic Pec Hest Hive
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Rush Tulip Vault Paige Drapes Peaks Brace Branch Lat Kennel CF.Jet Pressure
local notation "G₀"=> SU.group
open Scroll
variable {f n :Side}{a d w e:ℝ}
open Work.F05
variable {B C L:Side}{j:ℕ}{ho:Odd L.val}{Y:Pricing j L ho (Thread j)}{P':Grasp Y B e}
section
variable{ι X Y:Type*}[MeasurableSpace X][TopologicalSpace X][OpensMeasurableSpace X][MeasurableSpace ι][CompactSpace X][SecondCountableTopology X][NormedAddCommGroup Y][MeasurableSpace Y][BorelSpace Y]
lemma refill (f:X→Y)(p:Continuous f)(g:ι→X)(v:Measurable g): RG.Envelope (f ∘ g):=by
 obtain ⟨C,T⟩:= isCompact_univ.bddAbove_image p.norm.continuousOn; exact ⟨p.measurable.comp v,C,fun i=>T ⟨_,Set.mem_univ _,rfl⟩ ⟩
end
open Pastry
local instance (I:Type)[Fintype I][DecidableEq I]:MeasurableSpace (Op I):=borel _
local instance (I:Type)[Fintype I][DecidableEq I]:BorelSpace (Op I):=⟨rfl⟩
lemma sailW(R:GramM (mid C B))(X:Ward R)(A:Pearl P')(U:Stamped j L ho Y)(p:0<e)(h:1 ≤ j)(s:ℕ)(T:Scree.Loom (mid C B))(hp:Roof _ d e s T)(t:P'.roundZ≤(mid C B).val): RG.Envelope (denZ R P' T):=by
 letI: CompactSpace (CapX C B e):= isCompact_iff_compactSpace.mp (show IsCompact {x:Pane (mid C B)|Guard x e} from (CF.Phase.cover_closed ..).isCompact)
 let K(V:Orbit (mid C B)):CapX C B e:=⟨T V,hp.paid _⟩; let J:=R.J; have ht:Measurable K:= hp.bill.subtype_mk
 let Y₀:= (fun i:CapX C B e=>relV P' J i.val); have hx:RG.Envelope fun i=>Y₀ (K i):= refill Y₀ (house_k A U p h J t) K ht
 obtain ⟨a,b,c,hh⟩:= X.area; have he : RG.Envelope (R.H0):= pole_w _ (T:=fun v:ℝ=>R.v- ↑v) (by fun_prop) (PathData.channels_env (n:=More (mid C B)) hh R.p R.beta)
 have hb:RG.Envelope fun x=> Pec.pigment R.J.I (T x):=refill (Pec.pigment R.J.I) (pigmentC R.J.I) T hp.bill; have hf:RG.Envelope fun x=> R.betaL T x:= kitE _ _ (·-·) (by fun_prop) (snap (ι:=Pane (mid C B)) (Z:=Orbit (mid C B)) he measurable_fst) hb
 have hy:=P'.broadness _ t J.M; let Y':= fun i: CapX C B e=> spar j J.M i.val -- tune
 have hh:Continuous Y':= continuousOn_iff_continuous_restrict.mp hy.continuousOn
 let f(i):= tank (Y' (K i)) (R.board i); let N:=Single (mid C B); have H:RG.Envelope f:= kitE (Y' ∘ K) R.board (@tank N _ _) (tan_k N) (refill Y' hh K ht) (billE R X); let B₀(i):= acts (f i) (Y₀ (K i)); have hb:RG.Envelope B₀:=kitE f (Y₀ ∘ K) (fun Tt : FC N=> (fun i=>acts Tt i)) (Continuous.clm_apply (acts_cont.comp continuous_fst) continuous_snd) H hx; exact kitE _ _ (fun (t:ℂ) (v:Phys (mid C B))=> t • v) (by exact continuous_fst.smul continuous_snd) (pole_w _ Complex.exp Complex.continuous_exp hf) hb
open Broc
variable {M B':Side}{V:Ratio (CSide M B) (mid C B)}{pM:Male}(l:V.count=L)(u:Stamped j L ho Y)(t:ℕ)(p:Tax L (ticketT (Thread j) true) false true a w t d)(h:t≤(CSide M B).val)(hp:e≤d)(v:0<e)(z:P'.roundZ≤(CSide M B).val)
include p z hp h l v
omit hp h l v p z in
lemma heat_p {N D:Side} (G:Ratio N D)(T:Coil N D→Op (Iota G))(d a w:ℝ)(H:Crown (badge _) (Peaks.parcel G false d) (Peaks.parcel G true d) a w (fun x=> T x.val)) : Continuous (fun x:↥(legal G d)=>T x.val):=by
 obtain ⟨F,C,U,V,hx⟩:= H; have he(x:↥(legal G d)):T x.val=∑ i,F i x:= hx x; simp_rw [he]; exact continuous_finsetSum _ fun i _=>(U i).toTicket.cont
lemma heat_t : Continuous fun x:↥(Rent0 V e)=>ticketT (Thread j) true pM V (unionP x.val):=by
 let f(i:↥(Rent0 V e)):↥(legal V d):= ⟨unionP i.val,ambient _ _ v hp i.property⟩; have hf:Continuous f:= (((profile_c.comp (continuous_fst.comp continuous_subtype_val)).prodMk (profile_c.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk _)
 let F:=ticketT (Thread j) true pM V; have hF:Continuous fun x:↥(legal V d)=> F x.val:=heat_p V F d a w (p pM V l h)
 have he: Continuous ((fun x:↥(legal V d)=>F x.val) ∘ f):= hF.comp hf; exact he
omit p hp h
lemma heat_n (x:↥(Rent0 V e)): chargeA (Thread j) V pM (unionP x.val)≠0:=by
 obtain ⟨i,g⟩:= Phase.cue_from x.val.2; let Z:=starfish M B x.val.2 i; let W:=accordL V x.val Z; have ht:=pose_g P' v V l z x.val (show JointB V x.val e from x.property) Z (starK P'.capY v.le (show JointB V x.val e from x.property).cg g); have H:= (Y.cap V l (P'.needed.trans z) pM W ht.glyph).pay; change chargeA (Thread j) V pM (unionP x.val)=Complex.exp _ at H; rw [H]; exact Complex.exp_ne_zero _
include p hp h
lemma heat_c : Continuous (fun x:↥(Rent0 V e)=> ( (sect0 V * chargeA (Thread j) V pM (unionP x.val))⁻¹:ℂ)) ∧ Continuous fun x:↥(Rent0 V e)=> ticketT (Thread j) true pM V (unionP x.val) :=by
 let o:=oceanA V; let ψ:=fun i:↥(Rent0 V e)=> ticketT (Thread j) true pM V (unionP i.val); have hc:Continuous ψ:=heat_t l t p h hp v z; have hi:Continuous fun x:↥(Rent0 V e)=> effectK (ψ x) o:= (acts_cont.comp (quant_cont.comp hc)).clm_apply continuous_const
 have he:Continuous fun x:↥(Rent0 V e)=> chargeA (Thread j) V pM (unionP x.val):= Continuous.inner (f:=fun _=>o) continuous_const hi
 refine ⟨?_,hc⟩; exact (Continuous.mul (f:=fun _=>sect0 V) continuous_const he).inv₀ (fun x=>mul_ne_zero (norm_pos_iff.mp ((sectorU V).symm ▸ zero_lt_one)) (heat_n (pM:=pM) l v z x))
variable {α:Type*}[MeasurableSpace α]
lemma heat_k (T: α→ Nom (mid M B) (mid C B))(W:α→Phys (mid C B))(H:∀ i,JointB V (T i) e)(ht:Measurable T)(hW:RG.Envelope W): RG.Envelope fun i=> fire (Thread j) V pM (unionP (T i)) (cartsL (switchG V).symm (W i)):=by
 let U(i:α):↥(Rent0 V e):=⟨T i,H i⟩; letI:CompactSpace ↑(Rent0 V e):= open_tr ..; have hh:Measurable U:= ht.subtype_mk
 obtain ⟨hc,hY⟩:= heat_c (pM:=pM) l t p h hp v z; let M':= mid M B; let N:=Single M'; let f(i:α):=ticketT (Thread j) true pM V (unionP (T i)); have hs:RG.Envelope f:=refill (fun i:↥(Rent0 V e)=>ticketT (Thread j) true pM V (unionP i.val)) hY U hh
 let Z:=fun (A: Op (Iota V)) (w:Phys (mid C B))=>pailL (patchQ V) (reefS V true) (effectK A (cartsL (switchG V).symm w)); have hz:Continuous (uncurry Z):= (pailL _ _).continuous.comp (f:=fun x:Op (Iota V) × Phys (mid C B) => effectK x.1 (cartsL (switchG V).symm x.2)) ((acts_cont.comp (quant_cont.comp continuous_fst)).clm_apply ((hoist _ _).continuous.comp continuous_snd))
 let y(i:↥(Rent0 V e)):= (sect0 V*chargeA (Thread j) V pM (unionP i.val))⁻¹; have hx:= refill y hc U hh; have ht:= kitE f W Z hz hs hW; exact kitE (y∘U) (fun i=> Z (f i) (W i)) (fun (x:ℂ) (t: Phys M')=> x • t) (by exact continuous_fst.smul continuous_snd) hx ht
end YM.CF.Girt
