import YM.SU5.Relativistic.Schist
import YM.SU5.Relativistic.Elast
import YM.SU5.Relativistic.Frills
import YM.SU5.Relativistic.Impala
import YM.SU5.Relativistic.ToothLake
import YM.SU5.Relativistic.Lazuli
/-! # Actual Fermi pressure. Uses ONE gauge, glue over most blocks, cost via columns. Doesn't assume braIb.
 Supports unrelated to path/refinements -- this is analytic pressure not observable-specific.
 -/
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
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
namespace Papal
open CF.Pannier.Damask
open Buffered
open Papyrus.GaugeFlux
open CF.Papyrus.Granat CF.Pannier.Chancel
variable {a δ κ:ℝ}
private lemma seams (e:0<a)(k:ℕ) : ∀ᶠ W:ℕ in atTop,∃ r:ℕ, W=r+k+1∧
    (2*W+1:ℝ)^4-(2*r+1:ℝ)^4 ≤ a*(2*W+1:ℝ)^4:=by
 let Y(w:ℕ):ℝ:=2*w+1
 have he:Tendsto (fun w:ℕ=>(Y w)⁻¹) atTop (𝓝 0):= by unfold Y; exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0:ℝ)<2)))
 let f(w:ℕ):= 1-(2*((k+1:ℕ):ℝ))*(Y w)⁻¹; have hp:Tendsto (fun w:ℕ=>1-f w ^4) atTop (𝓝 0):=by
    have ht := (he.const_mul (2*((k+1:ℕ):ℝ))); have hh:Tendsto f atTop (𝓝 1):= by simpa only [mul_zero,sub_zero] using Tendsto.sub (tendsto_const_nhds (x:=1)) ht -- binder
    simpa only [one_pow,sub_self] using Tendsto.sub (tendsto_const_nhds (x:=1)) (hh.pow 4)
 filter_upwards [hp.eventually (ge_mem_nhds e), eventually_ge_atTop (k+1)] with i hh hq
 let r:=i-(k+1); have ht:i=r+k+1:=by unfold r; omega
 refine ⟨r,ht,?_⟩; let v:=Y i; have hf:0<v:=by unfold v Y; positivity
 change v^4-Y r^4 ≤a*v^4; rw [show Y r=f i*v by unfold f; rw [sub_mul, one_mul, mul_assoc _ (Y i)⁻¹ v, show (Y i)⁻¹*v=1 from inv_mul_cancel₀ hf.ne',mul_one]; unfold v Y; push_cast; have hv:(i:ℝ)=r+k+1:= (by exact_mod_cast ht); linarith, mul_pow]; apply le_trans (le_of_eq (show v^4- f i^4*v^4=(1-f i^4)*v^4 by ring)); exact mul_le_mul_of_nonneg_right hh (by positivity)
-- volume count harness
private lemma smoothCount (i s d:ℕ) : More (P.Ctor (Y.ir i) (s+d))= More (P.Ctor (Y.ir i) s) * P.R.L^d:=by
 induction d with
 | zero=> rw [Nat.add_zero,pow_zero,mul_one]
 | succ k ih=>
    rw [← Nat.add_assoc, pow_succ,←mul_assoc,←ih]; exact Subtype.ext (kint ..)
private lemma tiles_present (z:ℕ) (i d s:ℕ)(h:d≤ s) : ∃ (C: Side)(L:Ratio C (More (P.Ctor (Y.ir i) s))),2≤ C.val ∧ L.count=P.R.L^d:=by
 obtain ⟨p,rfl⟩:=Nat.exists_eq_add_of_le h; rw [Nat.add_comm d p]
 let A:= More (P.Ctor (Y.ir i) p); refine ⟨A,⟨P.R.L^d,?_⟩,(show 2≤ (P.Ctor (Y.ir i) p).val*2 from Nat.le_mul_of_pos_left _ (P.Ctor (Y.ir i) p).property),rfl⟩
 rw [smoothCount Y i p d]; rfl
private lemma rangePoints {N:Side} (S: Support (More N)): (modesIn N S)ᶜ.card ≤Sᶜ.card*180:=by
 let f(i:Single N):=(node i.1.1,i.1.2,i.2)
 rw [←card_image_of_injective ((modesIn N S)ᶜ) (show Injective f from fun ⟨⟨x,i⟩,j⟩ ⟨⟨y,k⟩,l⟩ e=> by obtain ⟨v,h,w⟩ : x=y ∧ i=k ∧ j=l:= ⟨needle (congrArg Prod.fst e),congrArg (fun i=> i.2.1) e, congrArg (fun i=> i.2.2) e⟩; rw [v,h,w])]
 let A:= Sᶜ ×ˢ (univ: Finset (SpinIdx × SU.Slot)); apply le_trans (b:=A.card) (card_le_card (image_subset_iff.mpr (fun i p=> mem_product.mpr ⟨mem_compl.mpr (fun h=>mem_compl.mp p ((modes_at ..).2 h)),mem_univ _⟩)))
 unfold A; rw [card_product,card_univ,Fintype.card_prod,SU.slots,show Fintype.card SpinIdx=4 from Fintype.card_fin _]

open CF.Papyrus.Franc
private def dustK (r w:ℕ) : ℝ:= (4*((r+4)*2+1)^4*((w+1)+(w+1)+1)^4:ℕ)
lemma postageV(γ d:ℝ)(z N:ℕ)(p:0<d)(g:0<γ) :∃ D:ℝ,0≤D∧∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,N ≤ (count Y s i).val ∧∀ k:ℕ,s ≤ Y.uv k→let G:= gram Y s i k; let M:=G.J.M; let n:= count Y s i; let L:= room Y s i;∀ y:Orbit n,∃ (S:Support (More n))(m:Skye.Seat n→SU.E), Rightful (Lattice.halo z S) (Lattice.gauge m (L y)) 1 γ ∧ (↑(modesIn n S)ᶜ.card:ℝ) ≤ 180*(d*n.val^4)+D*flakes G.p.threshold y.1:=by
 let b:=d/16
 have hb:0<b:=by unfold b; positivity
 obtain ⟨w,l⟩:= eventually_atTop.mp (seams hb z)
 obtain ⟨k',k1⟩:= ((tendsto_pow_atTop_atTop_of_one_lt (show 1<P.R.L.val by have h:= P.V.tallX; omega)).eventually_ge_atTop (2*w+1)).exists
 have ho:Odd (P.R.L^k').val := by change Odd _; simpa using P.R.odd_side.pow (n:=k')
 obtain ⟨W,hW⟩:=ho; have hf:2*w+1≤(P.R.L^k').val:=by exact_mod_cast k1
 obtain ⟨r,l1,l2⟩:= l W (by omega); obtain ⟨τ,hτ,uτ⟩:= stampG_price W γ g
 let U:=(2*r+1:ℝ)^4; let X:=dustK P.J.n W; have hx:0≤X:=by unfold X dustK; positivity
 let K:= X*U*180; have hK:0≤K:=by unfold K U; positivity
 have hs:Tendsto (temp ∘ hat P.R.L P.x) atTop (𝓝 0):= (show Tendsto temp atTop (𝓝 0) by simpa using Work.E09.radiusB_temp 0).comp (turnover P)
 refine ⟨K,hK,?_⟩
 filter_upwards [eventually_ge_atTop k',hs.eventually (ge_mem_nhds hτ),hs.eventually (ge_mem_nhds P.J.ht)] with s kS hτ' hu
 filter_upwards [(count_grows Y s).eventually_ge_atTop (2*W+3+N)] with i hi ; have hw:N≤ (count Y s i).val:=by omega
 refine ⟨hw,?_⟩; intro k tk WP n L' y
 obtain ⟨V,F0,C0,H⟩:= tiles_present Y 0 i k' s kS; have hl:F0.count.val=2*W+1:= H ▸ hW
 let σ:=WP.p.threshold; let A:=L' y; have hz:σ=temp (hat P.R.L P.x s):= (congrArg BudgetPoint.threshold (prices_plot Y s i k tk).1).trans (Y.meter.boot s).1
 have hV:2*(W+1)<(More n).val:=by change _ < n.val*2; change _ ≤ n.val at hi; omega
 let G:=flakes σ y.1
 have hG:( (Lattice.halo (W+1) (RG.flags σ A)).card:ℝ) ≤ G*X:=by
    have he:= Py.Rate.Pannier.grease_f (roofage Y i s) y (t:=σ) (hz ▸ hu) (W+1) 1; change (halo _ (RG.flags σ (pull 1 0 A))).card≤_ at he; rw [show Lattice.pull 1 0 A=A from ?_] at he -- tune
    · exact (Nat.cast_le.mpr he).trans_eq (by unfold G X dustK flakes; push_cast; ring)
    rw [Lattice.pull_one]; ext i; simp [Lattice.translate]
 obtain ⟨S,m,g₀,g1⟩:=wallMaps F0 hl hV A σ γ (fun i x=>uτ _ WP.p.threshold_pos.le (show σ ≤ τ from hz.trans_le hτ') hV le_rfl i A x) (show r+z+1 ≤ W by omega) hG -- tuner
 refine ⟨S,m,g₀,?_⟩; let Q:=modesIn n S
 have hv':16*(n.val:ℝ)^4=(V.val:ℝ)^4*(2*W+1:ℝ)^4:=by
    have hh:(n.val:ℝ)*2=(V.val:ℝ)*(2*W+1:ℝ):=by exact_mod_cast show n.val*2=V.val*(2*W+1) from F0.exact_size.trans (congrArg (V.val*·) hl)
    rw [←mul_pow, ←hh]; ring
 have ht': ((Sᶜ).card:ℝ) ≤ d*n.val^4+(G*X)*U:=by apply le_trans g1; refine add_le_add_left (((mul_le_mul_of_nonneg_left l2 (by positivity : (0:ℝ)≤(V.val:ℝ)^4)).trans_eq ?_)) _; unfold b; linear_combination -d/16*hv'
 have hg: (Qᶜ.card:ℝ) ≤ (d*n.val^4+G*X*U)*180:=by
    have he: (Qᶜ.card:ℝ) ≤ Sᶜ.card* (180:ℝ):=by exact_mod_cast rangePoints S
    exact he.trans (mul_le_mul_of_nonneg_right ht' (by norm_num))
 refine hg.trans_eq ?_; unfold K G; ring
private lemma tumble {n:Side}{P:Op (Single n)}(f:Skye.Seat n→SU.E)(k:ℕ): stunt k (tickA n) (twist (tradew n f) P)=stunt k (tickA n) P:=by
 unfold stunt; nth_rw 1 [←tick_g f]; rw [jv_twist, det_twist]
lemma scaleTilt(t:P.d ≤ δ)(x:∃ N:ℕ,∀ η>(0:ℝ), ∃ γ>(0:ℝ),∃ w:ℕ,∀ n:Side,N ≤ n.val→ Winter P.K.j δ n γ w η)(ε:ℝ)(p:0<ε):∀ᶠ m:ℕ in atTop,∃ K:ℝ,0≤K ∧∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ, s ≤ Y.uv k → ∀ y:Orbit (count Y s i), let G:= gram Y s i k; let n:= count Y s i; let V:= spar P.K.j G.J.M (room Y s i y); stunt m (tickA n) V ≤ seaPrec P.K.j n G.J.M+ ε*sites n+K*flakes G.p.threshold y.1 :=by
 filter_upwards [CF.Papyrus.Franc.purge P.K.j (P.kJ ▸ (by omega)) ε p] with m H0
 let T:=1-CF.Papyrus.Franc.hatch m; let V:= (2*(m:ℝ)+2)/T; have hf:0<T:= sub_pos.mpr (hatch_up _)
 have hp:0<V:=by unfold V; positivity
 let W:= ε/(600*V); have hW:0 < W:=by unfold W; positivity
 obtain ⟨N,u⟩:=x; obtain ⟨γ,v,f,w⟩:=u W hW
 obtain ⟨D,hD,h⟩:= postageV Y γ W f N hW v; refine ⟨2*(V*D),by positivity,?_⟩
 filter_upwards [h] with s h; filter_upwards [h] with i hi k tk y G n V'
 obtain ⟨S,K,X,Y'⟩:=hi.2 k tk y; let U:=room Y s i y; let F:=Lattice.gauge K U; let X':=spar P.K.j G.J.M F
 let Q:=spar P.K.j G.J.M (1:Pane n)
 have hu:Guard U P.d:=(roofage Y i s).paid y; have ht:Guard F P.d:=Cube.Guard.cov hu _
 have hy:Sparkle n P.d G.J.M P.K.j:= P.U.broadness _ (P.J.gran.trans ((Y.voyage i).ownership s).size) _
 have hx:IsStarProjection Q:=hy.projection _ (guard0 P.dpos.le); have hv:‖(X'-Q)*Vo S‖≤W:= hearthB_wind (b:=false) (w n hi.1) (P.dpos.le.trans t) (ht.shrink t) X
 have hl:= CF.Papyrus.Franc.thread (hy.projection _ ht) hx (plus_P n) m (S:=modesIn n S) hv hW.le
 rw [show spar P.K.j G.J.M F=twist (tradew n K) V' from hy.covary _ _ hu,tumble] at hl
 apply hl.trans; rw [show 2*(m:ℝ)+2=V*T from (div_mul_cancel₀ _ hf.ne').symm,Pic.units_t]; apply le_trans (add_le_add_left (H0 n _ hx) _) _
 let z:=Y'; let C:=flakes G.p.threshold y.1
 have h' : ((modesIn n S)ᶜ.card:ℝ) ≤ 180*(W*n.val^4)+D*C:=Y'
 change seaPrec P.K.j n _+_+((V*T)*_)/T≤ _+ε*((((n.val*2):ℕ):ℝ)^4)+_
 have ht:C*C≥0:=mul_self_nonneg C; have hz: W*(600*V)=ε:=div_mul_cancel₀ _ (by positivity)
 let A:=180*(n.val:ℝ)^4*W+((modesIn n S)ᶜ.card:ℝ)*2
 rw [show V*T*A/T= V*A from (by field_simp)]
 unfold A; push_cast; nlinarith only [mul_le_mul_of_nonneg_left h' hp.le, congrArg (fun x:ℝ=> x*((n.val:ℝ)^4)) hz, show 0≤ ε*(n.val:ℝ)^4 by positivity]
lemma bakeYn {R':ℝ}(H:CF.Papyrus.Franc.postage P.K.j R')(p:0≤R')(t:P.d ≤ δ)(x:∃ N:ℕ,∀ η>(0:ℝ), ∃ γ>(0:ℝ),∃ w:ℕ,∀ n:Side,N ≤ n.val→ Winter P.K.j δ n γ w η)(q:CF.Papyrus.Franc.charge R'≤ P.h)(m:ℕ) (ε:ℝ)(w:0<ε): ∃ K:ℝ,0≤K∧∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ,s ≤ Y.uv k →let G:= gram Y s i k; let n:=count Y s i; let L:= room Y s i;∀ y:Orbit n,∀ Yp:IsStarProjection (spar P.K.j G.J.M (L y)), ∀ T:Shaft (Single n),‖T.sell‖≤2→‖T.buy‖≤2→‖(T.foldC (Saber (B:=tickA n) Yp m)).glow (Graph.mile P.K.j G L y)‖ ≤ Real.exp (ε*sites n+K*flakes G.p.threshold y.1):=by
 obtain ⟨N,v⟩:=x
 obtain ⟨C,hC,Yp⟩:=off_age (n:=m)
 obtain ⟨γ,g,z,F⟩:= localMail (P.dpos.le.trans t) v H m
 let l:= 2*(1+C); have hl:0<l:=by unfold l; positivity
 let d:= ε/(180*32*l); have he:0<d:=by unfold d; positivity
 obtain ⟨D,hD,r⟩:= postageV Y γ d z N he g
 obtain ⟨V,u,X⟩:=lanternX (t:=P.d) (r:=P.J.n) (mul_pos hl (show (0:ℝ)<2 by norm_num)|>.le) (cash_v P.W.C) P.J.ht (level_p P.W.C) (ε/4) (by positivity)
 let K:=V+D*2*l; have hK:0≤K:=by unfold K; positivity
 have hb:=(((dev_R P.R).1.low (k:=1) (by omega)).spine.eventually (ge_mem_nhds (show 0<(ε:ℝ)/8 by positivity)))
 refine ⟨K,hK,?_⟩
 filter_upwards [r,(turnover P).eventually hb,(turnover P).eventually X] with s hr hu hv
 obtain ⟨a,X⟩:= hv; filter_upwards [hr,(count_grows Y s).eventually_ge_atTop a] with i hi hA k tk G n L y yP T tx ty
 obtain ⟨S,Q,g₀,g1⟩:=hi.2 k tk y
 let A:=L y; let B:=Lattice.gauge Q A; let Z:=spar P.K.j G.J.M A
 obtain ⟨a,b,c,z,H'⟩:=prices_plot Y s i k tk
 have ht: G.p.threshold=temp (hat P.R.L P.x s):= (congrArg BudgetPoint.threshold a).trans (Y.meter.boot s).1
 let S':=T.foldC (Saber (B:=tickA n) yP m)
 let W':=flakes G.p.threshold y.1
 let R:=fun p:ℝ=> Real.exp p
 let M':=180*(n.val:ℝ)^4
 let N':=sites n
 let K':= Q
 have hS:‖Comb (tickA n) Z m‖ ≤ C:=Yp n Z yP; have hy:Guard A P.d:= (roofage Y i s).paid y; have hx:Sparkle n P.d G.J.M P.K.j:=P.U.broadness _ (P.J.gran.trans ((Y.voyage i).ownership s).size) _
 let D':= Complex.exp (-Pec.pigment G.J.I A) • exp (dg (Graph.actF P.K.j G L y)); have hw: ‖S'.glow D'‖≤ R (ε/4*N'+V*W'):=by
    have hu':Pays (l*2) D' (R (ε/4*N'+V*W')):= by unfold W'; rw [ht]; exact X (roofage Y i s) _ _ _ P.K.j H' hA y yP
    apply loomBound S' _ _ _ _ D' hu'
    · unfold S' Shaft.foldC Saber; simp only; apply mul_le_mul_of_nonneg_right _ zero_le_two; exact (norm_mul_le ..).trans (mul_le_mul tx ((norm_add_le ..).trans (by rw [norm_star,norm_one]; linarith only [hS])) (norm_nonneg _) zero_le_two)
    unfold S' Shaft.foldC Saber; simp only; apply mul_le_mul_of_nonneg_right _ zero_le_two; exact (norm_mul_le ..).trans ((mul_le_mul_of_nonneg_left ty (norm_nonneg _)).trans ((mul_le_mul_of_nonneg_right ((norm_sub_le ..).trans (by rw [norm_star,norm_one]; exact add_le_add_right hS _)) zero_le_two).trans_eq (mul_comm ..)))
 have hp : 1≤ P.h:=(show 1≤ CF.Papyrus.Franc.charge R' from (by unfold CF.Papyrus.Franc.charge; linarith only [p])).trans q
 let F':= (univ : Finset Bool) ×ˢ (modesIn n S)ᶜ
 have hh(i:LeanV (Single n)): ‖S'.glow (drawT Z i)‖≤P.h*(if i∈F' then Real.exp l else 1):=by
    split_ifs with x
    · apply (scyth (B:=tickA n) yP m _ hS hC.le i _ tx ty).trans ((le_trans _ (le_mul_of_one_le_left (Real.exp_pos _).le hp))); apply (le_add_of_nonneg_right zero_le_one).trans; exact Real.add_one_le_exp l
    rw [mul_one]; have he: node i.2.1.1∈S:=by
       by_contra h; exact x (Finset.mem_product.mpr ⟨mem_univ _,mem_compl.mpr fun p=>h ((modes_at ..).1 p)⟩)
    have hk:Guard B P.d:=Cube.Guard.cov hy _; exact (F n hi.1 _ (hx.projection _ (guard0 P.dpos.le)) S B A Q g₀ rfl (hk.shrink t) yP (hx.projection _ hk) (hx.covary _ Q hy).symm i he T tx ty).trans q
 change ‖S'.glow (Graph.mile _ _ _ _)‖≤ R _
 rw [show Graph.mile P.K.j G L y=tank Z (G.board y)*D' from (Algebra.mul_smul_comm ..).symm,Shaft.glow_mult]
 apply (norm_mul_le ..).trans (le_trans (mul_le_mul (boardG S' G P.h _ _ _ _ H' Z y _ F' (by linarith) hl.le hh) hw (norm_nonneg _) (Real.exp_pos _).le) _)
 unfold R; rw [←Real.exp_add]; apply Real.exp_monotone
 have hV : (F'.card:ℝ) ≤ 2*(180*(d*(n.val:ℝ)^4)+D*W'):=by
    unfold F'; rw [card_product]; push_cast; exact mul_le_mul_of_nonneg_left g1 (show 0 ≤ (2:ℝ) by norm_num)
 unfold K; let E:=dleaf P.R.L (hat P.R.L P.x s) -- tune pressure
 have hx:E≤ε/8:=hu
 change (E+E+E)*N'+l*_+(ε/4*N'+V*W') ≤ ε*N'+(V+D*2*l)*W'
 have ht': 0 ≤ N':=by change 0≤((((n.val*2):ℕ):ℝ)^4); positivity
    -- tuner
 have hd:180*32*l*d=ε:= by unfold d; field_simp
 let C:=(n.val:ℝ)^4; have he: N'=16*C:=by change (((n.val*2:ℕ):ℝ)^4)=_; unfold C; push_cast; ring
 rw [he]; nlinarith only [mul_le_mul_of_nonneg_left hV hl.le, congrArg (fun x:ℝ=> x*C) hd, mul_le_mul_of_nonneg_right hx (show 0≤ C by unfold C; positivity),mul_nonneg w.le (show 0≤ C by unfold C; positivity)] -- tune
end Papal
end LocalLimit
end Rate
end YM.CF.Py
