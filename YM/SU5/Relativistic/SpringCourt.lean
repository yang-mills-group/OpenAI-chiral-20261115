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
private lemma twist_now {n:Side}{P:Op (Single n)}(f: Skye.Seat n → SU.E) (a:ℝ):
    crater (tickA n) (twist (tradew n f) P) a=crater (tickA n) P a:=by
 let X:=twist (tradew n f); let U:=tickA n; unfold crater
 rw [show Bolt (tickA n) ((twist (tradew n f)) P) a=X (Bolt U P a) from ?_, show Matrix.det (X _)= _ from (show Matrix.det (X (Bolt U P a))= _ from Fock.det_twist ..)]
 unfold X Bolt U; rw [map_add,map_mul,map_mul,map_sub,map_add,map_smul,map_sub,map_one,tick_g]
private def dustK (r w:ℕ) : ℝ:= (4*((r+4)*2+1)^4*((w+1)+(w+1)+1)^4:ℕ)
lemma frosts (e:0<a)(v:a ≤ 1)(t:P.d ≤ δ)(x:∃ N:ℕ,∀ η>(0:ℝ), ∃ γ>(0:ℝ),∃ w:ℕ,∀ n:Side,N ≤ n.val→ Winter P.K.j δ n γ w η) (ε:ℝ)(p:0<ε):∃ K:ℝ,0≤K∧∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ,s ≤ Y.uv k→let G:= gram Y s i k; let M:=G.J.M; let n:= count Y s i; let L:= room Y s i;∀ y:Orbit n,
    crater (tickA n) (spar P.K.j M (L y)) a ≤ crater (tickA n) (spar P.K.j M (1:Pane n)) a+ ε*sites n+ K*flakes G.p.threshold y.1:=by
 let d:=ε*a^2/1000; let b:=d/16; have hd:0<d:=by unfold d; positivity
 have hb:0<b:=by unfold b; positivity
 obtain ⟨N,u⟩:=x; obtain ⟨γ,g,z,F⟩:= u d hd; obtain ⟨w,l⟩:= eventually_atTop.mp (seams hb z)
 obtain ⟨k',k1⟩:= ((tendsto_pow_atTop_atTop_of_one_lt (show 1<P.R.L.val by have h:= P.V.tallX; omega)).eventually_ge_atTop (2*w+1)).exists
 have ho:Odd (P.R.L^k').val := by change Odd _; simpa using P.R.odd_side.pow (n:=k')
 obtain ⟨W,hW⟩:=ho; have hf:2*w+1≤(P.R.L^k').val:=by exact_mod_cast k1
 obtain ⟨r,l1,l2⟩:= l W (by omega); obtain ⟨τ,hτ,uτ⟩:= stampG_price W γ g
 let U:=(2*r+1:ℝ)^4; let X:=dustK P.J.n W; have hx:0≤X:=by unfold X dustK; positivity
 let K:= X*U*180 / a^2; have hK:0≤K:=by unfold K U; positivity
 have hs:Tendsto (temp ∘ hat P.R.L P.x) atTop (𝓝 0):= (show Tendsto temp atTop (𝓝 0) by simpa using Work.E09.radiusB_temp 0).comp (turnover P)
 refine ⟨K,hK,?_⟩
 filter_upwards [eventually_ge_atTop k',hs.eventually (ge_mem_nhds hτ),hs.eventually (ge_mem_nhds P.J.ht)] with s kS hτ' hu
 filter_upwards [(count_grows Y s).eventually_ge_atTop (2*W+3+N)] with i hi k tk WP M n L' y
 obtain ⟨V,F0,C0,H⟩:= tiles_present Y 0 i k' s kS; have hl:F0.count.val=2*W+1:= H ▸ hW
 let σ:=WP.p.threshold; let A:=L' y; have hz:σ=temp (hat P.R.L P.x s):= (congrArg BudgetPoint.threshold (prices_plot Y s i k tk).1).trans (Y.meter.boot s).1
 have hV:2*(W+1)<(More n).val:=by change _ < n.val*2; change _ ≤ n.val at hi; omega
 let G:=flakes σ y.1
 have hG:( (Lattice.halo (W+1) (RG.flags σ A)).card:ℝ) ≤ G*X:=by
    have he:= Py.Rate.Pannier.grease_f (roofage Y i s) y (t:=σ) (hz ▸ hu) (W+1) 1; change (halo _ (RG.flags σ (pull 1 0 A))).card≤_ at he; rw [show Lattice.pull 1 0 A=A from ?_] at he -- tune
    · exact (Nat.cast_le.mpr he).trans_eq (by unfold G X dustK flakes; push_cast; ring)
    rw [Lattice.pull_one]; ext i; simp [Lattice.translate]
 obtain ⟨S,m,g₀,g1⟩:=wallMaps F0 hl hV A σ γ (fun i x=>uτ _ WP.p.threshold_pos.le (show σ ≤ τ from hz.trans_le hτ') hV le_rfl i A x) (show r+z+1 ≤ W by omega) hG -- tuner
 let V':=gauge m A; let Z:=spar P.K.j M V'; let R:=spar P.K.j M (1:Pane n)
 have hA:= (roofage Y i s).paid y; have hu': Guard V' P.d:=Cube.Guard.cov hA _
 have hp:Sparkle n P.d M P.K.j := P.U.broadness _ (P.J.gran.trans ((Y.voyage i).ownership s).size) _
 let Q:=modesIn n S; have hT:‖(Z-R)*cutM Q‖≤d:= hearthB_wind (b:=false) (F n (by change _ ≤ n.val at hi; omega)) (P.dpos.le.trans t) (hu'.shrink t) g₀
 let B:=tickA n
 have hb':B*cutM Q=cutM Q*B:=by unfold B; rw [touchP,Fock.cutM,Fock.cutM,Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]; apply congrArg Matrix.diagonal; ext i; rw [mul_comm]
 have he:= hopeful (plus_P n) (hp.projection _ hu') (hp.projection _ (guard0 P.dpos.le)) e v hb' hd.le hT; rw [show spar (N:=n) P.K.j M V'=twist (tradew n m) (spar (N:=n) P.K.j M A) from (show Z=twist (tradew _ m) (spar P.K.j M A) from hp.covary _ _ hA), twist_now] at he -- hp Q inference hT
 apply he.trans; rw [add_assoc]; apply add_le_add_right
 have hv':16*(n.val:ℝ)^4=(V.val:ℝ)^4*(2*W+1:ℝ)^4:=by
    have hh:(n.val:ℝ)*2=(V.val:ℝ)*(2*W+1:ℝ):=by exact_mod_cast show n.val*2=V.val*(2*W+1) from F0.exact_size.trans (congrArg (V.val*·) hl)
    rw [←mul_pow, ←hh]; ring
 have ht': ((Sᶜ).card:ℝ) ≤ d*n.val^4+(G*X)*U:=by apply le_trans g1; refine add_le_add_left (((mul_le_mul_of_nonneg_left l2 (by positivity : (0:ℝ)≤(V.val:ℝ)^4)).trans_eq ?_)) _; unfold b; linear_combination -d/16*hv'
 have hg: (Qᶜ.card:ℝ) ≤ (d*n.val^4+G*X*U)*180:=by
    have he: (Qᶜ.card:ℝ) ≤ Sᶜ.card* (180:ℝ):=by exact_mod_cast rangePoints S
    exact he.trans (mul_le_mul_of_nonneg_right ht' (by norm_num))
 apply le_trans (div_le_div_of_nonneg_right (div_le_div_of_nonneg_right (add_le_add_right (mul_le_mul_of_nonneg_right hg (by norm_num : (0:ℝ)≤2)) _) (sq_nonneg _)) (by norm_num : (0:ℝ)≤2))
 rw [Pic.units_t]; change _ ≤ ε*(((More n).val:ℝ)^4)+K*G
 change _≤ ε*((((n.val*2):ℕ):ℝ)^4)+K*G; unfold d K; push_cast; field_simp; nlinarith only [show 0≤ ε*(n.val:ℝ)^4*a^2 by positivity] -- tune
-- later certificate combined
end Papal
end LocalLimit
end Rate
end YM.CF.Py
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.frosts
