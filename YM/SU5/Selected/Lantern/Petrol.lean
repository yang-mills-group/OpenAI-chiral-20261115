import YM.SU5.Selected.Lantern.Scatter
import YM.SU5.Selected.Pack.Batten
import YM.SU5.Selected.Airy.Income

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
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
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
local notation "G🌸"=> SU.group
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
namespace Papal
open Buffered Afterglow Journey
open scoped ComplexOrder
open CF.Pannier.Chancel
open YM.CF.Pannier.Chancel.Lantern
variable (H:Real.exp 1≤ P.x)
open Crest
namespace Mileage
local notation "κI" i:max s:max k:max => (gram Y s i k).J.M
local notation "SN" i:max s:max => Papal.count Y s i
private lemma tender_g(s i k:ℕ)(f:Ferry Y s i k): Twosome (tent Y H) (Papal.count Y s i) (solder Y i k f.depth s):=by
 let m:=momentm Y i s; let K₀:=tent Y H; let X:=collector Y H i k f.depth s; let F:=solder Y i k f.depth s; have ht:=boxprice Y H i k f.depth s f.fire f.enters
 apply across K₀ m F (terrain Y H (Y.ir i) s) (Y:=X) (fun x=>rfl); exact fun a z _ p=>Metered.twiceX ht a z p
where across (K:Calibration)(m:Side){n:Side} (X:Mark n→ℂ)(p:K.c m=n){Y:Mark (K.c m)→ℂ}(h:∀ f,Y f=X (p▸f)) (g:Twosome K (K.c m) Y):Twosome K n X:=by subst n; rw [show X=Y from Eq.symm (funext h)]; exact g
private lemma small_after (a b k:ℂ) (n : ℕ)(s δ:ℝ)(δ0:0 < δ)(ps:(↑n:ℝ) ≤ s)(hn:0<n)
    (p : ‖k‖ ≤ Real.exp (-δ * s))(q : ‖k-b‖ ≤ Real.exp (-δ*s))
    (g: ‖a‖^n ≤ ‖b‖) : ‖a‖ ≤ Real.exp (1-δ):=by
  apply (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.exp_pos _).le hn.ne').mp
  have ht:(1:ℝ)≤n:=by exact_mod_cast hn
  apply g.trans; rw [←Real.exp_nat_mul]; refine ((norm_le_norm_sub_add b k).trans (add_le_add ((norm_sub_rev ..).trans_le q) p)).trans ?_
  rw [show (↑n:ℝ)*(1-δ)=n+(-δ*(n:ℝ)) by ring,Real.exp_add]
  have hp: Real.exp (-δ*s) ≤ Real.exp (-δ*(n:ℝ)):= Real.exp_le_exp_of_le (by nlinarith)
  have hE: 2 ≤ Real.exp (n:ℝ):=by linarith only [ht,Real.add_one_le_exp (n:ℝ)]
  nlinarith only [hE,hp, (show 0<Real.exp (-δ*(n:ℝ)) from Real.exp_pos _)]

lemma traverses (i k s:ℕ)(p:s<Y.uv k):
    (gram Y s i k).J.M= upMale P.R.L P.R.odd_side (gram Y (s+1) i k).J.M:=by
 let t:=Y.voyage i; let z:=Y.uv k; let h:= t.X z; let V:= P.W.arm (Y.meter.large.trans t.funds) z; have he(q:ℕ)(w:q≤z): (gram Y q i k).J= V.Q q:= (h.pull.owns q w).taste.symm; rw [he s p.le, he (s+1) p]; exact (V.pass s p).grown
lemma stakesBill {i k:ℕ}(d:ℕ) : ∀ s:ℕ,s+d ≤ Y.uv k → d+1 ≤ ((gram Y s i k).J.M.val).val:= by
 induction d with
 | zero=> exact fun i _=> (κI _ _ _).val.property -- macro insufficient
 | succ d ih=>
    intro s t; rw [traverses _ _ _ _ (by omega)]; let v:=(gram Y (s+1) i k).J.M.val.val; change _ ≤ P.R.L.val*v; have hh:d+1 ≤ v:= ih (s+1) (by omega); have hv:=P.R.coarse; nlinarith
lemma backs (s:ℕ): ∀ (d:Side), ∀ᶠ k:ℕ in atTop,∀ i, d≤(gram Y s i k).J.M.val:=by
 intro d; filter_upwards [Y.uv_grows.tendsto_atTop.eventually_ge_atTop (s+d.val)] with k p i; change d.val ≤ _; apply le_trans _ (stakesBill Y d.val s p); omega
lemma heartland (s:ℕ) : ∀ i:ℕ, Tendsto (fun k=> (gram Y s i k).J.M) atTop Airy.mtn:=by
 intro i; apply tendsto_comap_iff.mpr; exact tendsto_atTop.mpr fun k=> (backs Y s k).mono fun _ h=> h i

lemma precinct_4 (s i k:ℕ): spar P.K.j (gram Y s i k).J.M (1:Pane (Papal.count Y s i))= (Airy.tip (Papal.count Y s i) (gram Y s i k).J.M) ⊗ₖ (1:Op SU.Slot):=by
 rw [P.kJ,Dial.spar,profile_trivial,Tulip.funde_flat 4 (by decide)]; let M:=(gram Y s i k).J.M; let n:=Papal.count Y s i; congr 1; apply (cart_traded (A:=Fir.bar 4 M.val) (cBar 4 M.val true (by omega) M.property) n).trans; exact Airy.freeze_square _ -- tune
open Airy (Frame Coast)
lemma airyCost (s n p:ℕ)(G:Side)(hc:8≤G.val)(hb:n≥4) : ∃ C> (0:ℝ),∃ K:ℝ,0<K∧∀ (D:Side)(ε:ℝ),0<ε→ε≤1→∃ (w:ℕ) (X Z: Airy.Coast→ Airy.Wq p),
    Airy.Frame (G:=G) n p X Z D w (K* Real.exp (-(1/2))^D.val+ε*(2*C+1)) (2*ε) (C+1) ∧
    ∀ᶠ k:ℕ in atTop,∀ i:ℕ, ∀ (q:Type)[Fintype q][DecidableEq q],∀ (x: q→Site (Papal.count Y s i)× Fin p), Airy.Beacons G D p x→
       let F':= Airy.hire p X x; let V':= Airy.hire p Z x; ‖F'‖≤C+1∧‖V'‖≤C+1∧‖F'ᴴ* V'-1‖≤ K*Real.exp (-(1/2))^D.val+ ε*(2*C+1) ∧ ‖(((1-Airy.tip _ (κI i s k)):Op _)* V': Matrix _ q ℂ)‖≤ 2*ε :=by
 obtain ⟨C,c,K,h,u⟩:=Airy.looked n p G hc hb; refine ⟨C,c,K,h,fun D ε pε tε=>?_⟩; obtain ⟨w,X,Z,F⟩:=u D ε pε tε; refine ⟨w,X,Z,F,?_⟩; obtain ⟨M,d⟩:= Airy.mtn_out _ F.ticket; filter_upwards [backs Y s M] with k c i q _ _ x f; exact d _ (c i) (Papal.count Y s i) x f
-- pressure application. layout measured in base gauge cells L (`width W` governs joint support B).
variable {Ω T A δ γ ξ η J R E a ε:ℝ}{r d w maxW num t:ℕ}{q:Type}[Fintype q][DecidableEq q]
-- need δ≥P.d criterion & Winter eventual. ratio lower on copy exponent. upper on #marks `num`. N based geometric. hK : $a length≥$ .
open CF.Pannier.Chancel (cows)
lemma loomPrice (Vw:∀ᶠ k:ℕ in atTop,∀ N:Side, k ≤ N.val → Winter P.K.j δ N γ w ε ∧∀ M:Tulip.Male, safeReflect M P.K.j δ N)
    (fee : E⁻¹ ≤ P.h) (he:0<E)(e':E≤1)(v:Inflation A P)(tL:P.J.n ≤ t)
    (pδ:P.d ≤ δ)(pR:0<R)(eJ:1≤J)(pη:0≤η)(pξ:0≤ξ)(q₁:η+(ξ+ε*R) ≤ 1/3)(q₂:ξ+ε*R+(R*2)*(η+(ξ+ε*R))≤ E^3)
    (t0:r>0)(p:0≤a)(g:J*(E*(2*R+3))≤ Real.exp (-2*(a+J)))(f:0<Ω)
    (z:a* ((r:ℝ)/((4 * ((maxW+addgap (tent Y H):ℕ):ℝ))^4))≥ T) (pX: sealPrice P.V P.W - T+blossom P.K+(A+1) ≤ -Ω) (num:ℕ) (q:Type)[Fintype q][DecidableEq q] :
    ∀ᶠ s in atTop,∀ᶠ i:ℕ in atTop,∀ᶠ k:ℕ in atTop,(Y.voyage i).kick≤k ∧ s≤Y.uv k ∧ ∀ (L:List (Cab (Papal.count Y s i))), 0<L.length→ L.length ≤ num→ CF.Pannier.Chancel.Lantern.Service (κI i s k) P.K.j w t (gram Y s i k).p.threshold η ξ J R δ q r L →(∀ a:Axis,cows a (Resort L) maxW) →
    ‖Journey.compass Y i k s (guest L)‖ ≤ 2 * Real.exp (1-Ω) :=by
 let x(s):=hat P.R.L P.x s; let κ':ℝ:=(a+J)*(4*(t+t+1)^4*r:ℕ); let K':=tent Y H; obtain ⟨N,U⟩:= Vw.exists
 have e: Tendsto (fun s:ℕ=> temp (x s)) atTop (𝓝 0):=(show Tendsto temp atTop (𝓝 0) by simpa using Work.E09.radiusB_temp 0).comp (turnover P)
 filter_upwards [e.eventually (ge_mem_nhds P.J.ht),measured Y v (inv_pos.mpr he).le fee (κ':ℝ)] with s θ h₀
 let B:= maxW + addgap K'; have hB:0<B:= Nat.add_pos_right _ addgap_pos; let π:= r/ ((4 * (B:ℝ))^4); -- π notation!
 filter_upwards [h₀,(count_grows Y s).eventually_ge_atTop (N+B)] with i e₀ hK
 let C:=Papal.count Y s i; let F:=Vw; let μ:= More C; let D:=sites C; let A₀:= J^((μ).val^4*num*r); have hp:0<J:=zero_lt_one.trans_le eJ
 let G:=Real.exp (-Ω*D)/A₀; have hA:0<A₀:= by unfold A₀; positivity
 have w0: N+B ≤ C.val:=hK; obtain ⟨e'₁,b'⟩:=U C (by omega)
 filter_upwards [ferry_later Y s i, thaw_plot Y G (by unfold G; positivity) s] with k S φ
 refine ⟨S.depth,S.enters,fun L pL Ln h q'=>?_⟩; let M':=κI i s k; let X₀:=Journey.compass Y i k s; let Y₀:= solder Y i k S.depth s
 obtain ⟨V',T',eT,t',eL,vT,hT,k'⟩:= Roads.replicate (B:=maxW) (tender_g Y H s i k S) (b' M') (terrain Y H (Y.ir i) s).symm (show B ≤ C.val from by omega) L h q'
 let y:=Papal.gram Y s i k
 have ht:y.p.threshold=temp (x s):=((congrArg BudgetPoint.threshold (prices_plot Y s i k S.enters).1).trans (Y.meter.boot s).1)
 have gT:‖X₀ (guest V')‖ ≤ Real.exp (-Ω*D):=by
    have hbT:Backlog Y s i k E⁻¹ T κ' (guest V'):=by
       intro x'; refine eT.poolPrice P.J.k P.J.n e'₁ (roofage Y i s) (ht.trans_le θ) tL pδ pR eJ E he e' q₁ q₂ pη pξ a T π t0 p g z ?_ x' _ _ (safety Y s i k x').1 (safety Y s i k x').2 (touchP C ▸ tickB C) -- orientation
       -- order lemma poolPrice has u l g? dot position maybe
       have hv:T' ≤ V'.length:= eL.symm ▸ Nat.le_mul_of_pos_right _ pL; let r₀:=(V'.length:ℝ)*r
       have hT':D ≤ (V'.length:ℝ)*(4*(B:ℝ))^4:= by
           have ha: sites C ≤ T' * ( (4:ℝ)* ↑B)^4:= by unfold sites; exact_mod_cast hT
           exact ha.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hv) (by positivity))
       change _ ≥ π* _; unfold π; push_cast; rw [div_mul_eq_mul_div]; apply (div_le_iff₀ (by positivity)).mpr; nlinarith only [mul_le_mul_of_nonneg_left (show sites C ≤_ from hT') (Nat.cast_nonneg (α:=ℝ) r)] -- tune push & defeq
    exact (e₀ k S.depth S.enters _ T (eT.permit (subset_refl _)).env hbT).trans (Real.exp_le_exp_of_le (mul_le_mul_of_nonneg_right pX (by unfold sites; positivity)))
 have bL:‖X₀ (guest V')-Y₀ (guest V')‖≤Real.exp (-Ω*D):= ((φ i S.depth (guest V') A₀ (eT.permit (subset_refl _)).env (fun x=> (eT.guests_v x hp.le).trans (pow_le_pow_right₀ eJ (Nat.mul_le_mul_right r (le_trans eL.le (Nat.mul_le_mul vT Ln))))))).trans_eq (div_mul_cancel₀ _ hA.ne')
 have hv:(T':ℝ)≤ D:= by unfold D sites; exact_mod_cast vT
 let V':=guest L
 have he:‖Y₀ V'‖≤ Real.exp (1-Ω):= small_after _ _ _ _ _ _ f hv t' gT bL k'
 have hp0 : L.length ≤ μ.val^4*num:= Ln.trans (Nat.le_mul_of_pos_left _ (pow_pos μ.property _))
 have hT :‖X₀ V'-Y₀ V'‖≤ Real.exp (-Ω*D):= ((φ i S.depth V' A₀ (h.permit (subset_refl _)).env (fun x=>(h.guests_v x hp.le).trans (pow_le_pow_right₀ eJ (Nat.mul_le_mul_right _ hp0))))).trans_eq (div_mul_cancel₀ _ hA.ne')
 have hd:1 ≤ D:= sites_pos _; apply (norm_le_norm_sub_add _ (Y₀ V')).trans; refine (add_le_add (hT.trans ?_) he).trans (le_of_eq (by ring)); apply Real.exp_monotone; nlinarith
end Mileage
end Papal
end LocalLimit
end Rate
end YM.CF.Py
open YM.CF.Py.Rate.LocalLimit.Papal.Mileage
#print axioms airyCost
#print axioms loomPrice
#print axioms precinct_4
