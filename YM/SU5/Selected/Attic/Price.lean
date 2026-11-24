import YM.SU5.Selected.Attic.Blason
import YM.SU5.Selected.Attic.Rusk
import YM.SU5.Selected.Dais.Saga
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
namespace Convent
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

-- pressure application. layout measured in base gauge cells L (`width W` governs joint support B).
variable {Ω T A δ γ ξ η J R E a ε:ℝ}{r d w maxW num t:ℕ}{q:Type}[Fintype q][DecidableEq q]
-- need δ≥P.d criterion & Winter eventual. ratio lower on copy exponent. upper on #marks `num`. N based geometric. hK : $a length≥$ .
open CF.Pannier.Chancel (cows)
open CF.Pannier.Chancel.Attic CF.Pannier.Chancel.Lantern.Alternative
lemma AtticPrice (Vw:∀ᶠ k:ℕ in atTop,∀ N:Side, k ≤ N.val → Winter P.K.j δ N γ w ε ∧∀ M:Tulip.Male, safeReflect M P.K.j δ N)
    (fee : E⁻¹*a⁻¹ ≤ P.h) (he:0<E)(e':E≤1)(v:Rundle.eternal Y a T)(tL:P.J.n ≤ t)
    (pδ:P.d ≤ δ)(pR:0<R)(eJ:1≤J)(pη:0≤η)(pξ:0≤ξ)(q₁:η+(ξ+ε*R) ≤ 1/3)(q₂:ξ+ε*R+(R*2)*(η+(ξ+ε*R))≤ E^3)
    (p:0<a)(tA:a≤1) (g:J*southern E a (2*R)≤ (limitO a d J)⁻¹^2*Real.exp (-(2*(Ω+1))))(f:0<Ω)
    (z:T*(4 * ((maxW+addgap (tent Y H):ℕ):ℝ))^4 ≤1)(pT:0≤T) (num:ℕ) (q:Type)[Fintype q][DecidableEq q] :
    ∀ᶠ s in atTop,∀ᶠ i:ℕ in atTop,∀ᶠ k:ℕ in atTop,(Y.voyage i).kick≤k ∧ s≤Y.uv k ∧ ∀ (L:List (Cab (Papal.count Y s i))), 0<L.length→ L.length ≤ num→ CF.Pannier.Chancel.Lantern.Service (κI i s k) P.K.j w t (gram Y s i k).p.threshold η ξ J R δ q 1 L → Huts d L →(∀ a:Axis,cows a (Resort L) maxW) →
    ‖Journey.compass Y i k s (guest L)‖ ≤ 2 * Real.exp (1-Ω) :=by
 let x(s):=hat P.R.L P.x s; let κ':ℝ:=(capDebt d a J (Ω+1) t); let K':=tent Y H; obtain ⟨N,U⟩:= Vw.exists
 have e: Tendsto (fun s:ℕ=> temp (x s)) atTop (𝓝 0):=(show Tendsto temp atTop (𝓝 0) by simpa using Work.E09.radiusB_temp 0).comp (turnover P)
 filter_upwards [e.eventually (ge_mem_nhds P.J.ht),Rundle.compass_p Y v (κ':ℝ)] with s θ h₀
 let B:= maxW + addgap K'; have hB:0<B:= Nat.add_pos_right _ addgap_pos;  -- π notation!
 filter_upwards [(count_grows Y s).eventually_ge_atTop (N+B)] with i hK
 let C:=Papal.count Y s i; let F:=Vw; let μ:= More C; let D:=sites C; let A₀:= J^((μ).val^4*num*(1:ℕ)); have hp:0<J:=zero_lt_one.trans_le eJ
 let G:=Real.exp (-Ω*D)/A₀; have hA:0<A₀:= by unfold A₀; positivity
 have w0: N+B ≤ C.val:=hK; obtain ⟨e'₁,b'⟩:=U C (by omega)
 filter_upwards [ferry_later Y s i, thaw_plot Y G (by unfold G; positivity) s] with k S φ
 refine ⟨S.depth,S.enters,fun L pL Ln h zU q'=>?_⟩; let M':=κI i s k; let X₀:=Journey.compass Y i k s; let Y₀:= solder Y i k S.depth s
 obtain ⟨V',T',eT,eV,t',eL,vT,hT,k'⟩:= CF.Pannier.Chancel.Attic.replicate (B:=maxW) (tender_g Y H s i k S) (b' M') (terrain Y H (Y.ir i) s).symm (show B ≤ C.val from by omega) L h zU q'
 let y:=Papal.gram Y s i k
 have ht:y.p.threshold=temp (x s):=((congrArg BudgetPoint.threshold (prices_plot Y s i k S.enters).1).trans (Y.meter.boot s).1)
 have hv':(T':ℝ)≤ D:= by unfold D sites; exact_mod_cast vT
 let tW:= -(Ω+1)*(V'.length:ℝ); let ht':ℝ:=Real.exp (-Ω*T'); have gT:‖X₀ (guest V')‖ ≤ Real.exp (-Ω*T'):=by
    have hbT:Rundle.IcyBudget Y a tW s i k κ' (guest V'):=by
       intro x'; let U:=room Y s i x'; have e₁:= safety Y s i k x'; let F':= guest V'; let B:=changeM P.U U M'; let C':=tiltLoan (mateK C) (spar P.K.j M' U) a; have hc': C'=Real.exp (Rous.logo a P.K.j M' U):=Dais.Parity.powerR e₁.1 p tA
       have hb:CF.Pannier.Damask.Yep (E⁻¹*a⁻¹) (acts (star ((guest V') (x'.1,U))) (mateK C)) B (Real.exp (tW+κ'*flakes y.p.threshold x'.1)*C'):= poolTilt P.J.k P.J.n eT eV e'₁ (roofage Y i s) (ht.trans_le θ) tL pδ pR eJ E a he e' p tA q₁ q₂ pη pξ (Ω+1) (by positivity) g x' _ _ e₁.1 e₁.2 (touchP C ▸ tickB C)
       rw [hc',← Real.exp_add,show tW+_ +_=tW+Rous.logo a P.K.j M' U+κ'* flakes y.p.threshold x'.1 from add_right_comm ..] at hb; intro p'; refine (hb p').trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (show 0≤E⁻¹*a⁻¹ by positivity) fee p'.length) (Real.exp_pos _).le) -- tune
    have hv:T' ≤ V'.length:= eL.symm ▸ Nat.le_mul_of_pos_right _ pL; have hW: D ≤ T' * ( (4:ℝ)* ↑B)^4:= by unfold D sites; exact_mod_cast hT
    refine (h₀ i k S.enters S.depth tW _ (eT.permit (subset_refl _)).env hbT).trans (Real.exp_le_exp_of_le ?_); change _+ (-(Ω+1)*(V'.length:ℝ))≤_; have hpp:T*(4* (B:ℝ))^4 ≤ 1 := z; nlinarith only [mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hv) (show 0 ≤ Ω+1 by positivity),mul_le_mul_of_nonneg_left hW pT,mul_le_mul_of_nonneg_right hpp (Nat.cast_nonneg (α:=ℝ) T')] -- tW syntax
 have bL:‖X₀ (guest V')-Y₀ (guest V')‖≤Real.exp (-Ω*D):= ((φ i S.depth (guest V') A₀ (eT.permit (subset_refl _)).env (fun x=> (eT.guests_v x hp.le).trans (pow_le_pow_right₀ eJ (Nat.mul_le_mul_right 1 (le_trans eL.le (Nat.mul_le_mul vT Ln))))))).trans_eq (div_mul_cancel₀ _ hA.ne')
 have hv:(T':ℝ)≤ D:= by unfold D sites; exact_mod_cast vT
 let V':=guest L
 have he:‖Y₀ V'‖≤ Real.exp (1-Ω):= small_after _ _ _ _ _ _ f le_rfl t' gT (bL.trans (Real.exp_le_exp_of_le (by nlinarith : -Ω*D≤ -Ω * T'))) k'
 have hp0 : L.length ≤ μ.val^4*num:= Ln.trans (Nat.le_mul_of_pos_left _ (pow_pos μ.property _))
 have hT :‖X₀ V'-Y₀ V'‖≤ Real.exp (-Ω*D):= ((φ i S.depth V' A₀ (h.permit (subset_refl _)).env (fun x=>(h.guests_v x hp.le).trans (pow_le_pow_right₀ eJ (Nat.mul_le_mul_right _ hp0))))).trans_eq (div_mul_cancel₀ _ hA.ne')
 have hd:1 ≤ D:= sites_pos _; apply (norm_le_norm_sub_add _ (Y₀ V')).trans; refine (add_le_add (hT.trans ?_) he).trans (le_of_eq (by ring)); apply Real.exp_monotone; nlinarith
end Convent
end Papal
end LocalLimit
end Rate
end YM.CF.Py
open YM.CF.Py.Rate.LocalLimit.Papal.Convent

#print axioms AtticPrice

