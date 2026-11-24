import YM.SU5.Selected.Lantern.Therm
import YM.SU5.Selected.Lantern.Petrol

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
open CF.Pannier.Chancel.Lantern.Tender
open Airy (TideFrame Frame Coast Wq)
open Buffered (r₃) -- check
#print r₃
#check Aliases.finite_brix
#print Patch
def capitalW (Ω:ℝ)(W:ℝ)(K:ℝ)(A:ℝ): ℝ:= max (0:ℝ) (Ω+W+K+A+1)
def imperial (Ω:ℝ)(U:Supplier): Supplier:= fun K p X V B d T W M J l Z=>
    let A:= capitalW Ω (sealPrice V W) (blossom K) Z
    let ℓ:=4*r₃ p.L ((Aliases.finite_brix K.j p.L p.odd_side).choose) (Journey.distanceLaw l) p.J+1
    let E:=(Tender.curtain p.L A (2*(ℓ+4*B.val)) p.coarse).choose -- name
    max (U K p X V B d T W M J l Z) E⁻¹
private theorem funds (Ω:ℝ)(Z:ℝ)(U:Supplier)(g:decorate (imperial Ω U) P l Z≤ P.h): decorate U P l Z≤ P.h ∧ ∃ E≤P.h,Curtain P.R.L (capitalW Ω (sealPrice P.V P.W) (blossom P.K) Z) (addgap (tent Y H)) E⁻¹:=
  ⟨le_trans (le_max_left ..) g, (by
    let X:=(Tender.curtain P.R.L (capitalW Ω (sealPrice P.V P.W) (blossom P.K) Z) (addgap (tent Y H)) P.R.coarse)
    let E:=(Tender.curtain P.R.L (capitalW Ω (sealPrice P.V P.W) (blossom P.K) Z) (addgap (tent Y H)) P.R.coarse).choose
    exact ⟨E⁻¹,le_trans (le_max_right ..) g, (inv_inv E).symm ▸ (Tender.curtain _ _ _ P.R.coarse).choose_spec⟩)⟩
-- Winter calibrated margin simultaneously. δ not smaller than working P.d.
theorem exploring : ∃ δ>(0:ℝ),∀ ε>(0:ℝ), ∃ γ>(0:ℝ),∃ w:ℕ,∀ᶠ k:ℕ in atTop,∀ N:Side,k≤N.val→ Winter 4 δ N γ w ε ∧ ∀ M:Tulip.Male,safeReflect M 4 δ N := by
 obtain ⟨e,t,k,p⟩:= safe_reflect 4 (by decide : 1 ≤ 4); obtain ⟨e',v,h,r⟩:= winter 4 (by decide); refine ⟨min e e',lt_min t v,fun ε w=>?_⟩; obtain ⟨γ,p₀,l,f⟩:=r ε w; refine ⟨γ,p₀,l,?_⟩; filter_upwards [eventually_ge_atTop (k+h)] with k' g n v; refine ⟨?_,fun M=> safe_reflect_smaller (p n (by omega) M) (min_le_left ..)⟩; obtain ⟨x,y⟩:= f n (by omega); exact ⟨fun b M X u=>x _ _ _ (u.shrink (min_le_right ..)),fun b M L X Y p u=> y _ _ _ _ _ (p.shrink (min_le_right ..)) (u.shrink (min_le_right ..))⟩
-- CP5: refine guard *before* commission to include gauge covariance of spar on every marked input. Not claiming identity of `Season.Collaboration_CP4` arbitrary witness with any CP4-snapshot-version one, not substituting histories. Calling that same augment-supplier with smaller margin & licenses.lean now banks this also.
private lemma enter_G : ∃ δ>(0:ℝ), ∀ᶠ k:ℕ in atTop,∀ N:Side,k ≤ N.val → ∀ M:Tulip.Male, Brace.Sparkle N δ M 4:=by
 obtain ⟨δ,w,k,h⟩:= Brace.drift_l 4 (by decide); exact ⟨δ,w,(eventually_ge_atTop k).mono (fun i v N p=>h _ (le_trans v p))⟩
def austere:ℝ:= min exploring.choose enter_G.choose
lemma aust_p:0<austere:= lt_min exploring.choose_spec.1 enter_G.choose_spec.1
lemma aust_g : ∀ᶠ k:ℕ in atTop,∀ N:Side,k ≤ N.val → ∀ M:Tulip.Male, Brace.Sparkle N austere M 4:=enter_G.choose_spec.2.mono (fun k p N h M=>(p N h M).red (min_le_right ..))
lemma extols (ε : ℝ)(p:0<ε) : ∃ γ>(0:ℝ),∃ w:ℕ,∀ᶠ k:ℕ in atTop,∀ N:Side,k≤N.val→ Winter 4 austere N γ w ε ∧ ∀ M:Tulip.Male,safeReflect M 4 austere N:=by
 obtain ⟨γ,t,w,h⟩:= exploring.choose_spec.2 ε p; refine ⟨γ,t,w,?_⟩; filter_upwards [h] with n e N k; obtain ⟨⟨x,y⟩,v⟩:= e N k; have ht:austere ≤exploring.choose:= min_le_left ..; exact ⟨⟨fun b M X u=> x _ _ _ (u.shrink ht),fun b M L X Y p q=> y _ _ _ _ _ (p.shrink ht) (q.shrink ht)⟩,fun M=> safe_reflect_smaller (v M) ht⟩
variable (Ω A:ℝ)
-- output posture. Use exact displays. combine with ticket eventual for known P numerics.
abbrev Poll (N:Side)(D G:Side) := D.val∣N.val ∧ G.val∣N.val
local notation "Weather" => CF.Pannier.Chancel.Lantern.Service
structure Stow (G:Side)(b u w:ℕ)(X Z: Coast → Wq (10*u))(R C E:ℝ)(v:ℕ)(γ:ℝ): Prop where
 older: G=P.R.L^ (2:ℕ)
 gapX : G.val≥8
 count : 0<u
 age: Tender.nudge (addgap (tent Y H)) + 2*Airy.harbor (Tender.nudge (addgap (tent Y H))) (10*u)+100*addgap (tent Y H) ≤ (fundD P.R.L b).val
 earnings : P.d ≤ austere
 warmth : R=10000*C^ (4:ℕ)
 estate : E=clouds (fundD P.R.L b)
 heated : E⁻¹ ≤ P.h
 price : 1 ≤ C
 band : TideFrame (G:=G) (Tender.nudge (addgap (tent Y H))) (10*u) X Z (fundD P.R.L b) w (tightH (fundD P.R.L b) R) (tightH (fundD P.R.L b) R) C
 grounds : 0<γ
 weather : ∀ᶠ k:ℕ in atTop,∀ N:Side,k ≤ N.val → Winter P.K.j austere N γ v (tightH (fundD P.R.L b) R) ∧∀ M:Tulip.Male,safeReflect M P.K.j austere N
 cashOut (q num t:ℕ)(hh:0<q)(pg:addgap (tent Y H) ≤ widthK G (fundD P.R.L b) q)(tL:P.J.n ≤ t): ∀ (K:Type) [Fintype K] [DecidableEq K],
    let D:= fundD P.R.L b; let r:=powerK G D u q
    let J:= CF.Pannier.Chancel.Lantern.Station.tollK (dueW R)
    let η:= levyH D R
    ∀ᶠ s in atTop,∀ᶠ i:ℕ in atTop,∀ᶠ k:ℕ in atTop,
       Tapestry.Pay Y s i k ∧ Poll (SN i s) D G ∧
       (∀ {V:Type}[Fintype V][DecidableEq V](x: V→Site (SN i s)× Fin (10*u)), Airy.Beacons G D (10*u) x→
       let F':= Airy.hire (10*u) X x; let V':= Airy.hire (10*u) Z x; ‖F'‖≤C∧‖V'‖≤C∧‖F'ᴴ* V'-1‖≤ tightH D R ∧ ‖(((1-Airy.tip _ (κI i s k)):Op _)* V': Matrix _ _ ℂ)‖≤ tightH D R) ∧
       ∀ L:List (Cab (SN i s)), 0<L.length→ L.length ≤ num→ Weather (κI i s k) P.K.j v t (gram Y s i k).p.threshold η η J R austere K r L → (∀ i:Axis, cows i (Resort L) (widthK G D q)) → ‖Journey.compass Y i k s (guest L)‖ ≤ 2 * Real.exp (1-Ω)

lemma event_poll (b:ℕ) : ∀ᶠ s in atTop, ∀ i:ℕ, Poll (SN i s) (fundD P.R.L b) (P.R.L^ (2:ℕ)):=by
 filter_upwards [eventually_ge_atTop (b+2)] with s p i
 let a:=P.R.L; let F:=Y.ir i; have h(t:ℕ)(p:t≤ s) : a.val^t ∣ (SN i s).val:=by
    change _ ∣ F.val* (a.val^s)*2*P.block.val; exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left (pow_dvd_pow _ p) _) _) _ -- syntax
 exact ⟨h b (by omega),h 2 (by omega)⟩
#print Stow.mk
#print Poll
lemma licenses {A:ℝ}(ht: 0<Ω)(U: Supplier)(q:decorate (imperial Ω U) P l A ≤ P.h)(d:P.d ≤ austere)(t: Inflation A P) :
    decorate U P l A≤ P.h ∧ ∃ (G:Side)(b u w:ℕ)(X Z: Coast → Wq (10*u))(R C E:ℝ)(v:ℕ)(γ:ℝ),Stow Y H Ω G b u w X Z R C E v γ :=by
 let T:= capitalW Ω (sealPrice P.V P.W) (blossom P.K) A
 obtain ⟨hp,e,hp',⟨G,b,u,w,r,t',C,pC,g,q₁,d₁,v₁,X,Z,F⟩⟩:=funds Y H Ω A U q -- tune tuple
 let D:=fundD P.R.L b; let R:= 10000*C^ (4:ℕ); let J:=CF.Pannier.Chancel.Lantern.Station.tollK (dueW R); let η:=tightH D R; let η':=levyH D R; have hR:1≤R:= one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ pC); have hR':0<R:=zero_lt_one.trans_le hR
 obtain ⟨γ,hγ,v,p⟩:= extols η (mugs hR D); have pp: ∀ᶠ k:ℕ in atTop,∀ N:Side,k ≤ N.val → Winter P.K.j austere N γ v η ∧∀ M:Tulip.Male,safeReflect M P.K.j austere N:= by rw [P.kJ]; exact p
 have hf:(clouds D)⁻¹ ≤ P.h:= by change e⁻¹=clouds D at d₁; rwa [←d₁,inv_inv]
 have hu:0<u:=t' ▸ folred ..; have hp0:0≤ η':=by have he:0<clouds D:=(cloudsK ..).1; unfold η' levyH; positivity
 refine ⟨hp,G,b,u,w,X,Z, R,C,clouds D,v,γ,⟨r.symm,g,hu,q₁,d,rfl,rfl,hf,pC,F.havens,hγ,pp,?_⟩⟩
 intro Q num t_ a x v A' _ _; let r₀:=powerK G D u Q; have hT:rentL D * ((r₀:ℝ)/((4:ℝ)*↑(widthK G D Q+addgap (tent Y H)))^ (4:ℕ)) ≥ T:= by unfold r₀; rw [t']; exact effort G D T Q _ a x
 have hy: sealPrice P.V P.W - T+blossom P.K+(A+1) ≤ -Ω:=by linarith [show _ ≤ T from le_max_right (0:ℝ) _] -- tune
 obtain ⟨M,k⟩:= Airy.mtn_out _ F.ticket
 have hk(s):= backs Y s M
 have he:= loomPrice (J:=J) Y H pp hf (cloudsK ..).1 (cloudsK ..).2 t v d hR' (toll_pos hR'.le) hp0 hp0 (mill hR D).1 (mill hR D).2 (show r₀>0 by unfold r₀ powerK; positivity) (show 0≤rentL D by unfold rentL; positivity) v₁ ht hT hy num A' -- ⚠ v shadow
 filter_upwards [he,event_poll Y b] with s t u'
 filter_upwards [t] with i m
 filter_upwards [m,hk s] with j h v; refine ⟨⟨h.1,h.2.1⟩, r ▸ u' i,fun {Q'} _ _ x z=> k _ (v i) _ _ z,h.2.2⟩ -- tune cast `v` and q shadow
end Mileage
end Papal
end LocalLimit
end Rate
end YM.CF.Py
open YM.CF.Py.Rate.LocalLimit.Papal.Mileage
#print axioms licenses
