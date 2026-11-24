import YM.SU5.SatinWard.Resolution.Baffle
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 700000
set_option maxRecDepth 8000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
open MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
open Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
open scoped ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
open Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus QuadClock Ione Vow Swell
open _root_.Zephyr.Chern
universe uΩ


open Papal CF.Papyrus.Franc.SatinForce CF.Pannier.Chancel Checkers

open CF.Papyrus.Franc.Loaves
-- CP3 package. PUBLIC, no topology/order changes
open Moon
open Horizons FoliageP BareProgram Moonlit Moonlit.SwitchC
open _root_.YM.Regis.Head.Brecht _root_.YM.Regis.Circuit _root_.YM.Regis.Circuit.SpringDay
open SlabMark VelourBoard Papal.SkyTax Cygnet VelourWiggle
open YM.Stationary (Gaia)
open SwitchC.Garland SwitchC.Garland.Terrace SwitchC.Garland.Terrace.Juniper
open Abacus CheckerFlag SlopeCharge Maxwell
open scoped RealInnerProductSpace ContDiff
namespace Fame
open BProof Pressure
namespace Regulator

open _root_.YM.Gleam.Luster.Almanac Grade
open Papal.SkyTax
open _root_.YM.Regis.Head
open _root_.YM.Gleam.Luster.Almanac Grade
open _root_.YM.CF.Py.Rate.LocalLimit.Preparation _root_.YM.CF.Py.Rate.LocalLimit.Preparation.Tabletop Shrine Ione.Clock Moto
variable (P:Spine)
local notation "W★"=>P.calibration
local notation "Ω★"=>P.run.meter
open Preparation.Yoke Spine.Gingham Spine.Gingham.Diary
open ShapeLab ResolutionFrame Shrine 
open SatinWard
local notation "R"=> Option Tilted.Ramp
local notation "T"=> P.calibration
local notation "ι₀"=>Wage4
local notation "L"=> P.par.R.L
local notation "V"=> P.large
variable (X:R)
variable {s v g w:ℕ}(p:Cover)(e:Almanac P s w p)(h:s≤g)
variable {f0:ℕ} {Z:ℕ→ℕ} {η:Type}[Fintype η]{C H A:ℝ}
variable (pZ:Tendsto Z atTop atTop)(W:Calendrical P C H A f0 η Z){Wq:Bool→ Coords Wage4} {Uq:ℕ→ Bool→ Coords Wage4} {F:ℕ→ℕ}(WX:CriticalClock P C H A g f0 η Wq F Z Uq) (b: Bool)
include pZ W WX h
local notation "Yt" => (sprintCost L)
local notation "k▶" i:max => P.engine ((Z ∘F) i)
local notation "j▶" i:max => P.nomadic ((Z ∘ F) i)
omit W WX pZ h
open Worth Pays BProof Aria Casting MacroGrid
open Selected
local notation "ζ"=>P.sidesPerTick
-- Annotated center. translate with the REAL home clock (not simplified half). Pose Hc later.
variable (M:P.par.R.L.val %16 =1) (k:P.NightCop) (j:Axis)(x:P.Spectrum0 j)
variable {a: Cover} (qa:ResidualPermit a) (y:Coords Wage4) (q:payable P v 2) {u d:ℝ}
variable (f:ℕ)(g₀:f ≤ v)
local notation "τ" i:max=> P.macroStep i
local notation "W₀" => choirWidth P
variable (ρ:Piano P f0 C H A η Z)
variable {C' d' μ Q:ℝ} {t' β Wp} {R':P.Register} (T₁:CouncilGrant P R' d' C' t' Z Wp β) (H': PublicKernel P Z Wp)
local notation "Ψ" i:max=> tollηw P β i
local notation "ℓ" i:max=> moonClock P i
local notation "fρ" i:max=> corridorHeight P i
local notation "R♛" i:max=> corridorR P i
local notation "M♛" i:max=> (R♛ i:ℝ)
local notation "ζ₁" i:max=> (↑(Ψ i):ℂ)
open OS.Semigroup OS.Semigroup.Marble PSE MarbleFace
variable (c:Cover) (t:P.Apron)
-- pre-cost any minted clover sales of fixed height and budget. annotations where needed.
open CF.Onyx (moor moor_z)
local notation "Wₗ"=> (↑W₀:ℝ)*τ v
local notation "q◁"=> ℓ (fρ v)
local notation "μ✩"=> R♛ v
local notation "𝔅"=> (↑(Ψ v):ℂ)
local notation "𝓓"=> (↑(μ✩):ℂ)
local notation "𝒦"=> (Ψ v)
local notation "Υ"=> P.charter j x
local notation "Iₐ"=> P.ColorHil j x
local notation "ξ"=> P.physicalEnergy j x
local notation "ω₁"=> P.colorZero j x
local notation "△"=> quietArm (P.colorZero j x)
private abbrev folded:= (plane j 0).motion c
variable (sT:Stamped P v q c t)
-- immutable.
noncomputable abbrev altitude (i:Cover):= geoAt P v i
lemma stamp_meager {m:Cover}(c':|m j| ≤(ζ:ℤ)): |geoAt P v m j| ≤ τ v:=by
 rw [←macroUnit P v]; change |(m j:ℝ)*_|≤ _; rw [abs_mul,abs_of_nonneg (gaugeMesh_pos ..).le,← Int.cast_abs]; apply mul_le_mul_of_nonneg_right _ (gaugeMesh_pos ..).le; exact_mod_cast c'
noncomputable abbrev loomDay (d: Vantage)(u:ℝ):Gaia:= moor (u⁻¹ • d)
lemma scale_corridor : 0< R♛ v ∧ q◁=(R♛ v)*gaugeMesh P.par v:= ⟨div_pos (clockP ..) (gaugeMesh_pos ..), (div_mul_cancel₀ _ (gaugeMesh_pos ..).ne').symm⟩
lemma geoB (x y:Cover): loomDay (geoAt P v x-geoAt P v y) (q◁) = patchF (x-y) (R♛ v):=by
 let R':=R♛ v; let ℓ':=q◁; have hh:=scale_corridor P (v:=v); let c:= gaugeMesh P.par v; have ht: 0<c:= gaugeMesh_pos _ _
 ext i; change ℓ'⁻¹*((x i:ℝ)*c-(y i:ℝ)*c)=R'⁻¹* (↑(x i-y i):ℝ); rw [show ℓ'=R'*c from hh.2]; have h:0<R':=hh.1; push_cast; field_simp
lemma loom_upper (v:ℝ)(d:Vantage): ‖loomDay d v‖ ≤ 2*‖v⁻¹ • d‖:= moor_z _
lemma loom_lower (v:ℝ)(d:Vantage): |(v:ℝ)⁻¹*d j| ≤ ‖loomDay d v‖:=by apply (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp; rw [EuclideanSpace.norm_sq_eq]; exact single_le_sum («f»:=fun i=> (‖(loomDay d v).ofLp i‖)^2) (fun i _=>sq_nonneg _) (mem_univ j)
lemma tick_s (x₀:Cover)(e:∀ i≠j,x₀ i=0)(D:(Iₐ).Op) : P.charter j x (P.vtile v x₀) D=D:=by
 refine (P.charter_same _ _ (q:=0) (fun i p=>?_) _).trans (P.charter_zero ..); apply Subtype.ext; change P.tock v (x₀ i)=0; rw [e i p,P.tock_zero]
-- charges at ± 4*ℓ f on actual positions. hence arms bound ≤C/R^4 at pads (l,r≥10ℓ, etc, both). use broad c=0.. height. keep gauge annotation inside. 
local notation "r₀"=> (P.reachLeaf (fρ v) v (moonSpan P (fρ v)))
private noncomputable def leadWait (P:Spine)(j:Axis)(v:ℕ):Cover:= Pi.single j (4*((P.reachLeaf (corridorHeight P v) v (moonSpan P (corridorHeight P v))):ℤ))
local notation "o"=> leadWait P j v
private noncomputable abbrev tScore (i:Bool):= if i then leadWait P j v else -(leadWait P j v) -- keep field
lemma leadVal(i:Axis): P.laysM (P.vtile v o) i= if i=j then 4*q◁ else 0:=by
 change P.tock v (o i) =_; by_cases d:i=j
 · let r:=fρ v; have e: P.tock v r₀=q◁:= (extending_clock P (Nat.sub_le ..)).trans (by rw [P.tock_price]; push_cast; rfl); rw [if_pos d]; unfold leadWait; rw [d,Pi.single_eq_same, P.tock_price]; rw [P.tock_price] at e; push_cast at *; rw [←e]; ring
 rw [if_neg d]; unfold leadWait; rw [Pi.single_eq_of_ne d,P.tock_zero]
private noncomputable abbrev markP(i:Bool):= (if i then c else folded j c)+ P.sidesPerTick • tScore P j (v:=v) i
variable (Φs:StockedR P f0 v μ η Z C H A β)(hμ:0≤ μ) (Q':20 ≤ Q)
-- shadow F above {F:..}. include
include sT ρ Φs hμ Q'
local notation "δ"=> geoAt P v (markP P (v:=v) j c false)-geoAt P v (markP P (v:=v) j c true)
-- markP implicit v parameter explicit? proof compiles after inspect. time ∈[±(8±2)ℓ].
private lemma loom_credit : Addressing (markP P (v:=v) j c false) (markP P (v:=v) j c true) (loomDay δ q◁) μ (R♛ v) Q:=by
 let Z:= markP P (v:=v) j c; let h:0< q◁:=clockP P _; let d:=loomDay δ q◁; let k:=geoAt P v; have u(i:Axis): δ i= if i=j then -2*k c j -8*q◁ else 0:=by
    unfold markP tScore; simp only [↓reduceIte,Bool.false_eq_true]; rw [geo_pose,geo_pose,vtNeg,lays_neg]; dsimp only [Pi.sub_apply,Pi.add_apply,Pi.neg_apply]; rw [leadVal]; by_cases e:i=j
    · subst i; simp only [if_true]; change ((↑(folded j c j):ℝ)*_) + _- (k c j+_)= _; unfold folded; rw [fling_move,if_pos rfl,mul_zero, add_zero,Int.cast_neg, neg_mul]; change -(k c j)+_ - (k c j+_)=_; ring
    rw [if_neg e]; change ((↑(folded j c i):ℝ)*_)+_-(k c i+_) = _; unfold folded; rw [fling_move,if_neg (Ne.symm e),neg_zero,add_zero,add_zero]
    rw [if_neg e]; exact sub_self (k c i)
 have hp:|k c j| ≤ q◁:=by
    apply (stamp_meager P j (v:=v) (m:=c) (sT.fare _).2).trans
    let g:=Φs.money.1.trans Φs.money.2.le; refine le_trans ?_ (loans_le P ρ Φs.money.1 Φs.money.2.le); have u:=windowLaw P ρ g; have hm:0 ≤ Wₗ:= mul_nonneg (by positivity) (P.macroStep_pos v).le; linarith
 have hV :6*q◁ ≤ -(δ j) ∧ -(δ j) ≤10*q◁:=by rw [u, if_pos rfl]; rw [abs_le] at hp; constructor<;> linarith only [hp.1,hp.2]
 have he:=loom_lower j (q◁) δ; have hδ:(δ j) ≤ 0:=by linarith only [hV.1,h]
 have hf: |(q◁)⁻¹*δ j|= (-δ j)/(q◁):=by rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by positivity) hδ),div_eq_mul_inv,neg_mul, mul_comm]
 refine ⟨hμ,Φs.magnify.1,?_,?_,?_⟩
 · rw [hf] at he; exact le_trans ((le_div_iff₀ h).2 (by linarith only [hV.1,h])) he
 · apply le_trans (loom_upper ..); refine le_trans ?_ Q'; have hq:‖(q◁)⁻¹ • δ‖≤10:=by
      apply (pi_norm_le_iff_of_nonneg (by norm_num)).2; intro i; change |(q◁)⁻¹*δ i| ≤ 10; by_cases e:i=j; · rw [e,hf]; exact (div_le_iff₀ h).2 hV.2
      rw [u,if_neg e]; norm_num
   linarith
 rw [geoB,sub_self,norm_zero]; exact div_nonneg hμ (scale_corridor P).1.le
local notation "D"=> t.kiss P j
local notation "T₀★"=> t.realWidth P j
local notation "G₀"=> t.engine P j x
local notation "r₁"=>4*(q◁)
variable {U:ℝ}(uBank:WickBank P β v U μ Q)
include uBank T₁
lemma pay_arm : let r:=4*(q◁); let A:=(ξ).sand G₀ (r-T₀★) (r-T₀★)
 (μ✩)^4* ‖△ (𝔅⁻¹ • A)‖≤ Real.sqrt (2*U):=by
 intro r Iβ; let Aa(i:Bool):P.Apron:= if i then t else D; let N:= tScore P (v:=v) j; let A(i:Bool):= if i then c else folded j c; let t'(i:Bool) :=P.vtile v (N i)
 have h: 0< r:=mul_pos (by norm_num) (clockP ..); have hX:T₀★ < r:=by rw [stamp_width P j q c t sT]; have hb:=windowLaw P ρ (Φs.money.1.trans Φs.money.2.le); let l':=loans_le P ρ Φs.money.1 Φs.money.2.le; unfold r; linarith only [hb,l', P.macroStep_pos v,clockP P (fρ v)]
 have hn:t' true=P.vtile v o:=rfl; have hz:P.vtile v (-o)=t' false:=rfl; have hx':P.laysM (P.vtile v o) j=r := by rw [leadVal,if_pos rfl]
 have hq:P.resignY j Aa (P.laysM ∘ t') false = -r+T₀★:=by unfold resignY Apron.time_edge; rw [Function.comp_apply, ←hz, vtNeg, P.lays_neg,Pi.neg_apply,hx']; rfl
 have hp:P.porchY j Aa (P.laysM ∘ t') true=r-T₀★:=by unfold porchY Apron.time_panel; rw [Function.comp_apply,hn,hx']; rfl
 have hm : P.Turnstile j Aa [false,true] (P.laysM ∘ t'):= List.pairwise_pair.mpr (by rw [hq,hp]; linarith)
 have he:=bank_use P j x q ρ T₁ uBank false Aa A N (fun i=> by cases i; exact Stamped.kissed P j q c t sT; exact sT) (Φs.money.1.trans Φs.money.2.le) (loomDay δ q◁) (loom_credit P j q ρ c t sT Φs hμ Q') hm -- syntax
 let p:=preMosaic P j x Aa false t'; have hu:p= Marble.seam (ξ) (ω₁) 0 (star Iβ) Iβ:=by
    let l:= r-T₀★; have u':0≤l:= sub_nonneg.mpr hX.le; let k:= tick_s P j x (v:=v) o (by intro i p; unfold leadWait; rw [Pi.single_eq_of_ne p]); let v':= tick_s P j x (v:=v) (-o) (by intro i p; unfold leadWait; rw [Pi.neg_apply, Pi.single_eq_of_ne p,neg_zero]); let Y':= anchor_pre P j x Aa false t' 0 l l l l le_rfl u' u' (by change l+0+l=P.porchY j Aa _ true-P.resignY j Aa _ false; rw [hq,hp]; unfold l; abel)
    unfold p; rw [Y']; change Marble.seam _ _ _ ((ξ).sand (Υ _ ((D).engine P j x)) l l) ((ξ).sand (Υ _ G₀) l l) = _; rw [←hz, show (!false)=true from rfl,hn,k,v']; refine congrArg₂ (Marble.seam (ξ) (ω₁) 0) ?_ rfl; -- `(D).peer ...` 
    unfold Iβ; rw [OS.Semigroup.sand_star,← t.peer P j x] -- sand_star namespace
 let Q₀:=corridorR P v; have hη:0<𝒦:= tollηw_p P ρ T₁ (Φs.money.1.trans Φs.money.2.le)
 have hB:0 < R♛ v:=(scale_corridor P).1
 let S:= 𝔅⁻¹ • Iβ; let ht:‖(𝓓^8:ℂ)*(𝔅^2:ℂ)⁻¹ * p‖ ≤2*U:= (norm_le_norm_sub_add ..).trans ((add_le_add (he.amount.trans (div_le_self he.nn Φs.magnify.2.1)) he.shadow).trans_eq (two_mul ..).symm)
 have hη' : p=(𝔅)^2 * Marble.seam (ξ) (ω₁) 0 (star S) S:=by
    rw [hu]
    let Q':= Iβ; have h':Q'=𝔅 • S:= (smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr hη.ne') _).symm
    change Marble.seam _ _ _ (star Q') Q'= _; rw [h',star_smul, Marble.seam_smul, Marble.seam_smul_right]; rw [show star (𝔅)=(𝔅) from by simp]; ring -- rw loop when S definally?
 have heq:= pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hη.ne')
 rw [hη',mul_assoc,inv_mul_cancel_left₀ heq, Marble.still_coin (ξ) (ω₁) (imPrev ..), norm_mul,norm_pow, Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hB.le,abs_of_nonneg (sq_nonneg _)] at ht -- star property
 refine (Real.le_sqrt (by positivity) (by have h:=uBank.positive; linarith)).mpr ?_; change ((μ✩)^4 * ‖△ S‖)^2 ≤ _; nlinarith only [ht]
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
