import GaugeFieldConstruction.AuteurS
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
open CF.Velvet CF.Pannier.Chancel Pitching.Focus
open YM.CF.Oath.BellPrice CF.Fief
open Oath
open Papal AUbard
open Papal FrameP Yoke.Promena WorldJ Frugal CF.Scroll MirrorCost
open Py Yoke.Promena
open CF.Neon CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart
open CF.TableF CF.TableF.Lenten CF.XGarden CF.XGarden.Shield
open WorldJ
open scoped YM.CF.Mew
open Pitching.Focus.CoeffArc TableF TableF.Lenten TableF.Lenten.Layout TableF.Lenten.Layout.Fren
open Ing Ing.Ivey CF.XGarden.MastTin
open CF.Pastry CF.Hive
open CF.Scroll
namespace RosterJ
variable {P:Spine}
variable {θ:BandS→ℕ}{G:ℝ}{f0:ℕ}
variable (p:RosterJ P θ G f0)
-- Bamboo table for all visits.At arrays even torus support, t Mind consumed.

local notation "ΤΓ"=> P.run
variable (B0:SωJ θ)(M:JωL θ)
namespace BoonsθJ
open JetCurry JetCurry.TrekJ ProbeθJ Yoke
variable (x:P.VMark)(R:Signed × Bool)(u:BandS)
local notation "Ξu"=> Fin (θ u)
local notation "η"=> FrameK (Fin (θ u))
variable (pu:Adept_T θ B0 M G)
-- Flexible anchor representation. stores assertion on arbitrary Movement Words.May align proofs of R3 via composition. KeyScope.S.
variable (L:finsJ)
local notation "Υs"=> ScaleμJ P.par u.val
-- CASH in force p P through procurement. preservation under Delayed (single.U)
local notation "ΚΡ"=> CalendarJ p B0 M
variable (A: CalendarJ p B0 M)
-- price limits of approximants.Any other heights at same point even with multiple gaps.N.Helper loan.
variable (T:LampHouseJ (θ:=θ) u) (D:P.Heritor)(V:LampΤJ p B0 M x R u A T D.path)
local notation "Zγ"=> FrameK (Fin (θ u))
local notation "ι" i:max=> D.path.subSeq i
local notation "gp" i:max=> P.gatePeriod (D.path.subSeq i)
local notation "gq" i:max=> P.gateCut (D.path.subSeq i)
local notation "βζ"=> FlavorRateJ P u
local notation "Κg"=> ΦWallet p
variable {f s l:ℕ}(g:f0≤ f)(s0:f0 ≤ s)
-- Portrait in all Habitat pads at Slabs.Location.Mar.K.Kernel.
local notation "νP" => RankQJ P.par
local notation "Kρ"=> p.price
local notation "gR" => RStepJ P.par
local notation "βρ" => stepRateJ P.par u.val
variable (σ τ:PermWallJ P) (i:Axis)(v:FrameK (Fin (θ u)))
open BoonsθJ Gleam BProof BProof.PricePort Gleam.Guide Gleam.clocks
open Fock.Flux
variable {d m:ℕ}
-- convergence along Rescale. Hom movement & spin. Mach anti.S. two/trio into Rank.P.R.
open CF.XGarden.MastTin.ArtCart.BluffV.Lave BluffV BluffV.Fables
open CF.Levier CF.Spire
open YM.GaugeFieldConstruction.Wick.Yacht YM.GaugeFieldConstruction.Wick YM.GaugeFieldConstruction.Cauchy
open GaugeFieldConstruction GaugeFieldConstruction.Phys Calibration Calibration.Floor
open SpaΘ
variable (Q: Py.Rate.LocalLimit.Badge)(t:ℕ)(u': TintDemand)(H: LicensedHeight (tagged_B Q) t u' P.par)
variable (m:ℕ){L:ℕ→ℕ}{a b:Genre}{d d':GaugeFieldConstruction.Calibration.Floor}{X Y:Waves}
local notation "kτ" f:max=> mount ((Richm_R P m f)⁻¹)
open Heritor Gap Raster
variable (pL:Tendsto L atTop atTop)
open SelectionAnalysis
namespace SignetS
open InterR Shower
abbrev GapS_π:=3500 -- thickness power
abbrev RibS_m:=450
section finesse
local notation "Ze"=> SpringR P
local notation "δ"=>deltaR P
-- algebra circumvent elaborating large powers.
lemma payPow_S {a b:ℕ}(h:a<b)(y:ℕ→ℝ)(k:Tendsto y atTop atTop)(p:∀ i, 0<y i) : Tendsto (fun i=> y i^a/y i^b) atTop (𝓝 0):=by
 obtain ⟨j,t⟩:= Nat.exists_eq_add_of_le h; have H:b=a+(1+j):=by omega
 refine (tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by omega:1+j≠0)).comp k)).congr ?_; intro i; change (y i^(1+j))⁻¹=_; rw[H,pow_add]; have he:=p i; field_simp; simp [pow_add]; ring
abbrev WishGap_S (P:Spine)(f:ℕ):= ((SpringR P f)^GapS_π)⁻¹
lemma Wish_posS (P:Spine)(f:ℕ):0<WishGap_S P f:=inv_pos.mpr (pow_pos (zero_lt_one.trans_le (SpringR.tall ..)) _)
lemma wish0_S (P:Spine) : Tendsto (WishGap_S P) atTop (𝓝 0):= tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by decide : GapS_π≠0)).comp (SpringR.escape ..))
local notation "QΔ"=> WishGap_S P
abbrev TideM (P:Spine)(f:ℕ):=deltaR P f*WishGap_S P f
lemma Tide_posS (P:Spine)(f:ℕ):0<TideM P f:=mul_pos (deltaR_good ..) (Wish_posS ..)
-- ratio helpers.
lemma CoverMedS {z n:ℕ}(p:n+4≤8*z+1) : ∀ᶠ f in atTop, PlethoraJ P (SportR P z f)≤deltaR P f*(SpringR P f^n)⁻¹:=by
 filter_upwards[R_squeeze P z] with f hf; let Z:= SportR P z f; let T:= SpringR P f; let L:= W_PhR P Z; have hv: 1≤ T:= SpringR.tall ..; have ht:0<T:= zero_lt_one.trans_le hv
 change PlethoraJ P Z≤ δ f*(T^n)⁻¹; rw [R_pitch,← Richm_peck P z f, mul_assoc]; refine mul_le_mul_of_nonneg_left (hf.trans ?_) (P.mellow_good _).le
 rw [←div_eq_mul_inv]; refine (le_div_iff₀ (pow_pos ht _)).2 ?_; rw [←pow_add]; exact pow_le_pow_right₀ hv (by omega)
lemma CoverHigh_S (P:Spine): ∀ᶠ f in atTop, PlethoraJ P (SportR P RibS_m f)≤ TideM P f:=CoverMedS (by decide: GapS_π+4≤8*RibS_m+1)
lemma tickS_rate (n:ℕ)(h:n<8*m+1): Tendsto (fun i=> widthζR P (SportR P m i)/(deltaR P i*(SpringR P i^n)⁻¹)) atTop (𝓝 0):=by
 let A:=payPow_S h (SpringR P) (SpringR.escape ..) (fun i=>zero_lt_one.trans_le (SpringR.tall ..)); let B:ℝ:=ruler P.par.block; have he:=A.const_mul B; rw [mul_zero] at he; apply he.congr; intro i; let Q:=SpringR P i; change B*(Q^n/Q^_)= _/(δ i*(Q^n)⁻¹); rw [div_mul_eq_div_div, widthδR m i]; change _ = B/Q^ (8*m+1)/_; simp only[div_eq_mul_inv, inv_inv]; ring
lemma ribPlot_S (p:UpShift_S ≤ m)(n:ℕ)(h:n≤3) :∀ᶠ f in atTop,widthζR P (SportR P m f)≤ TideM P f:=by
 filter_upwards [ (tickS_rate (P:=P) m GapS_π (by have ht:GapS_π<8*UpShift_S+1:=(by decide); omega)).eventually (ge_mem_nhds (show (0:ℝ)<1 from zero_lt_one))] with f h
 exact (div_le_one (Tide_posS ..)).mp h -- tune
abbrev MedCostS:=30+40*RibS_m
lemma ΥKappa_S(y:ℕ)(x:ℕ)(q:y+GapS_π<8*m+1): Tendsto (fun i=>(x:ℝ)*((TideM P i)⁻¹*(2*widthζR P (SportR P m i)))*SpringR P i^y) atTop (𝓝 0):=by
 have h:= (tickS_rate (P:=P) m (y+GapS_π) q).const_mul ((x:ℝ)*2); rw [mul_zero] at h; refine h.congr (fun i=>?_); change _ = _ * (_ * _)*_; unfold TideM WishGap_S; simp only [pow_add,mul_inv_rev, inv_inv, div_eq_mul_inv]; ring
end finesse
section
variable {I:Type}[Fintype I][DecidableEq I]
variable (u:I→GaugeFieldConstruction.Calibration.Floor)(S:DialsBJ P θ)(V:AxonsJ p B0 M A S D) (X':I→BezelR)(R':I→ Signed × Bool)(L0:I→finsJ)(H':∀ i:I,X' i∈ PerlSetR (u i))
abbrev AroundS (P:Spine)(f:ℕ)(t:ℕ)(x:I→Axis→ℝ) : I→ Cover:= fun i j=> LfloorR P (ScaleSχ P f x i j) t
local notation "Zs"=> SportR P m
local notation "Tα"=> TideM P
local notation "Ε"=>RecessS P m
local notation "Σa" i:max x:max=> AroundS P i (SportR P m i) x
lemma WidthAroundS (x:I→Axis→ℝ)(t k:ℕ):let F:=AroundS P k (SportR P m k) x; let s:=ScaleSχ P k x; ∀ i:I,∀ j:Axis, |s i j -(AskR P (CountersS P m k F) i j)|≤ widthζR P (SportR P m k):=by
 intro F s i j; let Z:=Zs k; let y:=s i j; obtain ⟨h,p,e⟩:=minutesR (P:=P) Z y; let R (i:ℤ):ℝ:=P.stampPin Z i; change |y-R (F i j)|≤ _; change (R (F i j))≤ _ at h; rw[e] at p; rw[abs_of_nonneg (sub_nonneg.mpr h)]; exact (by linarith only [show y<R (F i j)+_ from p])
abbrev LobeS (r:ℝ)(x:I→Axis→ℝ):Prop:=∀ j:Axis,∃ l:List I, PolesR l∧ BuntR (6*r) j l x
lemma OffPlotMaskS (x:I→Axis→ℝ)(T:ℝ){L:Axis→List I}(h:∀ j, BuntR (4*T) j (L j) x)(w:∀ j, PolesR (L j))(u:0<T): x∈ MasksR I:= fun i=> char_R (And.intro (w i) (List.Pairwise.imp (fun x=> sub_pos.mp ((mul_pos (by norm_num: (0:ℝ)<4) u).trans_le x)) (h i)))
lemma ShawGap_R (f:ℕ) (x:I→ Axis→ℝ)(L:Axis→List I) (w: widthζR P (SportR P m f) ≤ TideM P f)(e:∀ i: Axis,BuntR (6*WishGap_S P f) i (L i) x): let X:=ScaleSχ P f x; let Y:=AskR P (CountersS P m f (AroundS P f (SportR P m f) x))
 ∀ i:Axis, BuntR (6*TideM P f) i (L i) X ∧ BuntR (4*TideM P f) i (L i) Y:=by
 intro X Y i; let d:=deltaR P f
 have ht:d*(6*WishGap_S P f)= 6*TideM P f:=by unfold TideM d; ring
 have m':BuntR (6*TideM P f) i (L i) X:=by rw[←ht]; exact SpinOrdersS x _ i _ _ _ (e i) (deltaR_good ..).le rfl
 exact ⟨m',BuntPatchR _ _ _ _ _ m' (fun k=> (WidthAroundS m x 0 f k i).trans w)⟩
include pL
lemma around_limS (x:I→ Axis → ℝ)(v:ℕ→I→Axis→ℝ)(p:Tendsto v atTop (𝓝 x)):Tendsto (fun i=>RecessS P m (L i) (AroundS P (L i) (SportR P m (L i)) (v i))) atTop (𝓝 x):=by
 let F(k:ℕ):= RecessS P m (L k) (AroundS P (L k) (SportR P m (L k)) (v k))
 refine tendsto_pi_nhds.mpr (fun i=>tendsto_pi_nhds.mpr fun j=>?_)
 apply tendsto_of_tendsto_of_dist (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp p i) j); refine squeeze_zero (fun _=>dist_nonneg) ?_ ((widthδR_shrinks (P:=P) m).comp pL); intro k; rw [Real.dist_eq]
 let t:= L k; let d:= deltaR P t; let P':= AroundS P t (Zs t) (v k); change |v k i j- d⁻¹*(AskR P (CountersS P m t P') i j)|≤ (widthζR P (SportR P m t))/d; rw [←div_eq_inv_mul] -- orientation!
 apply (le_div_iff₀ (deltaR_good P t)).2; rw[mul_comm]; rw [show d*|v k i j-_/d|=|ScaleSχ P t (v k) i j-AskR P (CountersS P m t P') i j| from ?_]; exact WidthAroundS m (v k) t t i j
 let X:=AskR P (CountersS P m t P') i j; let y:=v k i j; have h₁:d * (y-X/d)=d*y-X:=by field_simp [show d≠0 from (deltaR_good P t).ne'] -- ring
 change d* |y-X/d|=|d*y-X|; rw[←h₁,abs_mul,abs_of_nonneg (deltaR_good P t).le]
omit pL
abbrev Scroll_S (m:ℕ)(f:ℕ)(C:CoinsR P)(x:DiagramR I):ℂ:=SπR C.porch (TapeI p B0 M pu A D m u S V X' R' L0 f) (ScaleSχ P f x)
include H H'
variable (q:UpShift_S ≤ m)(e:Fintype.card I≤ 3)
include q p e
lemma AcrossRealS :∀ ε>0,∀ᶠ f in atTop, ∀ x:I→Axis→ℝ, LobeS (WishGap_S P f) x → let F:= TapeI p B0 M pu A D m u S V X' R' L0 f; let Y:=AskR P (CountersS P m f (AroundS P f (SportR P m f) x)); Y∈ MasksR I∧∀ C:CoinsR P, ‖SπR C.porch F (ScaleSχ P f x)- SπR C.porch F Y‖<ε :=by
 let n:=Fintype.card I; let mP:= MedCostS
 have hx:= ΥKappa_S (P:=P) m (MedCostS*n) n (by
    have he:MedCostS*3+GapS_π<8*UpShift_S+1:=(by decide); have hd:=Nat.mul_le_mul_left MedCostS e; change _*Fintype.card I+_<_; omega)
 let T:= fun i=> (n:ℝ)*((TideM P i)⁻¹*(2*widthζR P (SportR P m i)))*SpringR P i^(mP*n)
 have h':Tendsto (fun i=> 4*T i) atTop (𝓝 0):=by simpa only[mul_zero] using hx.const_mul (4:ℝ)
 have hp(i:I):=SpendS_R p B0 M (R' i) pu A D Q t u' H m S V (u i) (L0 i) (X' i) (H' i) (le_trans (by decide: 26 ≤ UpShift_S) q) RibS_m (by decide)
 intro ε h
 filter_upwards[(ribPlot_S (P:=P) m q n e),CoverHigh_S P,eventually_all.mpr hp,h'.eventually (gt_mem_nhds h),eventually_ge_atTop f0] with f w c hs H e x hx
 intro F Y; choose L g v using hx
 let Q':= ShawGap_R m f x L w v; let r:= SportR P RibS_m f; let σ:I→PermWallJ P:=fun _=>AutoPadR P r; let d:=widthζR P (SportR P m f); let B:=SpringR P f^MedCostS; let R':=TideM P f
 refine ⟨OffPlotMaskS Y _ (fun i=>(Q' i).2) g (Tide_posS ..),fun C=>?_⟩
 refine lt_of_le_of_lt (AllJigR C.porch σ (ScaleSχ P f x) Y R' B d F (fun i=> AttS_R ..) L (fun i => (Q' i).1) g (fun _=> c) (fun i j=>hs i (σ i) j r (e.trans (SportR.hop ..)) le_rfl le_rfl) (WidthAroundS m x 0 f) (Tide_posS ..) (widthζR_pos ..).le w (pow_nonneg (zero_le_one.trans (SpringR.tall ..)) _)) ?_
 rw [show B^Fintype.card I=SpringR P f^(mP*n) from (pow_mul ..).symm]; exact H
variable (W:DiagramR I→ℂ) (w:GridPriceS p B0 M pu A D u S V X' R' L0 m W)
include w pL
lemma PantallaS (v:ℕ→I→ Axis→ℝ)(x:DiagramR I)(y:Tendsto v atTop (𝓝 x))(p':x∈ CardsR I)(e':∀ᶠ i in atTop,LobeS (WishGap_S P (L i)) (v i))(C:ℕ→ CoinsR P): Tendsto (fun i=> Scroll_S p B0 M pu A D u S V X' R' L0 m (L i) (C i) (v i)) atTop (𝓝 (W x)) :=by
 let A'(i:ℕ):= AroundS P (L i) (SportR P m (L i)) (v i)
 let F(i:ℕ):= TapeI p B0 M pu A D m u S V X' R' L0 (L i); let P'(i:ℕ):= SπR (C i).porch (F i); let T (i:ℕ):= AskR P (CountersS P m (L i) (A' i)); let Z(i:ℕ):=ScaleSχ P (L i) (v i)
 have he:=AcrossRealS p B0 M pu A D Q t u' H m u S V X' R' L0 H' q e; have hh:Tendsto (fun i=>P' i (T i)) atTop _:= w C L pL x A' (around_limS m pL x v y) p' ((e'.and (pL.eventually (he 1 zero_lt_one))).mono (fun i u=> (u.2 (v i) u.1).1)) -- type hole tune
 apply tendsto_of_tendsto_of_dist hh; rw [tendsto_zero_iff_norm_tendsto_zero,Metric.tendsto_nhds]
 intro ε E; filter_upwards [e', pL.eventually (he _ E)] with k w s; rw [dist_zero_right,norm_norm,Real.norm_eq_abs,abs_of_nonneg dist_nonneg,dist_comm,dist_eq_norm]; exact (s _ w).2 (C k)
#print axioms PantallaS
end
end SignetS
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
