import GaugeFieldConstruction.OvaPeakJ
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
variable {P:Spine}{X Z:Type}[Fintype X][Fintype Z][LinearOrder X][LinearOrder Z]
variable {θ:BandS→ℕ}{G:ℝ}{f0:ℕ}
variable (p:RosterJ P θ G f0)
-- Bamboo table for all visits.At arrays even torus support, t Mind consumed.
variable {m i k f:ℕ}
local notation "ΤΓ"=> P.run
local notation "ΓΥ"=> P.run.uv k
variable (w:f0 ≤ P.run.uv k)(h:(P.run.voyage i).kick≤ k)
local notation "Qi"=> p.Z i k w h
#check ProbeθJ
variable (B0:SωJ θ)(M:JωL θ)
namespace BoonsθJ
open JetCurry JetCurry.TrekJ ProbeθJ Yoke
variable (Ω:BoonsθJ p B0 M i k w h)(x:P.VMark)(R:Signed × Bool)(u:BandS)
variable {s t r:ℕ} {n:ℕ}
local notation "Ξu"=> Fin (θ u)
local notation "Φ"=> (ΓPrimary P.run i k θ)
local notation "η"=> FrameK (Fin (θ u))
variable (W:X→LaurelJ)(L:finsJ)(U:X→ Signed × Bool)(S:X→P.VMark)(Y:BoardDate X)
variable (B:SailκJ X θ→Waves)(Z:PlumberJ P.run i k X θ)(H: SalaryJ p B0 M i k w h S W U Y B f Z) (x':X) (tQ:R=U x')(pX:S x'=x)
local notation "Fν"=> FrameK (Fin (θ u))
-- Base x, any grade.T Echo test for any y at j*. Expresses ETOP independent Layout, Mirror.C law.
local notation "KΡ"=> RankQJ P.par
local notation "Zζ"=> P.run.uv k
variable (v:LaurelJ) (y:FrameK (Fin (θ u)))
-- label constraints.
set_option linter.unusedSectionVars false
set_option maxHeartbeats 240000
variable (Hv:Adept_T θ B0 M G)
-- reconstruct qualifications for FIN n constant. define transport-independent charge
local notation "cΞ"=> (TideMaskJ (f:=f) p w h B0 M Ω x R u)
local notation "ΤΩ"=> EchoTideJ (f:=f) p w h B0 M Ω x R u
local notation "Αζ"=> SailGateJ p w h B0 M Ω x R u
local notation "MΤ"=> Mark (side P.run i Zζ)
-- hull_any.Mark on ALL arrangements carrying grants. $L used only in grip. require boot zero. ANY Salary path constant x and R; V lens.Any Y Budget along b=claim from α. Shift palette P inside.
variable (m:ℕ)(κ:ℕ→BandS→ Fin 6)
-- sorted estimate for any layout (l prefix all Fin, last)
local notation "ΓN"=>P.run.uv k
local notation "qΘ"=> Collapse_J P
variable (q₀:f0 ≤ f)(e:3*f ≤ P.run.uv k)
-- correct startup blank. anchor p charged fee+ET.K.Work.Layout
local notation "Kχ"=> ΦWallet p
local notation "qΧ"=>RankQJ P.par f0
local notation "ξp"=> RankQJ P.par
abbrev FinchΩ (P:Spine)(f:ℕ)(V:LaurelJ)(t:ℂ) (i k:ℕ): Mark (side P.run i (P.run.uv k)):=TideJ P f V t • 1
lemma bannerΩ (c:ℂ)(u:Fin n→LaurelJ)(h:(P.run.voyage i).kick ≤ k): ‖Cap_ZΛ P.run i k (List.ofFn fun j=>FinchΩ P f (u j) c i k).prod‖ = ‖c‖^n:=by
 let Q(V:LaurelJ):= (TideJ P f V) c; let Z:= Q ∘ u; let J:=fun j=> Z j • (1:Mark (side P.run i (P.run.uv k))) -- tune index
 let γ:=List.finRange n
 have hp(l:List (Fin n)): (l.map J).prod= (l.map Z).prod • 1:=by induction l with | nil=> simp | cons j l ih=> rw [List.map_cons,List.prod_cons, ih,List.map_cons,List.prod_cons]; unfold J; rw [Algebra.smul_mul_assoc,one_mul,smul_smul]
 have hx(l:List (Fin n)): ‖(l.map Z).prod‖=‖c‖^l.length:=by induction l with |nil=> simp| cons j l ih=>rw [List.map_cons,List.prod_cons,norm_mul,ih, show ‖Z j‖=‖c‖ from ζNormJ (u j) c, List.length_cons,pow_succ',mul_comm]
 change ‖Cap_ZΛ _ _ _ (List.ofFn J).prod‖=_; rw [List.ofFn_eq_map,hp,Cap_ZΛ,Tapestry.scaleReader,Tapestry.oneReader _ _ _ _ ⟨h,le_rfl⟩, norm_smul,norm_one,mul_one,hx,List.length_finRange]
variable (pY:StaccatoJ p w h B0 M Ω x R u y)
lemma CargoStretchJ {v v':ℝ}{X:Mark (side P.run i (P.run.uv k))}{j:LaurelJ}(hp:CargoBillJ (f:=f) p w h B0 M x R κ L u j X v)(e:v≤v') :CargoBillJ (f:=f) p w h B0 M x R κ L u j X v':=fun X _ _ W B Z P ξ v k=> ChargedJ.lift e (hp X W B Z P ξ v k)
lemma pow_shiftχ (x a b:ℝ)(n:ℕ)(e:0≤ a)(f:0≤ b)(g:x^n ≤ a^n+b^n)(h:0<n): x^n ≤ (a+b)^n:=by
 refine g.trans ?_
 obtain ⟨n,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
 rw[pow_succ a,pow_succ b,pow_succ,mul_add]; exact add_le_add (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ e (le_add_of_nonneg_right f) _) e) (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ f (le_add_of_nonneg_left e) _) f)
local notation "Τ0"=> Effortχ P f0 f0
variable (Bδ:ℝ)(hB:LoomK y≤ Bδ)
local notation "Λb"=> Effortχ P f0 f0 Bδ
local notation "Δs" => P.run.uv k
include pY Hv hB
#check playerLJ
#check HoldTariffJ
lemma capφ (e:3*f0 ≤ P.run.uv k)(z:Collapse_J P n i f0)(W':Fin n→LaurelJ)(o: SevJ P f0 n i x W') (Lq:(n:ℝ)*(plumeZ P.par.R.L (P.run.uv k))⁻¹*(ΦWallet p* Effortχ P f0 f0 Bδ (RankQJ P.par f0*Bδ) u (P.run.uv k))^n ≤ (1:ℝ)^n): ‖SailSubsidyJ p w h B0 M Ω x R u y‖ ≤ ΦWallet p* (RankQJ P.par f0 * Bδ)+1:=by
 let c':=SailSubsidyJ p w h B0 M Ω x R u y; let V:= fun j:Fin n=> FinchΩ P f0 (W' j) c' i k; let U':=fun j:Fin n=> EchoTideJ (f:=f0) p w h B0 M Ω x R u (W' j) y
 let K:= V+U'; let Qμ:= ξp f0* Bδ; have he:0 ≤ RankQJ P.par f0:=(p.tempo f0 le_rfl).1.le; have hx:= (noLoom y).trans hB; have hQ:0≤Qμ:=mul_nonneg he hx; let κ:ℕ→BandS→Fin 6:= fun _ _=> 0; let z':=(Λb) Qμ u Δs
 have K0(j:Fin n): CargoBillJ (f:=f0) p w h B0 M x R κ 0 u (W' j) (K j) Qμ:=by
    intro X _ _ Y B Z H ξ v _; rw [show K j= SunLO (d0:=ξ) (f:=f0) p w h B0 M Ω x R u Z (fun s=>wayZJ P.par f0 s (Y ξ)) false f0 y from ?_]
    · apply ChargedJ.lift _ (FarePoolJ p w h B0 M Ω x R u Y (fun _=> R) (fun _=>x) _ B Z H ξ rfl rfl le_rfl w y); rw[FarePQ,if_pos (le_refl f0),mul_comm]; exact mul_le_mul_of_nonneg_left hB he
    rw [TorrentJ p w h B0 M Ω x R u Y (fun _=>R) (fun _=>x) _ B Z H ξ rfl rfl,v,add_comm]; rfl -- Y,H Step issue
 obtain ⟨v,v',t,d⟩:= HoldTariffJ p w h B0 M Ω x R u y le_rfl Qμ Bδ hQ hB -- tune
 have hh: Qμ≤ z':=(le_add_of_nonneg_left ((mul_nonneg (noLoom _) ((p.tempo _ w).1.le)).trans v)).trans d
 let ht:=WristBudgetJ p w h B0 M x R u 0 Hv κ le_rfl e W' o z K K0 hQ
 have hε(j):CargoBillJ (f:=f0) p w h B0 M x R κ 0 u (W' j) (V j) z':= CargoStretchJ p w h B0 M x R u 0 κ (playerLJ (f:=f0) p w h B0 M x R u 0 (W' j) κ c') t
 have hw := HandboundJ p w h B0 M Ω x R u 0 y Hv κ le_rfl e W' o z _ (hQ.trans hh) pY 1 (by decide) (fun _ _ _=>by decide) K V v' (fun i=> CargoStretchJ p w h B0 M x R u 0 κ (K0 i) hh) hε (fun _=>rfl)
 have hV:‖c'‖^n≤ ((ΦWallet p*Qμ)+1)^n:=by
    refine pow_shiftχ ‖c'‖ (ΦWallet p*Qμ) 1 n (mul_nonneg (WalletB _).le hQ) (by norm_num) ?_ (roomProfitJ z).1
    rw [← bannerΩ (P:=P) (f:=f0) c' W' h]; let Ω_:=Cap_ZΛ P.run i k (List.ofFn K).prod; let T:=Cap_ZΛ P.run i k (List.ofFn V).prod
    change ‖T‖≤_; rw [show T=Ω_-(Ω_-T) from (by abel)] -- rw rewrites Ω_-T? target doesn't. 
    exact (norm_sub_le ..).trans (add_le_add ht (hw.trans Lq))
 exact le_of_pow_le_pow_left₀ (Nat.ne_of_gt (roomProfitJ z).1) (add_nonneg (mul_nonneg (WalletB _).le hQ) (zero_le_one)) hV -- tune
#print axioms capφ
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
