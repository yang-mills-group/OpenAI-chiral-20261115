import GaugeFieldConstruction.SpigotS
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
variable {n:ℕ}{I:Type}[Fintype I][DecidableEq I]
-- volume of strips on any regular compact object, no regular border required.
private lemma halo_fS {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][ProperSpace E][MeasurableSpace E][BorelSpace E][SecondCountableTopology E](μ:Measure E)[Measure.IsAddLeftInvariant μ][IsLocallyFiniteMeasure μ] (f:E→ ℝ)(h:Continuous f)(v:E)(e:∀ t:ℝ,∀ x,f (t • v+x)=t+f x) (K:Set E)(q:IsCompact K): ∃ C>0,∀ r:ℝ,0<r→ μ.real (K ∩ {x | |f x|≤r})≤ C*r:= by
 obtain ⟨R,t⟩:= q.isBounded.subset_closedBall (0:E); let A:=closedBall (0:E) (R+ 3*‖v‖); have ha: μ A<⊤:= (ProperSpace.isCompact_closedBall _ _).measure_lt_top -- tune
 let B:= μ.real A; have hB:0 ≤ B:= measureReal_nonneg; refine ⟨B+1,(by linarith),?_⟩
 intro r hr; let z:= ⌊1/r⌋₊; let X:=Fin (z+1); let H:= K ∩ {x:E| |f x|≤r}; let p (i:X):= (i.val:ℝ)*(3*r); let Y (i:X)(x:E):= p i • v+x; let T (i:X):= Y i ⁻¹' H
 have he(i:X): ↑(i:ℕ) ≤ (z:ℝ):=by exact_mod_cast (Nat.lt_succ_iff.mp i.isLt : _≤ z)
 have ht: (z:ℝ)≤ 1/r:= Nat.floor_le (by positivity); have hz(i:X): p i≤3:=by unfold p; have he:= (le_div_iff₀ hr).mp ((he i).trans ht); linarith only [he]
 have hx :Pairwise (Function.onFun Disjoint T):=by
   have hp(i j:X)(h:i<j): Disjoint (T i) (T j):=by
      apply Set.disjoint_left.mpr; intro x m l
      have hb:|p i+f x|≤r:= (e (p i) x) ▸ (show |f (p i • v+x)|≤r from m.2) -- tune
      have hd:|p j+f x|≤r:= (e (p j) x) ▸ (show |f (p j • v+x)|≤r from l.2)
      have hr':(↑(i.val):ℝ)+1 ≤ (↑(j.val):ℝ):=by exact_mod_cast (show i.val+1≤j.val from h)
      have hv:p i+3*r ≤ p j:=by unfold p; exact (le_of_eq (Eq.symm (by rw [add_mul,one_mul]))).trans (mul_le_mul_of_nonneg_right hr' (by positivity)) -- tune
      linarith only [ (abs_le.mp hb).1,(abs_le.mp hd).2,hv,hr]
   intro a b v; rcases lt_or_gt_of_ne v with p|p; · exact hp a b p
   exact (hp b a p).symm
 have hX(i:X): MeasurableSet (T i):=((q.measurableSet.inter (measurableSet_le h.abs.measurable measurable_const)).preimage (show Continuous (Y i) from continuous_const.add continuous_id).measurable)
 have h'(i:X): μ (T i)= μ H:= measure_preimage_add _ (p i • v) H
 have hY: μ H<⊤:=lt_of_le_of_lt (measure_mono Set.inter_subset_left) q.measure_lt_top
 have hA: (⋃ i:X,T i) ⊆ A:= by
    intro x m; obtain ⟨i,v⟩:=Set.mem_iUnion.mp m; unfold A; rw [Metric.mem_closedBall,dist_zero_right]
    have h': ‖Y i x‖ ≤ R:=by
       have hx := t v.1; simpa only [Metric.mem_closedBall,dist_zero_right] using hx
    let d₀:=p i; calc
        _ = ‖Y i x-d₀ • _‖:= by congr; unfold Y d₀; abel
        _≤ ‖Y i x‖+‖d₀ • _‖:= norm_sub_le ..
        _≤ _:=add_le_add h' (by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by unfold d₀ p; positivity)]; exact mul_le_mul_of_nonneg_right (hz i) (norm_nonneg _))
 have hw: (z+1:ℕ)*μ.real H ≤ B:=by
    apply le_trans (le_of_eq ?_) (measureReal_mono hA ha.ne); rw [measureReal_iUnion_fintype hx hX (fun i=>(h' i).symm ▸ hY.ne)]; unfold Measure.real; simp_rw [h']; rw [sum_const,Finset.card_univ]; change _= Fintype.card (Fin (z+1)) • _; rw [Fintype.card_fin,nsmul_eq_mul]; -- tune
 have hk:1/r ≤ (↑(z+1:ℕ):ℝ):=by push_cast; exact (Nat.lt_floor_add_one _).le
 have hB': 1/r * μ.real H ≤ B:= (mul_le_mul_of_nonneg_right hk measureReal_nonneg).trans hw
 change μ.real H ≤_ ; exact (show μ.real H≤B*r from (div_le_iff₀ hr).1 (by simpa [div_eq_inv_mul] using hB')).trans (by linarith) -- tune
-- Orientation Works.S.E measure variant uniform volume. Need readability points.X Est.
section
abbrev ΦplanR (n:ℕ)(x:Points n):DiagramR (Fin n):= fun i j=>x i j
abbrev B_Esc (n:ℕ):= ΦplanR n ⁻¹' CardsR (Fin n)
abbrev P_Esc (n:ℕ):= ΦplanR n ⁻¹' MasksR (Fin n)
lemma ΦlegR (n:ℕ) : Continuous (ΦplanR n):=by
 let f : (Fin n→E4) →DiagramR (Fin n):= fun x i j=> x i j
 apply (show Continuous f by unfold f; fun_prop).comp (show Continuous (fun x:Points n=> x.ofLp) by fun_prop)
lemma Bopen_R (n:ℕ): IsOpen (B_Esc n):= (prosc_R ..).preimage (ΦlegR ..)
lemma Popen_R (n:ℕ): IsOpen (P_Esc n):= (ply_openR ..).preimage (ΦlegR ..)
abbrev FeeCord (a b:Fin n)(j:Axis)(x:Points n):ℝ:= x a j-x b j
abbrev Bibbin (n:ℕ):= {p : (Fin n × Fin n) × Axis // p.1.1≠p.1.2}
def TurnFigureS (r:Bibbin n) (z:ℝ): Set (Points n) := {x | |FeeCord r.val.1.1 r.val.1.2 r.val.2 x|≤6*z}
lemma TurnΦcS (r:Bibbin n)(z:ℝ) : IsClosed (TurnFigureS r z) := isClosed_le (show Continuous fun x:Points n=> |FeeCord r.val.1.1 r.val.1.2 r.val.2 x| by unfold FeeCord; fun_prop) continuous_const
abbrev StrikeM_S (n:ℕ)(z:ℝ) := ⋃ i:Bibbin n, TurnFigureS i z
lemma StressσS (n:ℕ)(z:ℝ) : IsClosed (StrikeM_S n z) := isClosed_iUnion_of_finite fun i=> TurnΦcS i z
lemma EaseFigureS (r:ℝ) (x:Points n)(g:0 < r)(p:x∉ StrikeM_S n r) : LobeS r (ΦplanR n x):=by
 let F:= ΦplanR n x
 have h{a b:Fin n}(j:Axis)(e:a≠b) : 6*r< |x a j-x b j|:=lt_of_not_ge fun t=> p (Set.mem_iUnion.mpr ⟨⟨((a,b),j),e⟩,t⟩)
 intro i; have hu:F∈ VplaneR (Fin n) i:=by
    intro a b e; by_contra v; have H:= (mul_pos (by norm_num:0<(6:ℝ)) g).trans (h i v); rw [show x a i=x b i from e,sub_self,abs_zero] at H; exact lt_irrefl _ H
 obtain ⟨L,q,u⟩:= vplane_w hu; refine ⟨L,q,List.Pairwise.imp (fun {a b} t=>?_) u⟩; change F a i < F b i at t; have p: b≠a:=fun q=> lt_irrefl _ (q ▸ t); have H:= h i p; rw [abs_of_nonneg (sub_nonneg.mpr (show x a i ≤ x b i from t.le))] at H; exact H.le
-- measure packing.Density.Centre proofs
lemma Hamper_S (r:Bibbin n) (K:Set (Points n))(q:IsCompact K): ∃ C>0, ∀ δ:ℝ,0<δ→ volume.real (K∩ TurnFigureS r δ) ≤ C*δ:=by
 let a:=r.val.1.1; let b:=r.val.1.2; let h:=r.val.2; let f (x:Points n):ℝ:= x a h-x b h
 let w:= points (fun i:Fin n=>if i=a then basis h else (0:E4))
 have hx (t:ℝ)(x:Points n):f (t • w+x)=t+f x:=by
    have q:w a h=1:=by unfold w points; simp [basis] -- tune
    have p:w b h=0:=by unfold w points; simp [Ne.symm (show a ≠ b from r.2)]
    change t*w a h+x a h-(t*w b h+x b h)=t+(x a h-x b h); rw [q,p]; ring
 obtain ⟨C,g,t⟩:=halo_fS volume f (show Continuous f by unfold f; fun_prop) w hx K q
 refine ⟨C*6,mul_pos g (by norm_num),fun i p=>?_⟩
 unfold TurnFigureS; rw [mul_assoc]; exact t _ (mul_pos (by norm_num) p)
lemma VolumeEaseS (K:Set (Points n))(q:IsCompact K):∃ C>0, ∀ δ:ℝ,0<δ→ volume.real (K∩ StrikeM_S n δ)≤ C*δ:=by
 choose c t h using fun r:Bibbin n=> Hamper_S r K q
 have h₀:0≤∑ i,c i:=Finset.sum_nonneg fun i _=> (t i).le
 refine ⟨1+∑ i,c i,by linarith,fun d p=>?_⟩; rw[_root_.add_mul,Finset.sum_mul,one_mul,StrikeM_S,Set.inter_iUnion]; exact (measureReal_iUnion_fintype_le _).trans ((sum_le_sum (fun i _=>h i d p)).trans (le_add_of_nonneg_left p.le)) -- rw def syntax
lemma VolumePlenumS (n:ℕ): volume ((P_Esc n)ᶜ)=0:=by
 let μ:Measure (Points n):= volume; let G:= (P_Esc n)ᶜ; let D (i:ℕ):= closedBall (0:Points n) (i:ℝ); have hp(i:ℕ):IsCompact (D i):=ProperSpace.isCompact_closedBall _ _
 have he(i:ℕ):μ (D i∩G)=0:=by
    obtain ⟨C,c,t⟩:=VolumeEaseS (D i) (hp i)
    have hx:μ (D i)<⊤:= (hp i).measure_lt_top
    have g(d:ℝ)(p:0< d): G ⊆  StrikeM_S n d:=by
       intro x m; by_contra! v; have he:= EaseFigureS d x p v; have hu: ΦplanR n x∈ MasksR (Fin n):=by
          intro j; obtain ⟨l,H,r⟩:= he j; exact char_R ⟨H,List.Pairwise.imp (fun a=>sub_pos.mp ((mul_pos (by norm_num:0<(6:ℝ)) p).trans_le a)) (show l.Pairwise _ from r)⟩
       exact m hu -- tune
    let b:= μ.real (D i∩G); by_contra! v; have h:0<b:= ENNReal.toReal_pos v (ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_left) hx)) -- tune signature
    have ht:0<b/(2*C):=by positivity
    let r:=b/(2*C)
    have hh:b≤C*r:= (measureReal_mono (Set.inter_subset_inter_right _ (g r ht)) (ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_left) hx))).trans (t r ht); unfold r at hh; field_simp at hh; linarith
 have hK: G= ⋃ i:ℕ,(D i∩G):=Set.Subset.antisymm (fun x t=>by obtain ⟨n,h⟩:=exists_nat_gt ‖x‖; exact Set.mem_iUnion.mpr ⟨n,(show x∈ D n ∩ G from ⟨(by simpa only [D,Metric.mem_closedBall,dist_zero_right] using h.le), t⟩)⟩) (Set.iUnion_subset fun i=>Set.inter_subset_right)
 change μ G=0; rw [hK]; exact measure_iUnion_null he
lemma P_Efull (n:ℕ): ∀ᵐ x:Points n, x∈P_Esc n :=VolumePlenumS n
#print axioms P_Efull
end
end SignetS
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
