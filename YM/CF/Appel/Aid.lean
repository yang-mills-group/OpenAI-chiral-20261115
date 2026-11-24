import YM.CF.Appel.Hunt
set_option autoImplicit false
noncomputable section
namespace YM.CF.Appel
open Char Summit Neige
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric Newt Jet
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
 AnalyticBridge.NonflatCovarianceLocality.Matching
open Push.SectorMeasure Next.Fluctuations Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur PhysicalNext.JointLoad PatchReads
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace ENNReal NNReal
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{A A':Stores S}{F F':Forest S.ratio}{k k':S.Choices} {V W:Config G c}{x C:ℝ}{r l:ℕ}
 {Y: LinkArray G (Frozen A x F)}{Y':LinkArray G (Frozen A' x F')}{o:Site c}
variable {α E:Type} [Fintype α][DecidableEq α] [NormedAddCommGroup E][NormedSpace ℝ E] {p:α→Site c} {K v d s t:ℝ} {n:ℕ}
open Gaussian ProbabilityTheory AnalyticBridge.Annulus1AD
open SectorNext.Remainder.Affine SectorNext.Remainder.Scales
variable {q:Chi}{J:ChartRatio G}{D κ: ℝ}
-- authorize & emission receipt before choosing history length, with unused cumulative spare
structure SafeX(K:Teller G)(P:Patch)(J:ChartRatio G)(w κ width H:ℝ)(g n:ℕ)(x:ℝ):Prop where
 He : Ledger K P.L w κ (2*width) H n g x
 Hp : Seen K P.L w width x
 Hl : 120 ≤ radiusB x ∧ span P x ≤ radiusB x/50
 Hz : 0<width*fiery G x P.L ∧ 2*(width*fiery G x P.L)<firstRadius G ∧ 4*(width*fiery G x P.L)<J.radius
 HR : ∀ {c f:Side}(S:StepData c f)(T:Tube G S)(A:Stores S)(F:Forest S.ratio)(V:Config G c)(k:S.Choices)(O:Allocation G S x w),Cert P K S T x→ A.flags=RG.flags (temp x) V→ Standing (F:=F) (A:=A) O J (width*fiery G x S.patch.L) k V∧ ∃ B, Authorized A V F x B
lemma help(K:Teller G)(P:Patch)(hK:P.Branches K.bind G) (hJ:LocalRatio J) (w κ:ℝ)(hw:0<w)(hκ:0<κ):∃ W:ℝ,1≤W ∧ ∀ width≥W,∀ H:ℝ,∀ g n:ℕ,∀ᶠ x:ℝ in atTop,SafeX K P J w κ width H g n x:=by
 obtain ⟨C,E,hC,hE,hm⟩:= sponsored_permit K J hJ P hK w hw
 obtain ⟨p,hp,H⟩:= AnalyticBridge.Annulus1AD.started w K P.L hw -- tune
 let W:=max C p; refine ⟨W,hp.trans (le_max_right ..),fun width hd h g n=>?_⟩
 have hP : p ≤ width := (le_max_right ..).trans hd; have hc:C ≤ width:=(le_max_left ..).trans hd
 have he : Tendsto (fun x:ℝ=>width*fiery G x P.L) atTop (𝓝 0):=by have he:= (tally_g G P.L 0 1).const_mul width; rw [mul_zero] at he; refine he.congr fun x=> ?_; rw [fi]; ring
 filter_upwards [SectorNext.Remainder.Affine.authorize K P.L w κ (2*width) h n g hw hκ, hm,H width hP, he.eventually (gt_mem_nhds (show (0:ℝ) < min (firstRadius G/2) (J.radius/4) by have hp:= hJ.patch; have hy:=first_pos G; positivity)),small_span P, Work.E01.radiusB_tendsto.eventually_ge_atTop 120] with x ha hr hh he hr' hu
 obtain ⟨hi,hf,ht,hl,hq⟩:=hr; have hb:0≤fiery G x P.L:=temp_nonneg _; obtain ⟨hg,hj⟩:= lt_min_iff.mp he -- Needs reduce lambda
 refine ⟨ha,hh,⟨hu,hr'⟩,⟨hf.trans_le (mul_le_mul_of_nonneg_right hc hb),?_⟩,?_⟩ -- syntax hz
 · constructor <;> linarith
 intro c f S T A F V k O hx hy; obtain ⟨p,t⟩:= (hq c f S T hx.got hx.size hx.funds.1).2.2 A F k V O Chi.canonical
 obtain ⟨he,-,B,-,hv⟩:= t hy 1 zero_lt_one; rw [hx.got]; exact ⟨fun u h v i=> by obtain ⟨a,ha,hk,hp⟩:=he.core u h v i; exact ⟨a,ha.trans (mul_le_mul_of_nonneg_right hc hb),hk,hp⟩,⟨B,hv⟩⟩
end YM.CF.Appel
