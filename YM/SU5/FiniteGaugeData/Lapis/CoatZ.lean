import YM.SU5.FiniteGaugeData.Lapis.Label
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.LapisS
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Heat Quest Fock.Brique
open Nacre Heat Charm Chrono Journey
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
open SalonG
open YM.SU5.FiniteGaugeData.Lapis Lumi Eight
open Next.Rank Spindle Push.Local Rhythm LightK
namespace Stadium
variable {ι:Type}[Fintype ι][DecidableEq ι]
variable (T:Duct SU.group ι)(K:Clip){r x α b:ℝ}{N:Side}
variable (Q:Calibration)(p:Cover)(a: Signed)(z:ℂ) (n:Side)
local notation "I₁"=> Lumi.macroK ι T
local notation "S₁"=> scape p (macroK ι T)
local notation "X₀" => pole T K r Q p a

def plaza (K:Clip)(r:ℝ)(Q:Calibration)(o:Cover)(s:Signed) (z:ℂ) (α:ℝ): W Q:= (Real.exp α:ℂ) • (1+z • pole T K r Q o s)
lemma mint : Locator Q (plaza T K r Q p a z α) (scape p (macroK ι T)):=locate_scale _ _ _ (locate_sum _ _ (locate_one ..) (locate_scale _ _ _ (paneBolt ..)))
-- scalar post exactly on ANY fields. no native normalization assumed
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
variable (s i k:ℕ)
local notation "Kₜ" =>tent Y h
local notation "N₁"=> side Y i s
local notation "P"=> plaza T K r (tent Y h) p a z α
local notation "V₀" v:max => Lumi.live T K r a (wrap (More (side Y i s)) p) v
lemma candy (x:Fields N₁) : sold Y h s i (plaza T K r (tent Y h) p a z α).val x=(Complex.ofReal (Real.exp α)*(1+z* Complex.ofReal (V₀ x.1))) • (1:FC (Single N₁)):=by
 unfold plaza; rw [Subalgebra.coe_smul,Subalgebra.coe_add,Subalgebra.coe_smul,map_smul,map_add,map_smul]; change _=((Real.exp α:ℂ)*(1+z * (Lumi.live T K r a (wrap (More N₁) p) x.1:ℂ))) • (1:FC _); rw [sold_rod,identityW,sold_one]; simp only [Pi.smul_apply,Pi.add_apply,Pi.one_apply,mul_add,mul_one,add_smul,smul_add,smul_smul] -- exact
abbrev pulse(b:ℝ):ℝ:= (b*T.h)^2/2
lemma tint (v:ℝ) (t:‖z‖≤b)(p:|v|≤T.h): ‖1+z*(v:ℂ)‖≤ Real.exp (z.re*v+pulse T b):=by
 let y:= z*(v:ℂ); let x:= z.re*v; have he:x=y.re:=by simp [y,x]
 have ht₀:0≤b:=(norm_nonneg _).trans t; have ht:‖y‖ ≤ b*T.h:=by unfold y; rw [norm_mul,Complex.norm_real]; exact mul_le_mul t p (norm_nonneg _) ht₀
 have hx: ‖1+y‖^2=1+(‖y‖)^2+2*x:=by rw [Complex.sq_norm,Complex.normSq_add,he,Complex.sq_norm]; simp
 have hK:(1+‖y‖^2+2*x) ≤ Real.exp (x+pulse T b)^2:=by
    rw [sq (Real.exp _),←Real.exp_add]; unfold pulse; linarith only [Real.add_one_le_exp (x+(b*T.h)^2/2+(x+(b*T.h)^2/2)),pow_le_pow_left₀ (norm_nonneg _) ht 2]
 exact (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le).1 (hx.trans_le hK)
-- same codec geometry.
lemma stake (t:‖z‖≤b) : LapisS.Rent Y h s i T K r z.re (α+pulse T b) 1 (scape p (macroK ι T)) (plaza T K r (tent Y h) p a z α):=by
 unfold Rent; rw [spindle_PATCH]; apply Packed.singleton_t (wrap (More N₁) p) a _ (Subset.refl _); intro V; let x:ℝ:= V₀ V.1; let y:ℂ:=z*(x:ℂ); refine ⟨(Real.exp α:ℂ)*(1+y),candy ..,?_ ⟩
 rw [norm_mul, Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]; refine (mul_le_mul_of_nonneg_left (tint T z x t (T.enough _)) (Real.exp_pos _).le).trans_eq ?_
 rw [←Real.exp_add]; unfold Lumi.makes; rw [sum_singleton]; congr 1; change α+ _= z.re *x +_; ring
lemma stand(C:ℝ)(u:α≤ C)(t:‖z‖≤b)(X:Fields N₁): ‖sold Y h s i (plaza T K r (tent Y h) p a z α).val X‖ ≤ Real.exp C*(1+b*T.h):=by
 rw [candy,norm_smul, norm_one,mul_one,norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]; apply mul_le_mul (Real.exp_monotone u) _ (norm_nonneg _) (Real.exp_pos _).le; apply (norm_add_le ..).trans; rw [norm_one,norm_mul,Complex.norm_real]; exact add_le_add_right (mul_le_mul t (T.enough _) (norm_nonneg _) ((norm_nonneg _).trans t)) _
end Stadium
end YM.CF.Buffered.Afterglow.Hierarchy.LapisS
#print axioms YM.CF.Buffered.Afterglow.Hierarchy.LapisS.Stadium.stake
