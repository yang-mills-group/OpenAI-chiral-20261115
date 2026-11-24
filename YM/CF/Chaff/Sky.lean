import YM.CF.Gully.Cove
import YM.CF.Rill.Pott
import YM.CF.Skye.Hark
import YM.CF.Prism.Pecu
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 450000
noncomputable section
namespace YM.CF.Chaff
open Function NormedSpace Filter Metric Finset Lattice MeasureTheory RG
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Kronecker
open Pressure
open Cube Lat Tenant Tulip Gully Spire Scroll Scree Jet Ave Skye Gas Pastry Dial Fock
section fro
open scoped Matrix.Norms.Frobenius
lemma farm_x (i j:SU.F): ContDiff ℝ ω (fun x:SU.group.Color=> SU.fund (SU.group.lieExp x) i j):=by
 let L:SU.group.Mat →ₗ[ℝ] ℂ:={ toFun:=fun x=>x i j,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }; exact (LinearMap.toContinuousLinearMap L).contDiff.comp SU.group.exp_jet
end fro
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
lemma eve : ContDiff ℝ ω (SU.fund ∘ SU.group.lieExp):=by
 let f(x:SU.group.Color): SU.F → SU.F →ℂ :=fun i j=> SU.fund (SU.group.lieExp x) i j
 have ht:ContDiff ℝ ω f:= contDiff_pi.mpr fun i=>contDiff_pi.mpr fun j=> farm_x i j; exact ((Nacre.coordL (k:=SU.F)).symm.toContinuousLinearMap.contDiff.comp ht) -- tune
variable {m B N: Side}{a e v K H C:ℝ}{n:ℕ}
local notation "Λ" => CSide m B
local notation "ξ"=> Domain m B
local notation "G"=>SU.group
lemma larder (k:ℕ):∃ K:ℝ,1≤K∧∀ (n:Side)(U:Pane n),∀ x:tangD n,‖x‖≤1 →TransK k (increment U) x K:=by
 obtain ⟨C,h,g⟩:= Push.Uniform.exists_allows (isCompact_closedBall (0:SU.group.Color) 1) (f:=SU.fund ∘ SU.group.lieExp) (fun i _=> eve.contDiffAt) k
 let D:=composeCost k C 1; refine ⟨max 1 D,le_max_left ..,fun n U x p i=>?_⟩
 let l:= ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ :reach n=>SU.group.Color) i; have hp: ‖l x‖ ≤1:= (norm_le_pi_norm x i).trans p; let hK:=g (l x) (mem_closedBall_zero_iff.mpr hp); have he: Allows k (fun y:tangD n=>SU.fund (SU.group.lieExp (l y))) x D:= (show Allows k _ _ C from ⟨hK.1.of_le le_top,hK.2⟩).comp (allows_linear (ContinuousLinearMap.opNorm_le_bound l zero_le_one (fun u=> (norm_le_pi_norm u i).trans_eq (one_mul _).symm)) hp)
 let V:=(ContinuousLinearMap.mul ℝ (Op SU.F)).flip (SU.fund (U i)); have hL: ‖V‖≤1:=by refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v=>?_ ; rw [one_mul]; exact (norm_mul_le v _).trans_eq (by rw [show ‖SU.fund (U i)‖=1 from CStarRing.norm_of_mem_unitary (SU.fund_U _),mul_one])
 have hh:=he.linear V hL; rw [one_mul] at hh; refine (hh.mono (le_max_right ..)).germ (Eventually.of_forall fun y=>?_); simp only [increment, SU.fund_mul]; rfl
lemma toll_y (g:a<e):∃ s:ℝ,0<s ∧ s ≤1∧∀ (m:Side)(U:Pane m),Guard U a →∀ x:tangD m, ‖x‖<s→Guard (increment U x) e:=by
 let p:= (e-a)/4; have hp:0<p:=div_pos (sub_pos.mpr g) (by norm_num)
 have he: Tendsto (brand ∘ SU.group.lieExp) (𝓝 0) (𝓝 1):=by have h:= (Dial.spinD.comp (SU.group.lieExp_cont)).continuousAt (x:=0); simpa only [ContinuousAt,Function.comp_apply,SU.group.mat_lieExp_zero,brand_one] using h
 obtain ⟨r,t,w⟩:=Metric.eventually_nhds_iff.mp (he.eventually (ball_mem_nhds _ hp)); refine ⟨min 1 r,lt_min zero_lt_one t,min_le_left ..,fun m U p' x hx=>?_⟩
 rw [show e=a+4*p by unfold p; ring]; refine turns_B _ _ p' (fun i=> ?_); simp only [increment,brand_mul]; have h:‖brand (SU.group.lieExp (x i))-1‖ ≤ p:= (mem_ball_iff_norm.mp (w (by rw [dist_zero_right]; exact ((norm_le_pi_norm x i).trans_lt hx).trans_le (min_le_right ..)))).le -- tune
 have he(y:Tulip.Twig): ‖y*brand (U i)‖=‖y‖:= by rw [show brand (U i)=star (brand ((U i)⁻¹)) by rw [brand_inv,star_star],brand_rig]
 rw [← show _ * brand (U i)= brand (SU.group.lieExp (x i))*brand (U i)-brand (U i) from (show (brand (SU.group.lieExp (x i))-1)*brand (U i)=_ by rw [sub_mul,one_mul]),he]; exact h
end YM.CF.Chaff
