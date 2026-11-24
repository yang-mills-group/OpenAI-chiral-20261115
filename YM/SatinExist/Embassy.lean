import YM.SatinExist.Tipple
import SatinThinCoalition
import YM.SatinExist.Lunary
import YM.SatinExist.ShiftE
import YM.SatinExist.Taint
import YM.SatinExist.Cameo
import SatinThinBeam
import SatinThinMill
-- Raze sell at finite registration. Toward unpadding on MANY *Operators*.
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open TopologicalSpace Germ Alliance
namespace Spine
open Aria Set TopologicalSpace Metric Casting
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j) (D:P.Apron)(n w:ℕ)
local notation "K"=> P.calibration
local notation "Μ"=> timeMesh P.par
local notation "N"=> notch (timeMesh P.par)
local notation "Γ"=> P.VMark
local notation "κ"=> P.laysM
local notation "ψ"=> P.physicalEnergy j x
local notation "ν"=> P.seasons j x
local notation "E"=> (P.physicalEnergy j x).E
local notation "ω"=> P.colorZero j x
local notation "Φ"=> P.colorSpace j x
local notation "X"=>P.ColorHil j x
local notation "Χ"=>P.ManyF j x
local notation "υ" v:max=>P.voxTest j n v
local notation "Π"=> P.pillar j x
section
omit P
open SatinTails SatinNucleus
variable {V:Hilbert}{T':ℕ→V.Op}{Y:V.Op}
private lemma crewWindBudget (q:ℕ → Coalition)(z:V)(f:ℕ→V)(v:Tendsto f atTop (𝓝 z)): Tendsto (fun n=>∑ i∈(q n).voters,((q n).w i:ℂ) • f (n+i)) atTop (𝓝 z):=by
 have he(n i:ℕ)(e:i∈(q n).voters): ‖((q n).w i:ℂ)‖=(q n).w i:= by rw [Complex.norm_real,Real.norm_of_nonneg ((q n).signed i e)];
 apply Metric.tendsto_nhds.mpr; intro e p; obtain ⟨n₀,H⟩:=eventually_atTop.1 (Metric.tendsto_nhds.mp v (e/2) (half_pos p)); filter_upwards [eventually_ge_atTop n₀] with n a
 let b(i:ℕ):ℂ:= (q n).w i; let D:= q n
 rw [dist_eq_norm]; refine lt_of_le_of_lt ?_ (half_lt_self p); change ‖_ -_‖≤ _
 have hZ:(∑ i∈ D.voters,b i • f (n+i)) - z=∑ i∈ D.voters,b i • (f (n+i)-z):=by
    have hw: (∑ i∈ D.voters,b i) = 1:=by change ∑ i∈ D.voters, (D.w i:ℂ)=1; rw [← Complex.ofReal_sum,D.pledges]; rfl
    simp_rw [smul_sub,sum_sub_distrib,←Finset.sum_smul,hw,one_smul]
 change ‖(∑ i∈ D.voters,b i • f (n+i))-z‖≤_; rw [hZ]
 refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun i=>D.w i*(e/2)) (fun i t=>?_)).trans_eq ?_)
 · rw [norm_smul,show ‖b i‖=D.w i from he n i t]; exact mul_le_mul_of_nonneg_left ( (dist_eq_norm (f (n+i)) z) ▸ (H (n+i) (by omega)).le) (D.signed i t)
 rw [← Finset.sum_mul,D.pledges,one_mul]
private lemma budgetWindCost (q:ℕ → Coalition)(C:ℝ)(t:∀ i, ‖T' i‖≤C)(n:ℕ) : ‖∑ i∈ (q n).voters, ((q n).w i:ℂ) • T' (n+i)‖ ≤ C:=by
 have he(n i:ℕ)(e:i∈(q n).voters): ‖((q n).w i:ℂ)‖=(q n).w i:= by rw [Complex.norm_real,Real.norm_of_nonneg ((q n).signed i e)];
 let I:= q n; exact (norm_sum_le ..).trans ((sum_le_sum (g:=fun i=>I.w i*C) (fun i s=>by rw [norm_smul,he n i s]; exact mul_le_mul_of_nonneg_left (t _) (I.signed i s))).trans_eq (by rw [← Finset.sum_mul,I.pledges,one_mul]))
private lemma byWin (a:ℕ)(q:Coalition)(b:V): ∑ i∈ q.voters, (q.w i:ℂ) • (T' (a+i) b)=(∑ i∈ q.voters, (q.w i:ℂ) • T' (a+i)) b:=by classical simp
private lemma crewStarEq (a:ℕ)(q:Coalition) : ∑ i∈ q.voters, (q.w i:ℂ) • (star (T' (a+i)))=star (∑ i∈ q.voters, (q.w i:ℂ) • T' (a+i)):=by simp

private lemma crewWind (q:ℕ → Coalition)(h:Brakes T' Y):Brakes (fun n=>∑ i∈ (q n).voters, ((q n).w i:ℂ) • T' (n+i)) Y:=by
 obtain ⟨C,p,t⟩:= h.costAll
 constructor
 · exact ⟨C,Eventually.of_forall fun n=> budgetWindCost q C t n⟩
 · intro y; exact (crewWindBudget (V:=V) q _ _ (h.brakes y)).congr fun n=> byWin n (q n) y
 intro y; exact (crewWindBudget (V:=V) q _ _ (h.heels y)).congr fun n=> ((byWin (T':=fun i=> star (T' i)) n (q n) y)).trans (congrArg (fun (T:V.Op)=> T y) (crewStarEq n (q n)))
end
section finance
open SatinTails SatinNucleus Six MacroGrid
variable (P:Spine)(x:P.Spectrum0 3)(j:Axis)(f r:ℕ)(v:ℕ→ℕ)(a:ℕ→ℝ)(u:StrictMono v)(q:ℕ → Coalition)(l:List Axis)
local notation "Y!" s:max=>P.pleading x f r s (q s) v a u -- signature order?
local notation "D!" s:max=> (Y! s).pivot P l
local notation "F!" i:max=> (P.basePlay x f (v i)).pivot P l
local notation "ξ"=> P.advocate 3 x j
local notation "V"=> P.ManyF j (P.advocate 3 x j)
local notation "M!" t:max G:max=> P.pillar j ξ G (-t) t 0
local notation "S" n:max=>parliament n (q n) v
local notation "η"=>P.rewardK f r
private lemma canvas_holiday {ι:Type*}[DecidableEq ι](Q:Finset ι) (x₀:ι→ℂ) (G:ι→P.Apron) (D:P.Apron) (i:ℕ)(p:D.s=i)(t:∀ j∈Q,(G j).s ≤ i) (z:∀ j'∈Q,(G j').realWidth P j ≤ D.realWidth P j) (hx:D.F=∑ j'∈Q,x₀ j' • (G j').full P i) (r:ℝ)(B:2* D.realWidth P j ≤ r): -- x shadow!
    P.pillar j ξ D (-r) r 0= ∑ j'∈Q,x₀ j' • M! r (G j') :=by
 let w:=D.u j; let W:=w+w; have hw:0<W:= add_pos (D.pos j) (D.pos j)
 have he:↑(whenly (timeMesh P.par) i W)=D.realWidth P j+D.realWidth P j:=by
    rw [when_add,NNReal.coe_add]; have hx:(whenly (timeMesh P.par) i w:ℝ)=D.realWidth P j:=by unfold Apron.realWidth; rw [p]; exact (natural_time ..).symm
    rw [hx]
 have ht: D.realWidth P j < (whenly (timeMesh P.par) i W:ℝ):=he ▸ lt_add_of_pos_right _ (D.real_width_pos P j)
 have h' : D.full P i= D.F:=by rw [←p]; unfold Apron.full; rw [Nat.sub_self]; rfl
 exact P.petitions_r j ξ D i W Q x₀ G hw t p.le ht (fun i k=> (z i k).trans_lt ht) (h'.trans hx) r (he.trans_le (by linarith only [B]))
lemma crewCanvas {U:ℝ→(V).Op} (t:ℝ)(H:Mosaic P j ξ (fun i=> F! i) (fun i=>(a i:ℂ)) U) (p:0 < t) : Brakes (fun i=> M! t (D! i)) ((η:ℂ) • U t):=by
 let A':=U; let p':=(H.paid t p).pump (P.rewardK f r:ℂ); let q0 := crewWind q p'; let z(k j:ℕ):= (q k).w j*(η*a (k+j));
 refine q0.sameC ?_ rfl
 have he: Tendsto (fun i:ℕ=> (2:ℝ)*P.roomy*P.macroStep (v i)) atTop (𝓝 0):=by simpa only [mul_zero, comp_apply] using (P.macroStep_zero.comp u.tendsto_atTop).const_mul ((2:ℝ)*P.roomy)
 filter_upwards [he.eventually (ge_mem_nhds p)] with i e; symm
 let q':= Y! i; let D:= D! i; let Y(j:ℕ):= F! (i+j); let L:= q i; let n:= S i
 have hp:D.s=n:= q'.pivot_s P l -- cast!
 have hg(k:ℕ)(b:k∈L.voters): (Y k).s ≤ n:=by unfold Y; rw [Apron.pivot_s]; exact le_trans (le_sup (f:=fun k=>v (i+k)) b) (le_max_right ..)
 have hD:D.realWidth P j=(P.roomy:ℝ)*P.macroStep (v i):=(q'.pivot_w j P l).trans (P.pleading_w ..)
 have hx(k:ℕ)(b:k∈ L.voters): (Y k).realWidth P j ≤ D.realWidth P j:=by
    have hn:= u.monotone (Nat.le_add_right i k); unfold Y; rw [Apron.pivot_w,P.play_width,hD]; apply mul_le_mul_of_nonneg_left _ (by positivity); rw  [←P.daysF (v (i+k)) (v i) hn] -- choose?
    exact le_mul_of_one_le_left (P.macroStep_pos _|>.le) (one_le_pow₀ (by exact_mod_cast P.par.R.L.property))
 have H' : D.F=∑ j∈ L.voters,(z i j:ℂ) • (Y j).full P n:= P.reflectorSum ..
 have hu:2*D.realWidth P j ≤ t:=by rw [hD, ←mul_assoc]; exact e
 refine (canvas_holiday P x j L.voters (fun j=> (z i j:ℂ)) Y D n hp hg hx H' t hu).trans ?_; refine sum_congr rfl fun i h=> ?_ -- name shadow
 unfold z; push_cast; rw [mul_smul,mul_smul] -- tune
end finance
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
