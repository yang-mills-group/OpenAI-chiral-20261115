import YM.SatinExist.SchismX
import YM.SatinExist.Nugget
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4100
set_option maxHeartbeats 430000
set_option quotPrecheck false
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open OS.Semigroup (F)
open OS.Semigroup.Balloon
variable (P:Spine)(n s:ℕ)
open Aria Casting Six Xara
local notation "Λ"=> P.par
local notation "L"=> P.par.R.L.val
local notation "K"=> P.calibration
local notation "ℓ"=> P.calibration.ℓ
local notation "W" n:max c:max=> P.myroof n c
noncomputable abbrev clay (n:ℕ)(c:Bool):Finset Cover:={nodeC (P.myroof n c)}
noncomputable abbrev walls (n:ℕ)(c:Bool):Finset Cover:= wingspan P.par P.width (P.clay n c)
variable (c:Bool)
open Chalice
private abbrev windsX (c:Bool):ℝ:=if c then 1 else -1
private lemma sli (c:Bool): Tendsto (fun n:ℕ=>riseX (n:ℝ) (P.myroof n c)) atTop (𝓝 (Window.corner (windsX c))):= P.roof_cost c
-- cover wings offsets. all heights. finer call at L n.
local notation "d₀"=> L*gross (aliasLaw Λ) (distanceLaw P.width) P.par.R.J
private lemma spreadWall(x:Cover)(u:nodeC x∈ P.walls n c): x-L • P.myroof n c∈ Lattice.box (L+d₀):=by
 obtain ⟨y,h,g⟩:= mem_biUnion.mp u; obtain ⟨w,hv,rfl⟩:=mem_image.mp h; rw [show w= nodeC (P.myroof n c) from mem_singleton.mp hv] at *; obtain ⟨z,q,r⟩:= mem_image.mp g; rw [box_test]; constructor <;> intro i <;> have h:=congrFun r i <;> have he:=(box_test.mp q).1 i <;> have hv:=(box_test.mp q).2 i
 all_goals change z i+(↑L:ℤ)*(2*((W n c) i)+1)=2*(x i)+1 at h -- defeq?
 all_goals rw [mul_add, mul_one, mul_left_comm (L:ℤ) 2] at h; simp only [Pi.sub_apply, Pi.smul_apply', nsmul_eq_mul,Pi.mul_apply,Pi.natCast_apply]; omega
lemma stepCalls (E:Cover): Tendsto (fun n:ℕ=>riseX (↑(L*n:ℕ)) ((L • (W n c))+E)) atTop (𝓝 (Window.corner (windsX c))):=by
 have hp(i:Axis):Tendsto (fun n:ℕ=> riseX (n:ℝ) (W n c) i) atTop (𝓝 (corner (windsX c) i)):= by
    exact Tendsto.comp (PiLp.continuous_apply 2 (fun _ : Axis=>ℝ) i|>.continuousAt) (P.sli c)
 have hl:0<(L:ℝ):=by positivity
 apply (PiLp.continuous_toLp 2 _).continuousAt.tendsto.comp; refine tendsto_pi_nhds.mpr (fun i=> ?_)
 have h':StrictMono (fun n:ℕ=> L*n):= fun _ _ h=> Nat.mul_lt_mul_of_pos_left h (P.par.R.L.property)
 let Kv:= ((E i:ℤ):ℝ); have hz:=tendsto_const_nhds.div_atTop (a:=Kv) (tendsto_natCast_atTop_atTop (R:=ℝ)|>.comp h'.tendsto_atTop)
 refine (show Tendsto (fun n:ℕ=> riseX (n:ℝ) (W n c) i + Kv/(↑(L*n:ℕ))) atTop (𝓝 ((corner (windsX c) i))) from add_zero (corner (windsX c) i) ▸ (hp i).add hz).congr' ?_
 -- tune output
 filter_upwards [eventually_gt_atTop 0] with n p; change (↑((W n c) i):ℝ)/(n:ℝ)+ Kv/↑(L*n:ℕ)= (↑((L:ℤ)*((W n c) i) +E i):ℝ)/(↑(L*n:ℕ)); unfold Kv; push_cast; field_simp
variable (C1 C2:ℝ)(Y: Supplier)(R:P.Register)(T:uniform P R Y C1 C2)(d:P.NightCop)
include T d
private def pe (A B:GemUT)(c:Bool):Stone:=if c then stoneOf B else stoneOf A
private def spreadPrice (A B:GemUT):ℂ:= depictionC (pe A B) [false,true] (corner ∘ windsX)
private lemma shiftFareX (A B:GemUT)(X Z:ℕ→ Cover)(n:ℕ→ℕ)(p:Tendsto n atTop atTop)(v:Tendsto (fun i:ℕ=> riseX (n i:ℝ) (X i)) atTop (𝓝 (Window.corner (-1))))(q:Tendsto (fun i:ℕ=> riseX (n i:ℝ) (Z i)) atTop (𝓝 (Window.corner 1))) (z:ℝ)(vz:0<z):
  ∀ᶠ i:ℕ in atTop, ∀ᶠ s:ℕ in atTop,∀ x:P.Spectrum0 3, ‖ (↑(n i):ℂ)^6 * P.singleState 3 s x (sheen P.calibration (X i) A* sheen _ (Z i) B) - spreadPrice A B‖ < z:=by
 let S:= pe A B; let V:= (corner ∘ windsX)
 let O(i:ℕ)(b:Bool):Cover:= if b then Z i else X i
 have hz(i:ℕ)(x:GemUT)(l:Cover):P.onsiteRuby (stoneOf x) l i= Twah.gold i • sheen P.calibration l x:= by apply Subtype.ext; funext m; exact goldletter .. -- ensure funext m ok
 have hx(i:ℕ): P.tuneK (pressC S (O i) [false,true] (R:=n i))= (n i:ℂ)^6 • (sheen P.calibration (X i) A* sheen _ (Z i) B):=by
    change P.onsiteRuby (stoneOf A) (X i) (n i)*(P.onsiteRuby (stoneOf B) (Z i) (n i)*1)= _; rw [mul_one,hz,hz, smul_mul_assoc,mul_smul_comm,smul_smul,Twah.gold]; apply congrArg (fun k:ℂ=>k • _); ring -- tune
 have h:= matterU P R 3 C1 C2 Y T d S O [false,true] V z n p (by intro i; cases i; exact v; exact q) (fun i j h=> by
    apply Eventually.of_forall; intro n; have h:=congrArg (fun t:Gaia=>t (3:Axis)) h; cases i <;> cases j <;> first | rfl | norm_num [V,Window.corner,windsX] at h) vz
 simpa only [S,V,spreadPrice,hx, map_smul, smul_eq_mul, dist_eq_norm] using h
def quartz : GemUT:= (0,0,0,0)
abbrev μ : ℝ:= ‖spreadPrice quartz quartz‖/2
omit T d in
lemma mu_p : 0< μ:=by
 unfold μ; refine half_pos (norm_pos_iff.mpr ?_); unfold spreadPrice; rw [vertical _ _ _ (show 0 < (2:ℝ) from (by norm_num)) (show (2:ℝ)= _ from (by norm_num [windsX])), if_pos (show pe quartz quartz true = stones (pe quartz quartz false) from rfl)]
 apply mul_ne_zero; unfold numberX; · exact_mod_cast (dimf_pos _).ne'
 apply mul_ne_zero <;> (intro h; have p:=Window.kernel_pos (show (0:ℝ)<2 by norm_num); rw [h] at p; exact lt_irrefl _ p)
lemma heft : ∀ᶠ i:ℕ in atTop,∀ᶠ s:ℕ in atTop,∀ x:P.Spectrum0 3,μ/(i:ℝ)^6 < ‖P.singleState 3 s x (sheen P.calibration (P.myroof i false) quartz * sheen _ (P.myroof i true) quartz)‖:=by
 filter_upwards [P.shiftFareX C1 C2 Y R T d quartz quartz _ _ _ (show Tendsto (fun i:ℕ=>i) atTop atTop from tendsto_id) (P.sli false) (P.sli true) μ mu_p, eventually_gt_atTop 0] with n e h
 filter_upwards [e] with s p x; have hp:=p x; let V:= P.singleState 3 s x (sheen P.calibration (P.myroof n false) quartz *sheen _ (P.myroof n true) quartz);
 let F':= (n:ℂ)^6 * V
 change ‖F'-spreadPrice quartz quartz‖< _ at hp; apply (div_lt_iff₀ (by positivity)).2
 have he : ‖spreadPrice quartz quartz‖ ≤ ‖F'-spreadPrice quartz quartz‖ + ‖F'‖:= by rw [norm_sub_rev]; apply norm_le_norm_sub_add
 have hz: μ< ‖F'‖:=by unfold μ at *; linarith
 exact hz.trans_eq (by unfold F'; rw [norm_mul,norm_pow]; rw [Complex.norm_natCast,mul_comm])
def βX := 1+∑ i: GemUT× GemUT, ‖spreadPrice i.1 i.2‖
omit T d in
lemma billg (A B:GemUT) : 1+‖spreadPrice A B‖≤ βX:= sum_bill spreadPrice A B
where sum_bill (f:GemUT→GemUT→ℂ)(a b): 1+‖f a b‖≤ 1+∑ i:GemUT×GemUT, ‖f i.1 i.2‖:= add_le_add (le_refl _) (Finset.single_le_sum (f:=fun i:GemUT×GemUT=>‖f i.1 i.2‖) (fun _ _=> norm_nonneg _) (mem_univ (a,b)))
private lemma assault (A B:GemUT)(X Z:Cover):
 ∀ᶠ n:ℕ in atTop, ∀ᶠ s:ℕ in atTop,∀ x:P.Spectrum0 3, ‖P.singleState 3 s x (sheen P.calibration (L • W n false+X) A* sheen _ (L • W n true +Z) B)‖ ≤ βX/(↑(L*n:ℕ):ℝ)^6:=by
 have h':StrictMono (fun n:ℕ=> L*n):= fun _ _ h=> Nat.mul_lt_mul_of_pos_left h (P.par.R.L.property)
 filter_upwards [P.shiftFareX C1 C2 Y R T d A B _ _ _ h'.tendsto_atTop (P.stepCalls false X) (P.stepCalls true Z) 1 zero_lt_one,eventually_gt_atTop 0] with i v p
 filter_upwards [v] with s d x; let B':= spreadPrice A B; specialize d x; let F':= P.singleState 3 s x (sheen P.calibration (L • W i false+X) A * sheen _ (L • W i true + Z) B)
 have he:= (norm_le_norm_sub_add ((↑(L*i:ℕ):ℂ)^6*F') B').trans ((add_le_add d.le (le_refl _)).trans (show 1+‖B'‖≤βX from billg A B))
 rw [norm_mul,norm_pow] at he; apply (le_div_iff₀ (by positivity)).2; rw [mul_comm]; simpa only [Complex.norm_natCast] using he
lemma expensive : ∀ᶠ n:ℕ in atTop,∀ᶠ s:ℕ in atTop,∀ z:P.Spectrum0 3,∀ x:Cover,nodeC x∈P.walls n false→∀ y:Cover,nodeC y∈P.walls n true→∀ A B:GemUT, ‖P.singleState 3 s z (sheen P.calibration x A * sheen _ y B)‖ ≤ βX/(↑(L*n:ℕ):ℝ)^6:=by
 let U:=↥(Lattice.box (L+d₀)); let X(A:U):=A.val
 have h:= Filter.eventually_all.mpr (fun A: GemUT=> Filter.eventually_all.mpr (fun B:GemUT=>Filter.eventually_all.mpr (fun a:U=>Filter.eventually_all.mpr (fun b:U=>P.assault C1 C2 Y R T d A B (X a) (X b)))))
 filter_upwards [h] with n h; filter_upwards [Filter.eventually_all.mpr (fun A:GemUT=> Filter.eventually_all.mpr (fun B:GemUT=>Filter.eventually_all.mpr (fun a:U=>Filter.eventually_all.mpr (fun b:U=>h A B a b))))] with s φ z x p y v a b
 let k:U:=⟨_,P.spreadWall n false x p⟩; let t:U:=⟨_,P.spreadWall n true y v⟩; specialize φ a b k t z; rw [show L • W n false+ X k=x from add_sub_cancel _ _,show L • W n true+ X t=y from add_sub_cancel _ _] at φ; exact φ
#print axioms heft -- typo
#print axioms expensive
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
