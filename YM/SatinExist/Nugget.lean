import YM.SatinExist.CeladonA
import YM.SatinExist.Lack
import YM.SatinExist.Amy
import YM.SatinExist.Patina
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4100
set_option maxHeartbeats 430000
set_option quotPrecheck false
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
-- introduce double tail filter.P
variable (P:Spine)(x:P.Spectrum0 3) (n s m:ℕ)
open Aria Casting Six
local notation "Λ"=> P.par
local notation "K"=> P.calibration
local notation "q@" n:max => P.asked_at n
local notation "ℓ"=> P.calibration.ℓ
open Chalice
local notation "YZ@" E:max i:max=> Wort E i n
noncomputable abbrev onsiteRuby (i: Stone)(a:Cover)(q:ℕ): P.Test:= P.tuneK (audience a i q)
noncomputable abbrev tipOrder (i:Stone)(a:Cover)(q:ℕ): P.Test:= P.centeredSun x s (P.onsiteRuby i a q)
lemma rubrics (p:Cover)(F:Stone) : PureMatter K (P.onsiteRuby F p n):=by intro L x y; change (YZ@ p F) _ x=(YZ@ p F) _ y; rw [Chalice.words, Chalice.words]
lemma rubric_p (p:Cover): EarshotAlpha P x s (Chalice.honey p) (fun i=> P.tipOrder x s i p n):=by
 constructor; intro i
 let v:= audience p i n; let X:= P.onsiteRuby i p n; let U:= P.singleState 3 s x X
 let H:= bay K (Chalice.honey p) false; let G:= enclave K
 refine ⟨H.sub_mem ((Tapestry.locates ..).2 (v.1.narrow _)) (H.smul_mem H.one_mem U),G.sub_mem (P.celebrity v) (G.smul_mem G.one_mem U),P.centeredSun_good .., fun N p' q=>?_⟩
 let h:= P.rubrics n p i N p' q
 change X.val N p'-U • 1=X.val N q-U • 1; rw [show _=X.val N q from h]
variable (c:Bool)
def houseZ (n:ℕ)(c:Bool) (p:ℕ):Cover:= let i:ℤ:= p; let F:Cover:= fun j=> i+(cornerStep n j); if c then F else -F
where cornerStep (n:ℕ)(j:Axis):ℤ:= if j= (3:Axis) then (n:ℤ) else 0
local notation "℄"=> ruler (K).B
local notation "Δ" => (ℓ+(℄).natAbs+1)
abbrev myroof(n:ℕ)(c:Bool):Cover:= houseZ n c (P.calibration.ℓ+(ruler P.calibration.B).natAbs+1)
local notation "t@" x:max=> P.myroof n x
def WallRuby (i:Stone)(n s:ℕ)(c:Bool):P.Test := let y:= P.myroof n c; P.tipOrder x s (if c then stones i else i) y n
lemma rentWall (s n:ℕ)(c:Bool): EarshotAlpha P x s ({nodeC (P.myroof n c)}:Finset Cover) (fun i=> P.WallRuby x i n s c):=⟨fun i=>(P.rubric_p x n s _).sectionP _⟩ -- order
lemma westP : Punctus (P:=P) false Finset.univ (℄) ({nodeC (P.myroof n false)}:Finset Cover):=by
 intro v h i; rw [Finset.mem_singleton.mp h]; simp only [Bool.false_eq_true, ite_false, Finset.mem_univ, ite_true]; unfold myroof nodeC houseZ; simp; rw [abs_of_nonneg (by have ht:= ruler_gene P.calibration.B; omega)]; have ht:=ruler_gene P.calibration.B; unfold houseZ.cornerStep; split_ifs <;> omega
lemma eastP : Punctus (P:=P) true Finset.univ (℄) ({nodeC (P.myroof n true)}: Finset Cover):=by
 intro v h i; rw [Finset.mem_singleton.mp h]; simp only [ite_true, Finset.mem_univ]; unfold myroof nodeC houseZ; simp; rw [abs_of_nonneg (by have ht:= ruler_gene P.calibration.B; omega)]; have ht:=ruler_gene P.calibration.B; unfold houseZ.cornerStep; split_ifs <;> omega
private abbrev winds : Bool→ℝ := fun c=> if c then 1 else -1
lemma roofOne (i:Axis)(p:ℕ): Tendsto (fun n:ℕ=> riseX (n:ℝ) (houseZ n true p) i) atTop (𝓝 ((corner 1) i)):=by
 have h(i:ℕ): riseX (i:ℝ) 0= (0:Gaia):=by ext j; change (↑(((0:Cover) j)):ℝ)/(i:ℝ)=0; simp
 change Tendsto (fun n:ℕ=> (↑(houseZ n true p i):ℝ)/(n:ℝ)) _ _
 by_cases u:i=3
 · subst i; simp only [corner,EuclideanSpace.single_apply,myroof,houseZ,houseZ.cornerStep,ite_true,Int.cast_add,Int.cast_natCast]
   have he:= tendsto_const_nhds.div_atTop (a:=(p:ℝ)) tendsto_natCast_atTop_atTop; refine (show Tendsto (fun n:ℕ=> (p:ℝ)/n+1) atTop (𝓝 1) from (by simpa only [zero_add] using he.add_const 1)).congr' ?_
   filter_upwards [eventually_gt_atTop 0] with n hc; rw [add_div,div_self (by positivity)]
 simp only [corner,EuclideanSpace.single_apply,houseZ, houseZ.cornerStep,u,ite_true,ite_false,add_zero,Int.cast_natCast]; exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
lemma roof_cost : Tendsto (fun n:ℕ=>riseX (n:ℝ) (P.myroof n c)) atTop (𝓝 (Window.corner (winds c))):= by
 let F(n:ℕ) (c:Bool):=riseX (n:ℝ) (P.myroof n c); have hp:Tendsto (fun n=> F n true) atTop (𝓝 (corner 1)):= (PiLp.continuous_toLp 2 _).continuousAt.tendsto.comp (tendsto_pi_nhds.mpr (fun i=> roofOne i _)) -- tune
 cases c; swap; · exact hp
 have ht:corner (winds false)= -(corner 1):=PiLp.single_neg ..
 rw [ht]; refine hp.neg.congr fun i=>?_; ext j; change -(riseX (i:ℝ) (P.myroof i true) j) = (↑((-P.myroof i true:Cover) j):ℝ)/(i:ℝ); change -((↑(P.myroof i true j):ℝ)/(i:ℝ))= _; simp [neg_div]
/- do not require Hadron nontrivial. -/
open Filter CF.Velvet
noncomputable def seatsRuby : Matrix Stone Stone ℂ:= P.ticketGold x s (fun i=> P.WallRuby x i n s false) (fun i=> P.WallRuby x i n s true)
def fundis (i:Stone):ℂ:= numberX i.1.1*(Window.kernel 2 * Window.kernel 2)
variable (B:ℝ) (A:ℝ)(G: Supplier)(R:P.Register)(T:uniform P R G B A)(d:P.NightCop) -- Supplier maybe scope
local notation "Σ"=>P.singleState 3
-- Filter `Filter.bind atTop` mapping n→ latter feed; Tendsto zero; want x choices vary. Use custom filter
include d T
private lemma unique_direction {a b:Bool}(h:corner (winds a)=corner (winds b)): ∀ᶠ i:ℕ in atTop,P.myroof i a=P.myroof i b:=by
 apply Eventually.of_forall; intro i; have h:=congrArg (fun t:Gaia=>t (3:Axis)) h; cases a <;> cases b <;> first | rfl | norm_num [corner,winds] at h
omit d T
-- comp filter with all X earning. uniform momentum over ALL chars. This is NOT estimating anything w.r.t continuity all Pc.
private abbrev Vars := ℕ × ℕ × P.Spectrum0 3
local notation "Y"=> P.Vars
private def mintWay : Filter P.Vars:= Filter.bind atTop (fun p:ℕ=> Filter.bind atTop (fun s:ℕ=> Filter.map (fun x:P.Spectrum0 3=>(p,s,x)) ⊤))
private lemma wayM (x:Y→Prop): (∀ᶠ y in P.mintWay,x y) ↔ ∀ᶠ n:ℕ in atTop,∀ᶠ r:ℕ in atTop, ∀ t:P.Spectrum0 3,x (n,r,t):=by simp_rw [mintWay,eventually_bind,eventually_map, eventually_top]
local notation "ℜ" a:max z:max y:max=> P.onsiteRuby (a) (P.myroof (y) (z)) (y)
local notation "⋄" i:max => P.singleState 3 (i).2.1 (i).2.2
local notation "τ"=> P.mintWay
variable (i j:Stone)
include d T
private lemma costRoster (S:Bool→Stone)(L:List Bool) : Tendsto (fun v:Y=> (⋄ v) ((L.map (fun b=> (ℜ (S b) b v.1))).prod)) τ (𝓝 (depictionC S L (corner ∘ winds))):=by
 let X:= depictionC S L (corner∘winds)
 have he(O: Bool → Cover)(f:ℕ)(L:List Bool): P.tuneK (pressC S O L (R:=f))=(L.map fun b=> P.onsiteRuby (S b) (O b) f).prod:=by
    induction L with
    | nil=> rfl
    | cons i l h=> exact congrArg (P.onsiteRuby (S i) (O i) f * ·) h
 apply Metric.tendsto_nhds.mpr; intro e t; refine (P.wayM _).mpr ?_
 have hx := matterU P R 3 B A G T d S _ L (corner∘winds) e (fun i=>i) tendsto_id (fun b=>P.roof_cost b) (fun _ _ h=> P.unique_direction B A G R T d h) t -- arg order
 simpa only [he] using hx
private lemma cost_one :Tendsto (fun v:Y=> (⋄ v) (ℜ i c v.1)) τ (𝓝 0):=by
 let S:Bool→Stone:=fun _=>i; have ht:=costRoster P B A G R T d S [c]; rw [Chalice.coin] at ht; simpa only [S,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] using ht
private lemma cost_fee_two :Tendsto (fun v:Y=> (⋄ v) ((ℜ i false v.1)*(ℜ (stones j) true v.1))) τ (𝓝 (if j=i then fundis i else 0)):=by
 let S:Bool→Stone:=fun b=> if b then stones j else i
 have ht:=costRoster P B A G R T d S [false,true]; have hp: stones j=stones i ↔ j=i:= ⟨fun h=>(show Involutive stones from stones_inv).injective h,fun h=>congrArg stones h⟩ -- simpler
 rw [vertical S false true (show (0:ℝ)<2 from (by norm_num)) (by norm_num [winds])] at ht
 simpa only [hp,S,ite_true, Bool.false_eq_true,ite_false,List.map_cons,List.map_nil,List.prod_cons,mul_one,List.prod_nil,fundis] using ht
omit d T in
private lemma allegiance {I L: Type}[DecidableEq I][Fintype I] (X:L→Matrix I I ℂ)(D:Matrix I I ℂ)(F:Filter L)(u:∀ i j,Tendsto (fun l=>X l i j) F (𝓝 (D i j)))(H:Prized D):∀ᶠ i in F,Prized (X i):= by
 have t:Continuous (fun x:Matrix I I ℂ=> x.det):=(continuous_id (X:=Matrix I I ℂ)).matrix_det
 have hu:Tendsto X F (𝓝 D):= tendsto_pi_nhds.mpr (fun i=>tendsto_pi_nhds.mpr (u i))
 have h:∀ᶠ i in F,(X i).det≠0 := ((t.continuousAt.tendsto).comp hu).eventually (isOpen_ne.mem_nhds H.1)
 exact h.and (Filter.eventually_all.mpr (fun i=> (u i i).eventually (isOpen_ne.mem_nhds (H.2 i))))
omit d T in
private lemma diagonal_p {I:Type}[DecidableEq I][Fintype I](a:I→ℂ)(u:∀i,a i≠0): Prized (Matrix.diagonal a):= by
 refine ⟨?_,fun i=> by simpa using u i⟩; rw [Matrix.det_diagonal]; exact Finset.prod_ne_zero_iff.mpr fun i _=>u i
lemma roster_bank : ∀ᶠ n:ℕ in atTop,∀ᶠ s:ℕ in atTop, ∀ x:P.Spectrum0 3,Spine.Prized (P.seatsRuby x n s):=by
 let F(v:Y):Matrix Stone Stone ℂ:= P.seatsRuby v.2.2 v.1 v.2.1
 let D:=Matrix.diagonal fundis
 have he(j:Stone):fundis j ≠0:=by
    unfold fundis; apply mul_ne_zero
    · unfold numberX; exact_mod_cast (dimf_pos _).ne'
    exact mul_ne_zero (fun h=> by have ht:=Window.kernel_pos (show (0:ℝ)<2 from (by norm_num)); rw [h] at ht; exact lt_irrefl _ ht) (fun h=> by have ht:=Window.kernel_pos (show (0:ℝ)<2 from (by norm_num)); rw [h] at ht; exact lt_irrefl _ ht)
 have h(i j:Stone):Tendsto (fun v:Y=> F v i j) τ (𝓝 (D i j)):=by
    have he':=(P.cost_fee_two B A G R T d i j).sub ((P.cost_one false B A G R T d i).mul (P.cost_one true B A G R T d (stones j))) -- names
    rw [mul_zero,sub_zero,show _ = D i j from (show (if j=i then fundis i else (0:ℂ)) = D i j from ?_)] at he'
    swap; · split_ifs with h; subst j; exact (Matrix.diagonal_apply_eq ..).symm; exact (Matrix.diagonal_apply_ne _ (Ne.symm h)).symm
    apply he'.congr; intro v; exact (P.cent_sun ..).symm
 exact (P.wayM (fun u=> Prized (F u))).mp (allegiance F D τ h (diagonal_p fundis he))
omit d T
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
