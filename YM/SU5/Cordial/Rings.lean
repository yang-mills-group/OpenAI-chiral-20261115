import YM.SU5.Cordial.LatticeFieldEstimates
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 280000
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
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
variable (P:Spine){q:ℕ}(x:P.Spectrum0 3)(Z:Lead.Clan)(a:Axis)(i:ℤ)(s:ℕ)(c r:ℕ→ℕ)
local notation "B" => P.par.block
local notation "M"=> timeMesh P.par
local notation "Γ"=> marks M
local notation "N₀"=> notch M
local notation "σ" n:max=> P.singleState a (c n) (P.otherSpectrum 3 a x)
local notation "ε" => YM.basis (3:Axis)
local notation "ℓ" => P.calibration.ℓ
def dew (k:ℕ) : ℝ := (k:ℝ) / precisionAt P.par s
lemma dew_pos {k:ℕ}(h:0<k):0<dew P s k:= by unfold dew; positivity
lemma scale_here (k:ℕ) : inchR P.par s k=2* dew P s k:=by unfold inchR dew; ring
lemma proper_dew (G:Launch P c r): Tendsto (fun i=> P.dew (c i) (r i)) atTop (𝓝 0):=by
 have h:= (shrank G).div_const (2:ℝ); rw [zero_div] at h; exact h.congr fun i=> by rw [scale_here]; ring
lemma mintS (k:ℕ)(h:0<k): ((N₀ s i):ℝ) = (P.dew s k)*((P.crewB i:ℝ)/(k:ℝ)):= by
 change (i:ℝ) * ((↑(8*((B).val:ℝ≥0) / ((P.par.R.L.val:ℝ≥0)^s : ℝ≥0))):ℝ) = _; unfold dew crewB; simp only [NNReal.coe_div,NNReal.coe_mul,NNReal.coe_pow, NNReal.coe_natCast,NNReal.coe_ofNat]; unfold Heat.gaugeShift precisionAt; have he:0<(k:ℝ):=by exact_mod_cast h
 push_cast; field_simp; ring
variable (F:∀ i,Lead (r i))(T U: Gaia) (u:marchesR r F T U)(b:Bool)(n:Fin 2)(h:remainsR r F b n)
variable (A:ℕ→ℤ) (z:ℝ)
def bargain: Prop:=Tendsto (fun i=> (P.crewB (A i):ℝ)/(r i:ℝ)) atTop (𝓝 z)
include u in
lemma marching (q: bargain P r A z) : marchesR r (fun i=>P.migrate a (F i) (A i)) (T+ z • basis a) (U+ z • basis a):=by
 let x(k:ℕ):ℝ:=(P.crewB (A k):ℝ)/(r k:ℝ)
 have he(k:ℕ)(v:Cover) :riseX (r k) (v+P.crewB (A k) • step a)= riseX (r k) v + x k • basis a:=by
   ext i; by_cases t:a=i ; · subst i; simp [riseX,moor,x,add_div]
   simp [riseX,moor,Ne.symm t] -- tune hsymm
 exact ⟨(u.1.add (q.smul_const (basis a))).congr fun i=>by exact (show riseX (r i) (roam (F i) a (P.crewB (A i))).birth= _ from (by rw [Designs.proceeds, he])).symm,(u.2.add (q.smul_const (basis a))).congr fun i=>by exact (show riseX (r i) (roam (F i) a (P.crewB (A i))).death= _ from (by rw [Designs.track_cost, he])).symm⟩
include h in
lemma passRemain : remainsR r (fun i=>P.migrate a (F i) (A i)) b n:=by
 intro j; obtain ⟨v,g⟩:=Designs.costSpin (F j) a (P.crewB (A j)); exact ⟨g.trans (h j).1,v.trans (h j).2⟩
def inversion := Ortho.motion (Signed.reflect a) -- rs angle
lemma invert_self (x:Gaia): inversion a x a= -x a:= by simp [inversion] -- tune
include u in
lemma revolve (S:StrictMono r) : marchesR r (fun i=>(F i).mirror a 0) (inversion a U) (inversion a T):=by
 let f:= inversion a; let l(i:ℕ):ℝ:=(r i:ℝ)⁻¹; have hv:Tendsto (fun i=>l i • basis a) atTop (𝓝 0):= by simpa using ((tendsto_inv_atTop_zero (𝕜:=ℝ)|>.comp (tendsto_natCast_atTop_atTop.comp S.tendsto_atTop)).smul_const (basis a))
 have he(i:ℕ)(t:Cover): riseX (r i) ((plane a 0).flee t)=f (riseX (r i) t)- l i • basis a:= by
    ext j; simp only [PiLp.sub_apply, PiLp.smul_apply, f,inversion,Ortho.motion_at, Signed.mirrored]; by_cases h:a=j ; · subst j; simp [riseX,moor,sub_div,one_div,l, flee_pos,neg_div]
    simp [riseX,moor,h, Ne.symm h, flee_pos]
 refine ⟨?_,?_⟩
 · simp_rw [Lead.mirror,he]; simpa only [sub_zero, Function.comp_apply, f] using ((f.continuous.continuousAt.tendsto.comp u.2).sub hv)
 simp_rw [Lead.mirror,he]; simpa only [sub_zero, Function.comp_apply, f] using ((f.continuous.continuousAt.tendsto.comp u.1).sub hv)
include h in
lemma turnsZ : remainsR r (fun i=>(F i).mirror a 0) (axis_val a b) (Lead.shuffle a n) := fun v=> ⟨congrArg (axis_val a) (h v).1, congrArg (Lead.shuffle a) (h v).2⟩
-- precise sequences of marks for real offset
def roundingR (k:ℕ) (x:ℝ):ℤ := ⌊(k:ℝ)*x/(8*(B).val)⌋ -- nearest below
lemma intendR (h:StrictMono r) : bargain P r (fun i=>P.roundingR (r i) z) z:=by
 let u:ℝ:=8*(B).val; have hu:0<u:=by unfold u; positivity
 let F(i):ℝ:=r i; have hf:Tendsto F atTop atTop:= tendsto_natCast_atTop_atTop.comp h.tendsto_atTop
 let p(i:ℕ):= P.roundingR (r i) z; have he(i:ℕ):((P.crewB (p i)):ℝ)= (⌊F i*z/u⌋:ℤ)*u:=by unfold u p roundingR crewB Heat.gaugeShift F; push_cast; ring
 have hv:Tendsto (fun i=>z-u/F i) atTop (𝓝 z):=by simpa using (tendsto_const_nhds (x:=z)).sub (tendsto_const_nhds.div_atTop hf (a:=u))
 refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hv (tendsto_const_nhds (x:=z)) ?_ ?_ <;> filter_upwards [hf.eventually_gt_atTop 0] with i hi
 · change z-u/F i≤(P.crewB (p i):ℝ)/ F i; rw [he]; rw [le_div_iff₀ hi,_root_.sub_mul,div_mul_cancel₀ _ hi.ne']; have ha:= Int.sub_one_lt_floor (F i*z/u); rw [show F i*z/u-1=(z* F i-u)/u from ?_, div_lt_iff₀ hu] at ha; exact ha.le
   field_simp
 change (P.crewB (p i):ℝ)/ F i ≤ z; rw [he,div_le_iff₀ hi,mul_comm z,←le_div_iff₀ hu]; exact Int.floor_le _
lemma minusPath (q:P.bargain r A z):P.bargain r (-A) (-z):= q.neg.congr fun i=> by simp [crewB,Heat.gaugeShift,neg_div]
lemma addPath (C:ℕ→ℤ)(z':ℝ)(p:P.bargain r A z)(q:P.bargain r C z'):P.bargain r (A+C) (z+z') := (p.add q).congr fun i=>by simp [crewB,Heat.gaugeShift,add_div,mul_add]
lemma countPath (q:P.bargain r A z)(u:0<z)(h:StrictMono r) : Tendsto (fun i=> P.crewB (A i)) atTop atTop := by
 let F (i:ℕ):ℝ:=r i; let g(i:ℕ):= (P.crewB (A i):ℤ); let x(i:ℕ):ℝ:=g i
 have hf:Tendsto F atTop atTop:=tendsto_natCast_atTop_atTop.comp h.tendsto_atTop
 have hF:= hf.eventually_gt_atTop 0; have hX:Tendsto x atTop atTop:= (q.pos_mul_atTop u hf).congr' (hF.mono fun i hi=> div_mul_cancel₀ _ hi.ne') -- name
 refine tendsto_atTop.mpr fun j=> (hX.eventually_ge_atTop (j:ℝ)).mono fun i h=>?_ ; change (↑j:ℝ)≤ ↑(g i) at h; exact_mod_cast h
lemma priceV(q:P.bargain r A z)(v:∀ i,0<r i): Tendsto (fun i=> (↑(N₀ (c i) (A i)):ℝ)/P.dew (c i) (r i)) atTop (𝓝 z):= q.congr fun i=>by rw [mintS _ _ _ _ (v i),mul_comm (P.dew ..), mul_div_cancel_right₀ _ (P.dew_pos _ (v i)).ne'] -- check
-- flash mark & support pay
open Sods
def kernel0 (n:ℕ) : Cover:= (ℓ+n) • step 3
def flash (n:ℕ): Lead n := ⟨P.kernel0 n,P.kernel0 n+n • step 3,0,false,List.replicate (2*n) (posDir 3),by rw [Ballad.sail]; unfold direction; simp,by rw [Sods.swifts]; unfold nodeC; rw [smul_add,mul_smul (2:ℕ)]; abel,List.length_replicate⟩
lemma flash_here (n:ℕ): Tower.region 3 0 ℓ (P.flash n).patio:=by
 intro x e; obtain ⟨t,h,rfl⟩:= Cube.range_leg _ (posDir 3) (2*n) x (List.mem_toFinset.mp e); simp [flash,kernel0,nodeC]; omega -- tune
lemma flash_fixed (n:ℕ) (i:Cover)(x:i∈(P.flash n).patio)(h:a≠3): i a=1:=by
 obtain ⟨t,v,rfl⟩:= Cube.range_leg _ (posDir 3) (2*n) i (List.mem_toFinset.mp x); change (nodeC (P.kernel0 n)+t • step (S:=ℤ) 3) a=1; simp [kernel0,nodeC,h] -- tune
lemma heights_here (h:StrictMono r)(v:∀ i,0<r i): marchesR r (fun i=>P.flash (r i)) ε ((2:ℝ) • ε):=by
 let L(i:ℕ):ℝ:= (ℓ:ℝ)/(r i); have hl:Tendsto L atTop (𝓝 0):= tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp h.tendsto_atTop)
 have he(i:ℕ):riseX (r i) (P.kernel0 (r i))=L i • ε+ ε:= by
    have ht:0<(r i:ℝ):=by exact_mod_cast v i
    ext j; by_cases p:j=3
    · subst j; simp [riseX,moor,kernel0,L,add_div]; exact (v i).ne' -- tune
    simp [kernel0,riseX,moor,p]
 have hd(i:ℕ) : riseX (r i) (P.flash (r i)).death= L i • ε+(2:ℝ) • ε:=by
    have ht:0<(r i:ℝ):=by exact_mod_cast v i
    ext j; by_cases p:j=3
    · subst j; simp [riseX,moor,kernel0,L,flash,add_div]; rw [div_self ht.ne']; ring
    simp [kernel0,flash,riseX,moor,p]
 constructor
 · simpa only [show ∀ i:ℕ, riseX (r i) (P.flash (r i)).birth= L i • ε+ ε from he, add_zero,zero_smul, zero_add] using (show Tendsto (fun i=> L i • ε+ ε) atTop (𝓝 ((0:ℝ) • ε+ ε)) from (hl.smul_const ε).add_const _)
 · simpa only [hd, add_zero,zero_smul, zero_add] using (show Tendsto (fun i:ℕ=> L i • ε+(2:ℝ) • ε) atTop (𝓝 ((0:ℝ) • ε+(2:ℝ) • ε)) from (hl.smul_const ε).add_const _)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.revolve
#print axioms Spine.countPath
#print axioms Spine.priceV
#print axioms Spine.intendR
#print axioms Spine.flash_fixed
#print axioms Spine.heights_here
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
