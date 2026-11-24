import YM.CF.Tarn.Dye
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Tarn
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
open Arena
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
open Cube
variable {r:ℕ}{u v W a b w s':ℝ}{i:Site c}{F:Tab S}{K:Teller G}{P': Tab S}
section path
variable (T:Tube G S)(x u:ℝ)(q:Chi)(d:ℝ)(l:ℕ)
def pines (G' :Gauge)(c:Side)(u:ℝ): Set (Config G' c):=satU G' u '' ball 0 1
lemma pine_p(y:Mast G c)(h:‖y‖<1) : satU G u y∈pines G c u:= ⟨y,mem_ball_zero_iff.mpr h,rfl⟩
def zestQ (F:Tab S)(i: Site c)(V:Config G c):ℝ:= Quill T x q d l (bunk S F V) i - Quill T x q d l (bunk S F 1) i
def neatQ (F:Tab S):FileM c G:=fun i=> salsa (pines G c u) i ((l+68)*radiusB x) (fun y=>(zestQ T x q d l F i y:ℂ))
lemma z_p(P P':Tab S)(h:Kind S P P' (pavilion ((l+68)*radiusB x) i))(V W:Config G c)(hr:Ready T x)(hp:1000 ≤ radiusB x)(hv:drift G i ((l+68)*radiusB x) V W): zestQ T x q d l P i V=zestQ T x q d l P' i W:=by
 have he(V W:Config G c)(hp':drift G i ((l+68)*radiusB x) V W):Quill T x q d l (bunk S P V) i=Quill T x q d l (bunk S P' W) i:= Quill_r i hr hp (Subset.refl _) ⟨fun _ _=>Iff.rfl,h.site,fun i hu=>h.edge i (hu (mem_insert_self ..)),KinT h,fun _ p _=>hp' _ ((theatre ..).mp p),fun _ _=>rfl,fun _ _=>rfl⟩
 exact congrArg₂ (·-·) (he V W hv) (he 1 1 fun _ _=>rfl)
lemma knit(F P': Tab S)(p: Kind S F P' (pavilion ((l+68)*radiusB x) i))(hp:Ready T x)(hx:1000 ≤radiusB x): neatQ T x u q d l F i=neatQ T x u q d l P' i:=by
 funext i; unfold neatQ salsa; split
 next h=> exact congrArg Complex.ofReal (z_p T x q d l F P' p _ _ hp hx (fun _ _=>rfl))
 next h=> rfl
lemma lore (U W:Config G c)(hp:FreeResolvent.Gap (baseX T x (bareStores S) P.1 P.2 U) m)(h:K.Funds S T)(hm:0 < m)(hr:Ready T x)(hx:1000 ≤radiusB x)(g:Site c→SU.group.El)(hv:drift G i ((l+68)*radiusB x) (Lattice.gauge g U) W):zestQ T x q d l P i U=zestQ T x q d l P i W:=by
 have ht:Kind S P P (pavilion ((l+68)*radiusB x) i):= ⟨fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl⟩
 rw [← z_p T x q d l P P ht _ W hr hx hv]; let M:=bunk S P U; let N:=bunk S P (Lattice.gauge g U); have hpQ:= groundX g T x q d l M h hp hm (by omega) i; unfold zestQ; change Quill T x q d l M i-_=Quill T x q d l N i-_; apply congrArg (fun w:ℝ=>w-Quill T x q d l (bunk S P 1) i); rw [←hpQ]; unfold Quill; refine Finset.sum_congr rfl fun j _=>?_; rw [priceBeds,priceBeds]; refine Finset.sum_congr rfl fun u _=>?_; unfold pes; rw [show (shiftZ g M).bush x=(N).bush x from funext fun i=> False.elim ((notChilled S M.park x i.val) i.property)]; rfl -- tune defeq
lemma zStamp (H:∀ V: Mast G c, ‖V‖<1→ FreeResolvent.Gap (baseX T x (bareStores S) P.1 P.2 (satU G u V)) m)(h:K.Funds S T)(hm:0 < m)(hr:Ready T x)(hx:1000 ≤radiusB x):StampP (pines G c u) i ((l+68)*radiusB x) (fun v=> (zestQ T x q d l P i v:ℂ)):=by
 refine glaze_r ?_; rintro _ ⟨v,h',rfl⟩ W hv g p; exact congrArg Complex.ofReal (lore T x q d l _ W (H v (mem_ball_zero_iff.mp h')) h hm hr hx g p)
open Stationary Push.Loops
lemma fruitZ (t':Mast G c)(p:‖t'‖<1)(H:∀ V: Mast G c, ‖V‖<1→ FreeResolvent.Gap (baseX T x (bareStores S) P.1 P.2 (satU G u V)) m)(h:K.Funds S T)(hm:0 < m)(hr:Ready T x)(hx:1000 ≤radiusB x): neatQ T x u q d l P i (satU G u t')= (zestQ T x q d l P i (satU G u t'):ℂ):=land_s (zStamp T x u q d l H h hm hr hx) (pine_p _ _ p) 1 (fun i p=> by rw [fix_s]) -- tune implicit u
lemma fret(i:Site c)(h:0 < u)(hx:s'≤u)(ht:0 ≤ W)(hp:C*tipPay b x≤W)(hc:C ≤ W)(hu: tipPay v x ≤1)(ha: tipPay b x≤1)(hE: a*u ≤ W)(hC:0 ≤ C)(p:Ready T x)(Q:K.Funds S T)(hr:1000 ≤ radiusB x)(hm:0 < m)(D:∀ y:Mast G c,‖y‖<1 →Medal T x C m v a b n l u P.1 P.2 y) : let G':=Gems S.patch.L (radiusB x) n W; CakeF (neatQ T x u q d l P i) i ((l+68)*radiusB x) n s' (composeCost n (G'+G') (1+u⁻¹)):=by
 intro G'; have hv(y)(hy:‖y‖<1):= (D y hy).gap
 refine ⟨SpiceU (zStamp T x u q d l hv Q hm p hr), fun y hi =>?_⟩
 let L:= chair T P.1; let X:= u⁻¹ • L; have hL:‖X y‖<1:=by
    rw [show X y=u⁻¹ • L y from rfl,norm_smul_of_nonneg (inv_nonneg.mpr h.le),inv_mul_lt_iff₀ h,mul_one]; exact (Push.Uniform.tint_inv_le y).trans_lt (hi.trans_le hx)
 have hz:‖X‖ ≤ u⁻¹ :=by unfold X; erw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr h.le)]; apply mul_le_of_le_one_right (inv_nonneg.mpr h.le); exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun i=>by rw [one_mul]; exact Push.Uniform.tint_inv_le i -- tune
 have he := Quill_c (P:=P) (q:=q) (d:=d) i u a v b W (0:Mast G c) (D 0 (by simp)) p hr hc hu ha hE hC; have hZ: satU G u (0:Mast G c)=1:= by simp [satU,facadeX]
 let Y(z:Mast G c):= Quill T x q d l (bunk S P (satU G u z)) i; have ht : ‖Quill T x q d l (bunk S P 1) i‖ ≤ G':= hZ ▸ he.value -- tune
 have hp':Allows n X y (1+u⁻¹):=allows_linear (hz.trans (le_add_of_nonneg_left (by norm_num))) (hL.le.trans (le_add_of_nonneg_right (inv_nonneg.mpr h.le)))
 let C':=Complex.ofRealCLM; have hV:= ((subtract_p (Quill_c (P:=P) (q:=q) (d:=d) i u a v b W (X y) (D _ hL) p hr hc hu ha hE hC) (allows_const (X y) ht)).comp hp'); refine (((hV.linear C' (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun i=>by rw [one_mul]; exact (Complex.norm_real i).le)).mono (one_mul _).le).germ ?_)
 filter_upwards [X.continuous.continuousAt.eventually (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hL))] with v' ht'; change C' _= neatQ T x u q d l P i (represent v'); rw [← chap T P.1 v',← show u • X v'=L v' from smul_inv_smul₀ h.ne' (L v'), ← show satU G u (X v')= _ from rfl, fruitZ T x u q d l (X v') (mem_ball_zero_iff.mp ht') hv Q hm p hr]; rfl -- tune rewrite
end path
end YM.CF.Tarn
